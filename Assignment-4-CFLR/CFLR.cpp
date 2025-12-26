/**
 * CFLR.cpp
 * @author kisslune
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // Helper lambda to add edges and maintain symmetry for Points-to and Copy
    auto addEdge = [&](unsigned u, unsigned v, EdgeLabel label) {
        if (!graph->hasEdge(u, v, label)) {
            graph->addEdge(u, v, label);
            workList.push(CFLREdge(u, v, label));

            // Maintain symmetry for core relations to enable grammar matching
            if (label == PT) {
                // If u -> v is PT, then v -> u is PTBar
                if (!graph->hasEdge(v, u, PTBar)) {
                    graph->addEdge(v, u, PTBar);
                    workList.push(CFLREdge(v, u, PTBar));
                }
            }
            else if (label == Copy) {
                // If u -> v is Copy, then v -> u is CopyBar
                if (!graph->hasEdge(v, u, CopyBar)) {
                    graph->addEdge(v, u, CopyBar);
                    workList.push(CFLREdge(v, u, CopyBar));
                }
            }
        }
    };

    // 1. Initialization: Push all existing edges from graph to worklist
    // A4Lib::CFLRGraph constructor populates Addr, Copy, Store, Load, etc.
    for (const auto &srcMap : graph->getSuccessorMap()) {
        unsigned u = srcMap.first;
        for (const auto &lblMap : srcMap.second) {
            EdgeLabel lbl = lblMap.first;
            for (unsigned v : lblMap.second) {
                workList.push(CFLREdge(u, v, lbl));
            }
        }
    }

    // 2. Worklist Algorithm
    while (!workList.empty()) {
        CFLREdge edge = workList.pop();
        unsigned u = edge.src;
        unsigned v = edge.dst;
        EdgeLabel lbl = edge.label;

        // --- Unary Production Rules ---
        
        // Rule: AddrBar -> PT
        // Explain: Addr(a, p) implies p = &a. 
        // A4Lib constructs AddrBar(p, a). Thus p -> a is PT.
        if (lbl == AddrBar) {
            addEdge(u, v, PT);
        }

        // --- Binary Production Rules (Match Right) ---
        // Current edge (u -> v) matches with successors of v (v -> w)
        if (graph->getSuccessorMap().count(v)) {
            auto &succs = graph->getSuccessorMap()[v];

            // Rule: CopyBar * PT -> PT
            // (u -CopyBar-> v) * (v -PT-> w)  ==>  (u -PT-> w)
            // Logic: p = q (p->q CopyBar), q->o (PT) => p->o (PT)
            if (lbl == CopyBar) {
                if (succs.count(PT)) {
                    for (unsigned w : succs[PT]) addEdge(u, w, PT);
                }
            }
            
            // Rule: Store * PT -> PV
            // (u -Store-> v) * (v -PT-> w)  ==>  (u -PV-> w)
            // Logic: *p = q (q->p Store), p->o (PT) => q stored-in o (PV)
            else if (lbl == Store) {
                if (succs.count(PT)) {
                    for (unsigned w : succs[PT]) addEdge(u, w, PV);
                }
            }

            // Rule: PTBar * Load -> VP
            // (u -PTBar-> v) * (v -Load-> w)  ==>  (u -VP-> w)
            // Logic: r = *p (p->r Load), p->o (o->p PTBar) => o flows-to r (VP)
            else if (lbl == PTBar) {
                if (succs.count(Load)) {
                    for (unsigned w : succs[Load]) addEdge(u, w, VP);
                }
            }

            // Rule: PV * VP -> Copy
            // (u -PV-> v) * (v -VP-> w)  ==>  (u -Copy-> w)
            // Logic: q stored-in o (PV), o flows-to r (VP) => q flows-to r (Copy)
            else if (lbl == PV) {
                if (succs.count(VP)) {
                    for (unsigned w : succs[VP]) addEdge(u, w, Copy);
                }
            }
        }

        // --- Binary Production Rules (Match Left) ---
        // Predecessors of u (w -> u) match with current edge (u -> v)
        if (graph->getPredecessorMap().count(u)) {
            auto &preds = graph->getPredecessorMap()[u];

            // Triggered when current edge is the RIGHT side of a rule
            
            if (lbl == PT) {
                // Rule: CopyBar * PT -> PT
                // (w -CopyBar-> u) * (u -PT-> v) => (w -PT-> v)
                if (preds.count(CopyBar)) {
                    for (unsigned w : preds[CopyBar]) addEdge(w, v, PT);
                }
                // Rule: Store * PT -> PV
                // (w -Store-> u) * (u -PT-> v) => (w -PV-> v)
                if (preds.count(Store)) {
                    for (unsigned w : preds[Store]) addEdge(w, v, PV);
                }
            }
            else if (lbl == Load) {
                // Rule: PTBar * Load -> VP
                // (w -PTBar-> u) * (u -Load-> v) => (w -VP-> v)
                if (preds.count(PTBar)) {
                    for (unsigned w : preds[PTBar]) addEdge(w, v, VP);
                }
            }
            else if (lbl == VP) {
                // Rule: PV * VP -> Copy
                // (w -PV-> u) * (u -VP-> v) => (w -Copy-> v)
                if (preds.count(PV)) {
                    for (unsigned w : preds[PV]) addEdge(w, v, Copy);
                }
            }
        }
    }
}
