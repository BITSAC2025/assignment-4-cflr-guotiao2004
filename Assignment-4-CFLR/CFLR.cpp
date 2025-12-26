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
    // -------------------------------------------------------------------------
    // 0. Helper: Safe Edge Addition
    // -------------------------------------------------------------------------
    // Adds an edge to the graph and worklist.
    // Also maintains the necessary inverse edges (Bar edges) for PT and Copy
    // which are critical for the grammar rules (CopyBar * PT, PTBar * Load).
    auto addEdge = [&](unsigned u, unsigned v, EdgeLabel label) {
        if (!graph->hasEdge(u, v, label)) {
            graph->addEdge(u, v, label);
            workList.push(CFLREdge(u, v, label));

            // Maintain symmetry/inverse edges required by the grammar
            if (label == PT) {
                // If u -> v (PT), add v -> u (PTBar)
                if (!graph->hasEdge(v, u, PTBar)) {
                    graph->addEdge(v, u, PTBar);
                    workList.push(CFLREdge(v, u, PTBar));
                }
            } else if (label == Copy) {
                // If u -> v (Copy), add v -> u (CopyBar)
                if (!graph->hasEdge(v, u, CopyBar)) {
                    graph->addEdge(v, u, CopyBar);
                    workList.push(CFLREdge(v, u, CopyBar));
                }
            }
        }
    };

    // -------------------------------------------------------------------------
    // 1. Initialization
    // -------------------------------------------------------------------------
    // Populate the worklist with all initial edges present in the graph.
    // The graph is pre-filled by CFLRGraph constructor (A4Lib.cpp).
    for (const auto &srcMap : graph->getSuccessorMap()) {
        unsigned u = srcMap.first;
        for (const auto &lblMap : srcMap.second) {
            EdgeLabel lbl = lblMap.first;
            for (unsigned v : lblMap.second) {
                workList.push(CFLREdge(u, v, lbl));
            }
        }
    }

    // -------------------------------------------------------------------------
    // 2. Main Worklist Loop
    // -------------------------------------------------------------------------
    while (!workList.empty()) {
        CFLREdge edge = workList.pop();
        unsigned u = edge.src;
        unsigned v = edge.dst;
        EdgeLabel lbl = edge.label;

        // === Unary Rules ===
        // Rule: AddrBar -> PT
        // Initial p -> a (AddrBar) implies p points-to a.
        if (lbl == AddrBar) {
            addEdge(u, v, PT);
        }

        // === Binary Rules (Right Matching: u -> v -> w) ===
        // We look for edges v --nextLbl--> w
        if (graph->getSuccessorMap().count(v)) {
            const auto &succs = graph->getSuccessorMap()[v];

            // Rule: CopyBar * PT -> PT
            // (u --CopyBar--> v) * (v --PT--> w)  ==>  (u --PT--> w)
            if (lbl == CopyBar) {
                if (succs.count(PT)) {
                    for (unsigned w : succs.at(PT)) addEdge(u, w, PT);
                }
            }
            // Rule: Store * PT -> PV
            // (u --Store--> v) * (v --PT--> w)  ==>  (u --PV--> w)
            else if (lbl == Store) {
                if (succs.count(PT)) {
                    for (unsigned w : succs.at(PT)) addEdge(u, w, PV);
                }
            }
            // Rule: PTBar * Load -> VP
            // (u --PTBar--> v) * (v --Load--> w)  ==>  (u --VP--> w)
            else if (lbl == PTBar) {
                if (succs.count(Load)) {
                    for (unsigned w : succs.at(Load)) addEdge(u, w, VP);
                }
            }
            // Rule: PV * VP -> Copy
            // (u --PV--> v) * (v --VP--> w)  ==>  (u --Copy--> w)
            else if (lbl == PV) {
                if (succs.count(VP)) {
                    for (unsigned w : succs.at(VP)) addEdge(u, w, Copy);
                }
            }
        }

        // === Binary Rules (Left Matching: w -> u -> v) ===
        // We look for edges w --prevLbl--> u
        if (graph->getPredecessorMap().count(u)) {
            const auto &preds = graph->getPredecessorMap()[u];

            // Triggered when the current edge (u->v) is the *second* part of a rule
            
            if (lbl == PT) {
                // Rule: CopyBar * PT -> PT
                // (w --CopyBar--> u) * (u --PT--> v)
                if (preds.count(CopyBar)) {
                    for (unsigned w : preds.at(CopyBar)) addEdge(w, v, PT);
                }
                // Rule: Store * PT -> PV
                // (w --Store--> u) * (u --PT--> v)
                if (preds.count(Store)) {
                    for (unsigned w : preds.at(Store)) addEdge(w, v, PV);
                }
            }
            else if (lbl == Load) {
                // Rule: PTBar * Load -> VP
                // (w --PTBar--> u) * (u --Load--> v)
                if (preds.count(PTBar)) {
                    for (unsigned w : preds.at(PTBar)) addEdge(w, v, VP);
                }
            }
            else if (lbl == VP) {
                // Rule: PV * VP -> Copy
                // (w --PV--> u) * (u --VP--> v)
                if (preds.count(PV)) {
                    for (unsigned w : preds.at(PV)) addEdge(w, v, Copy);
                }
            }
        }
    }
}
