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
    // 0. Helper Lambda: Add Edge with Symmetry Maintenance
    // -------------------------------------------------------------------------
    // 当我们添加一条边时，如果它是 PT 或 Copy 类型，我们需要同时维护它的 Bar 边 (反向边)，
    // 以便后续的文法规则（如 CopyBar * PT）能够正确匹配。
    auto addEdge = [&](unsigned u, unsigned v, EdgeLabel label) {
        if (!graph->hasEdge(u, v, label)) {
            graph->addEdge(u, v, label);
            workList.push(CFLREdge(u, v, label));

            // 维护对称性 (Symmetry)
            if (label == PT) {
                if (!graph->hasEdge(v, u, PTBar)) {
                    graph->addEdge(v, u, PTBar);
                    workList.push(CFLREdge(v, u, PTBar));
                }
            } else if (label == Copy) {
                if (!graph->hasEdge(v, u, CopyBar)) {
                    graph->addEdge(v, u, CopyBar);
                    workList.push(CFLREdge(v, u, CopyBar));
                }
            }
        }
    };

    // -------------------------------------------------------------------------
    // 1. Initialization: Populate Worklist
    // -------------------------------------------------------------------------
    // 将图中所有现存的边加入 Worklist
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
    // 2. Main Loop: Worklist Algorithm
    // -------------------------------------------------------------------------
    // Grammar Rules implemented:
    // 1. AddrBar             -> PT
    // 2. CopyBar * PT        -> PT
    // 3. Store   * PT        -> PV  (Propagate Value to Object)
    // 4. PTBar   * Load      -> VP  (Value Property from Object)
    // 5. PV      * VP        -> Copy
    
    while (!workList.empty()) {
        CFLREdge edge = workList.pop();
        unsigned u = edge.src;
        unsigned v = edge.dst;
        EdgeLabel lbl = edge.label;

        // --- Unary Production Rules (单目规则) ---
        // Rule: AddrBar -> PT
        // 含义: 如果 p = &a，则 SVF 生成 a->p (Addr)。A4Lib 生成 p->a (AddrBar)。
        //       我们需要导出 p points-to a (PT)。
        if (lbl == AddrBar) {
            addEdge(u, v, PT);
        }

        // --- Binary Production Rules (双目规则) ---
        
        // Case A: Match Right (u -> v -> w)
        // 查看 v 的出边 (Successors)，寻找匹配: lbl * nextLbl -> newLbl
        if (graph->getSuccessorMap().count(v)) {
            auto &succs = graph->getSuccessorMap()[v];

            // Rule: CopyBar * PT -> PT
            // (u -> CopyBar -> v) AND (v -> PT -> w) ==> (u -> PT -> w)
            // 含义: p = q (q->p Copy, p->q CopyBar), q->o (PT) ==> p->o (PT)
            if (lbl == CopyBar) {
                if (succs.count(PT)) {
                    for (unsigned w : succs[PT]) addEdge(u, w, PT);
                }
            }
            
            // Rule: Store * PT -> PV
            // (u -> Store -> v) AND (v -> PT -> w) ==> (u -> PV -> w)
            // 含义: *p = q (q->p Store), p->o (PT) ==> q stored-into o (PV)
            else if (lbl == Store) {
                if (succs.count(PT)) {
                    for (unsigned w : succs[PT]) addEdge(u, w, PV);
                }
            }

            // Rule: PTBar * Load -> VP
            // (u -> PTBar -> v) AND (v -> Load -> w) ==> (u -> VP -> w)
            // 含义: r = *p (p->r Load), p->o (PT => o->p PTBar) ==> o loaded-to r (VP)
            else if (lbl == PTBar) {
                if (succs.count(Load)) {
                    for (unsigned w : succs[Load]) addEdge(u, w, VP);
                }
            }

            // Rule: PV * VP -> Copy
            // (u -> PV -> v) AND (v -> VP -> w) ==> (u -> Copy -> w)
            // 含义: q stored-into o (PV), o loaded-to r (VP) ==> q flows-to r (Copy)
            else if (lbl == PV) {
                if (succs.count(VP)) {
                    for (unsigned w : succs[VP]) addEdge(u, w, Copy);
                }
            }
        }

        // Case B: Match Left (w -> u -> v)
        // 查看 u 的入边 (Predecessors)，寻找匹配: prevLbl * lbl -> newLbl
        if (graph->getPredecessorMap().count(u)) {
            auto &preds = graph->getPredecessorMap()[u];

            // Rule: CopyBar * PT -> PT
            // (w -> CopyBar -> u) AND (u -> PT -> v) ==> (w -> PT -> v)
            if (lbl == PT) {
                if (preds.count(CopyBar)) {
                    for (unsigned w : preds[CopyBar]) addEdge(w, v, PT);
                }
                // Rule: Store * PT -> PV
                // (w -> Store -> u) AND (u -> PT -> v) ==> (w -> PV -> v)
                if (preds.count(Store)) {
                    for (unsigned w : preds[Store]) addEdge(w, v, PV);
                }
            }

            // Rule: PTBar * Load -> VP
            // (w -> PTBar -> u) AND (u -> Load -> v) ==> (w -> VP -> v)
            else if (lbl == Load) {
                if (preds.count(PTBar)) {
                    for (unsigned w : preds[PTBar]) addEdge(w, v, VP);
                }
            }

            // Rule: PV * VP -> Copy
            // (w -> PV -> u) AND (u -> VP -> v) ==> (w -> Copy -> v)
            else if (lbl == VP) {
                if (preds.count(PV)) {
                    for (unsigned w : preds[PV]) addEdge(w, v, Copy);
                }
            }
        }
    }
}
