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
    // TODO: complete this method
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // TODO: complete this function. The implementations of graph and worklist are provided.
    //  You need to:
    //  1. implement the grammar production rules into code;
    //  2. implement the dynamic-programming CFL-reachability algorithm.
    //  You may need to add your new methods to 'CFLRGraph' and 'CFLR'.

    // --- Safety / sanity check ---
    if (!graph) return;

    // Helper to combine two labels into a resulting label according to grammar/production rules.
    // CURRENT STRATEGY:
    //  - if labels are equal, keep that label;
    //  - otherwise, conservatively produce Copy.
    // Replace/add rules here to match the actual CFL grammar for your analysis.
    auto combineLabels = [](EdgeLabel l1, EdgeLabel l2) -> EdgeLabel {
        // Rule 1: Copy transitive closure
        // Copy + Copy -> Copy
        if (l1 == Copy && l2 == Copy)
            return Copy;

        // Rule 2: PointsTo propagation
        // Copy + PointsTo -> PointsTo
        if (l1 == Copy && l2 == PointsTo)
            return PointsTo;

        // Rule 3: Address-of handling (if Addr exists in graph initialization)
        // Copy + Addr -> PointsTo
        if (l1 == Copy && l2 == Addr)
            return PointsTo;

        // Return invalid label if no rule matches
        return (EdgeLabel)-1;
    };

    // Get maps
    auto &succMap = graph->getSuccessorMap();
    auto &predMap = graph->getPredecessorMap();

    // Initialize worklist with all existing edges in the graph
    for (const auto &srcPair : succMap) {
        unsigned src = srcPair.first;
        const auto &labelMap = srcPair.second;
        for (const auto &labelTargets : labelMap) {
            EdgeLabel lbl = labelTargets.first;
            const auto &targets = labelTargets.second;
            for (unsigned dst : targets) {
                CFLREdge e(src, dst, lbl);
                workList.push(e);
            }
        }
    }

    // Main DP-style worklist loop
    while (!workList.empty()) {
        CFLREdge cur = workList.pop();
        unsigned u = cur.src;
        unsigned v = cur.dst;
        EdgeLabel lab = cur.label;

        // 1) Forward composition: (u -lab-> v) + (v -lab2-> w) => (u -combine(lab,lab2)-> w)
        auto succIt = succMap.find(v);
        if (succIt != succMap.end()) {
            const auto &outLabelMap = succIt->second;
            for (const auto &lblTargets : outLabelMap) {
                EdgeLabel lab2 = lblTargets.first;
                const auto &wset = lblTargets.second;
                EdgeLabel newLab = combineLabels(lab, lab2);
                
                // Check if the combination produced a valid label
                if (newLab != (EdgeLabel)-1) {
                    for (unsigned w : wset) {
                        if (!graph->hasEdge(u, w, newLab)) {
                            graph->addEdge(u, w, newLab);
                            workList.push(CFLREdge(u, w, newLab));
                        }
                    }
                }
            }
        }

        // 2) Backward composition: (x -lab1-> u) + (u -lab-> v) => (x -combine(lab1,lab)-> v)
        auto predIt = predMap.find(u);
        if (predIt != predMap.end()) {
            const auto &inLabelMap = predIt->second;
            for (const auto &lblSrcs : inLabelMap) {
                EdgeLabel lab1 = lblSrcs.first;
                const auto &xset = lblSrcs.second;
                EdgeLabel newLab = combineLabels(lab1, lab);
                
                // Check if the combination produced a valid label
                if (newLab != (EdgeLabel)-1) {
                    for (unsigned x : xset) {
                        if (!graph->hasEdge(x, v, newLab)) {
                            graph->addEdge(x, v, newLab);
                            workList.push(CFLREdge(x, v, newLab));
                        }
                    }
                }
            }
        }

        // NOTE:
        // - The skeleton above performs a generic closure that composes adjacent edges.
        // - To implement the precise CFL grammar of your pointer analysis (e.g., productions
        //   like Copy, Store/Load interactions, Addr/AddrBar interactions, PT derivations, etc.),
        //   replace 'combineLabels' with the exact production mapping and add any
        //   additional special-case productions here.
    }
}
