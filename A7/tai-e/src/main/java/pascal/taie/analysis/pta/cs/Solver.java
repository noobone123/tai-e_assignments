/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (!callGraph.addReachableMethod(csMethod)) return;

        csMethod.getMethod().getIR().getStmts().forEach(
                stmt -> stmt.accept(new StmtProcessor(csMethod))
        );
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        public Void visit(New stmt) {
            var lVar = stmt.getLValue();
            var csVar = csManager.getCSVar(context, lVar);
            var obj = heapModel.getObj(stmt);
            var csObj = csManager.getCSObj(
                    contextSelector.selectHeapContext(csMethod, obj),
                    obj
            );
            var pts = PointsToSetFactory.make(csObj);
            /* For Debugging */
            // System.out.println("New: " + pointer + " -> " + pts);
            workList.addEntry(csVar, pts);
            return null;
        }

        public Void visit(Copy stmt) {
            var cslVar = csManager.getCSVar(context, stmt.getLValue());
            var csrVar = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(csrVar, cslVar);
            return null;
        }

        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var cslVar = csManager.getCSVar(context, stmt.getLValue());
            var loadField = stmt.getFieldRef().resolve();
            addPFGEdge(csManager.getStaticField(loadField), cslVar);
            return null;
        }

        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var csrVar = csManager.getCSVar(context, stmt.getRValue());
            var storeField = stmt.getFieldRef().resolve();
            addPFGEdge(csrVar, csManager.getStaticField(storeField));
            return null;
        }

        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }

            var csCallSite = csManager.getCSCallSite(context, stmt);
            var callee = resolveCallee(null, stmt);
            var calleeCtx = contextSelector.selectContext(csCallSite, callee);
            var csCallee = csManager.getCSMethod(calleeCtx, callee);

            handleCall(stmt, csCallSite, csCallee);
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(
                        target,
                        source.getPointsToSet()
                );
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var deltaSet = propagate(entry.pointer(), entry.pointsToSet());

            if (deltaSet == null) {
                continue;
            }

            if (entry.pointer() instanceof CSVar csVar) {
                var var = csVar.getVar();
                for (var obj : deltaSet) {
                    // process store fields
                    for (var stmt : var.getStoreFields()) {
                        var storeField = stmt.getFieldRef().resolve();
                        var rVar = stmt.getRValue();
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), rVar),
                                csManager.getInstanceField(obj, storeField)
                        );
                    }

                    // process load fields
                    for (var stmt : var.getLoadFields()) {
                        var loadField = stmt.getFieldRef().resolve();
                        var lVar = stmt.getLValue();
                        addPFGEdge(
                                csManager.getInstanceField(obj, loadField),
                                csManager.getCSVar(csVar.getContext(), lVar)
                        );
                    }

                    // process store arrays
                    for (var stmt : var.getStoreArrays()) {
                        var rVar = stmt.getRValue();
                        addPFGEdge(
                                csManager.getCSVar(csVar.getContext(), rVar),
                                csManager.getArrayIndex(obj)
                        );
                    }

                    // process load arrays
                    for (var stmt : var.getLoadArrays()) {
                        var lVar = stmt.getLValue();
                        addPFGEdge(
                                csManager.getArrayIndex(obj),
                                csManager.getCSVar(csVar.getContext(), lVar)
                        );
                    }

                    // process invokes
                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var deltaSet = PointsToSetFactory.make();
        var ptSet = pointer.getPointsToSet();
        for (var obj : pointsToSet) {
            if (ptSet.contains(obj)) {
                continue;
            } else {
                deltaSet.addObject(obj);
            }
        }

        if (!deltaSet.isEmpty()) {
            for (var obj : deltaSet) {
                ptSet.addObject(obj);
            }
            for (var succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, deltaSet);
            }
            return deltaSet;
        } else {
            return null;
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (var stmt : recv.getVar().getInvokes()) {
            var callee = resolveCallee(recvObj, stmt);
            if (callee == null || callee.isStatic()) {
                continue;
            }

            var csCallSite = csManager.getCSCallSite(recv.getContext(), stmt);
            var calleeCtx = contextSelector.selectContext(csCallSite, recvObj, callee);

            var calleeThisVar = callee.getIR().getThis();
            /* initialize this pointer of callee */
            workList.addEntry(
                    csManager.getCSVar(calleeCtx, calleeThisVar),
                    PointsToSetFactory.make(recvObj)
            );

            var csCallee = csManager.getCSMethod(calleeCtx, callee);
            handleCall(stmt, csCallSite, csCallee);
        }
    }

    private void handleCall(Invoke stmt, CSCallSite callSite, CSMethod csMethod) {
        var callEdge = new Edge<>(
                CallGraphs.getCallKind(stmt),
                callSite,
                csMethod
        );

        var invokeExp = stmt.getInvokeExp();
        if (callGraph.addEdge(callEdge)) {
            addReachable(csMethod);
            for (int i = 0; i < invokeExp.getArgCount(); i++) {
                var arg = invokeExp.getArg(i);
                var param = csMethod.getMethod().getIR().getParam(i);
                addPFGEdge(
                        csManager.getCSVar(callSite.getContext(), arg),
                        csManager.getCSVar(csMethod.getContext(), param)
                );
            }

            if (stmt.getResult() == null) {
                return;
            }

            for (var retVar : csMethod.getMethod().getIR().getReturnVars()) {
                addPFGEdge(
                        csManager.getCSVar(csMethod.getContext(), retVar),
                        csManager.getCSVar(callSite.getContext(), stmt.getResult())
                );
            }
        }
    }


    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
