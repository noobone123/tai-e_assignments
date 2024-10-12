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

package pascal.taie.analysis.pta.ci;

import fj.P;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        /* The purpose of the `addReachable` method is to update the worklist and
            add edges in the PFG that are not related to heap objects,
            which include copy, load/store of static fields, and static method calls, among others. */
        if (!callGraph.addReachableMethod(method)) return;

        // process statements using visitor pattern
        method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        public Void visit(New stmt) {
            var lVar = stmt.getLValue();
            var pointer = pointerFlowGraph.getVarPtr(lVar);
            var obj = heapModel.getObj(stmt);
            var pts = new PointsToSet();
            pts.addObject(obj);
            /* For Debugging */
            // System.out.println("New: " + pointer + " -> " + pts);
            workList.addEntry(pointer, pts);
            return null;
        }

        public Void visit(Copy stmt) {
            var lVar = stmt.getLValue();
            var rVar = stmt.getRValue();
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(rVar),
                    pointerFlowGraph.getVarPtr(lVar)
            );
            return null;
        }

        public Void visit(LoadField stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var lVar = stmt.getLValue();
            var loadField = stmt.getFieldRef().resolve();
            addPFGEdge(
                    pointerFlowGraph.getStaticField(loadField),
                    pointerFlowGraph.getVarPtr(lVar)
            );
            return null;
        }

        public Void visit(StoreField stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var rVar = stmt.getRValue();
            var storeField = stmt.getFieldRef().resolve();
            addPFGEdge(
                    pointerFlowGraph.getVarPtr(rVar),
                    pointerFlowGraph.getStaticField(storeField)
            );
            return null;
        }

        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }

            var callee = resolveCallee(null, stmt);
            handleCall(stmt, callee);
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

            if (entry.pointer() instanceof VarPtr varPtr) {
                var var = varPtr.getVar();
                for (var obj : deltaSet) {
                    // process store fields
                    for (var stmt : var.getStoreFields()) {
                        var storeField = stmt.getFieldRef().resolve();
                        var rVar = stmt.getRValue();
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(rVar),
                                pointerFlowGraph.getInstanceField(obj, storeField)
                        );
                    }

                    // process load fields
                    for (var stmt : var.getLoadFields()) {
                        var loadField = stmt.getFieldRef().resolve();
                        var lVar = stmt.getLValue();
                        addPFGEdge(
                                pointerFlowGraph.getInstanceField(obj, loadField),
                                pointerFlowGraph.getVarPtr(lVar)
                        );
                    }

                    // process store arrays
                    for (var stmt : var.getStoreArrays()) {
                        var rVar = stmt.getRValue();
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(rVar),
                                pointerFlowGraph.getArrayIndex(obj)
                        );
                    }

                    // process load arrays
                    for (var stmt : var.getLoadArrays()) {
                        var lVar = stmt.getLValue();
                        addPFGEdge(
                                pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(lVar)
                        );
                    }

                    // process invokes
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var deltaSet = new PointsToSet();
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (var stmt : var.getInvokes()) {
            var callee = resolveCallee(recv, stmt);
            if (callee == null || callee.isStatic()) {
                continue;
            }

            var calleeThisVar = callee.getIR().getThis();
            /* initialize this pointer of callee */
            workList.addEntry(
                    pointerFlowGraph.getVarPtr(calleeThisVar),
                    new PointsToSet(recv)
            );

            handleCall(stmt, callee);
        }
    }


    private void handleCall(Invoke stmt, JMethod callee) {
        var callEdge = new Edge<>(
                CallGraphs.getCallKind(stmt),
                stmt,
                callee
        );

        var invokeExp = stmt.getInvokeExp();
        if (callGraph.addEdge(callEdge)) {
            addReachable(callee);
            for (int i = 0; i < invokeExp.getArgCount(); i++) {
                var arg = invokeExp.getArg(i);
                var param = callee.getIR().getParam(i);
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(arg),
                        pointerFlowGraph.getVarPtr(param)
                );
            }

            if (stmt.getResult() == null) {
                return;
            }

            for (var retVar : callee.getIR().getReturnVars()) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(retVar),
                        pointerFlowGraph.getVarPtr(stmt.getResult())
                );
            }
        }
    }


    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
