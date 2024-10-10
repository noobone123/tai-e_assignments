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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Signatures;
import pascal.taie.language.classes.Subsignature;
import pascal.taie.language.type.Type;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    /* Each Signature may hit multiple transfers */
    private final Map<Subsignature, Set<TaintTransfer>> sigToTransfers = new HashMap<>();

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);

        for (var transfer : config.getTransfers()) {
            var sig = transfer.method().getSubsignature();
            sigToTransfers.computeIfAbsent(sig, k -> new HashSet<>()).add(transfer);
        }
    }

    public boolean isTaintSource(JMethod method, Type type) {
        var s = new Source(method, type);
        return config.getSources().contains(s);
    }

    public void handleTaintTransfer(JMethod method, Invoke invoke, Context callSiteCtx, CSVar base) {
        var transfers = sigToTransfers.get(method.getSubsignature());
        if (transfers == null) return;
        for (var transfer : transfers) {
            // case: arg-to-result
            if (transfer.from() >= 0 && transfer.to() == TaintTransfer.RESULT) {
                var receiver = invoke.getLValue();
                if (receiver != null) {
                    var csReceiver = csManager.getCSVar(callSiteCtx, receiver);
                    var arg = csManager.getCSVar(callSiteCtx, invoke.getInvokeExp().getArg(transfer.from()));
                    solver.addTFGEdge(arg, csReceiver);
                }
            }
            // case: arg-to-base
            if (transfer.from() >= 0 && transfer.to() == TaintTransfer.BASE) {
                if (base != null) {
                    var arg = csManager.getCSVar(callSiteCtx, invoke.getInvokeExp().getArg(transfer.from()));
                    solver.addTFGEdge(arg, base);
                }
            }
            // case: base-to-result
            if (transfer.from() == TaintTransfer.BASE && transfer.to() == TaintTransfer.RESULT) {
                var receiver = invoke.getLValue();
                if (receiver != null) {
                    var csReceiver = csManager.getCSVar(callSiteCtx, receiver);
                    solver.addTFGEdge(base, csReceiver);
                }
            }
        }
    }

    public boolean isTaintObj(Obj obj) {
        return manager.isTaint(obj);
    }

    public Obj getTaintedObj(Invoke stmt, Type type) {
        return manager.makeTaint(stmt, type);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();

        var csCallGraph = result.getCSCallGraph();
        csCallGraph.edges().forEach(edge -> {
            var csCallSite = edge.getCallSite();
            var csCallee = edge.getCallee();

            var callerCtx = csCallSite.getContext();
            var args = csCallSite.getCallSite().getInvokeExp().getArgs();
            for (int i = 0; i < args.size(); i++) {
                var arg = args.get(i);
                var csArg = csManager.getCSVar(callerCtx, arg);
                var pointsTo = result.getPointsToSet(csArg);
                for (var obj : pointsTo) {
                    if (isTaintObj(obj.getObject())) {
                        var taintSink = new Sink(csCallee.getMethod(), i);
                        if (config.getSinks().contains(taintSink)) {
                            taintFlows.add(new TaintFlow(
                                    manager.getSourceCall(obj.getObject()),
                                    csCallSite.getCallSite(), i
                            ));
                        }
                    }
                }
            }
        });

        return taintFlows;
    }
}
