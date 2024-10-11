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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        /* h1k0's code */
        deadCode.addAll(unreachableAnalyze(cfg, constants));
        deadCode.addAll(deadAssignAnalyze(cfg, liveVars));

        deadCode.remove(cfg.getExit());
        deadCode.remove(cfg.getEntry());
        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    private static Set<Stmt> deadAssignAnalyze(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set <Stmt> deadCodeStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set <Stmt> visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        doDeadAssignAnalyze(cfg, visitedStmt, deadCodeStmt, cfg.getEntry(), liveVars);
        return deadCodeStmt;
    }

    private static void doDeadAssignAnalyze(CFG<Stmt> cfg, Set<Stmt> visitedStmt, Set<Stmt> deadCode,
                                            Stmt curNode, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        if (visitedStmt.contains(curNode))
            return;
        else
            visitedStmt.add(curNode);

        if (curNode instanceof AssignStmt assignStmt && hasNoSideEffect(assignStmt.getRValue())) {
            if (assignStmt.getLValue() instanceof Var lVar && !liveVars.getOutFact(assignStmt).contains(lVar)) {
                deadCode.add(curNode);
            }
        }

        for (Stmt succ: cfg.getSuccsOf(curNode))
            doDeadAssignAnalyze(cfg, visitedStmt, deadCode, succ, liveVars);
    }

    private static Set<Stmt> unreachableAnalyze(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set <Stmt> allStmt = cfg.getNodes();
        Set <Stmt> visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set <Stmt> deadCodeStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        controlFlowUnreachableAnalyze(cfg, visitedStmt, cfg.getEntry());
        updateDeadCode(allStmt, visitedStmt, deadCodeStmt);
        visitedStmt.clear();

        ifBranchUnreachableAnalyze(cfg, visitedStmt, cfg.getEntry(), constants);
        updateDeadCode(allStmt, visitedStmt, deadCodeStmt);
        visitedStmt.clear();

        SwitchUnreachableAnalyze(cfg, visitedStmt, cfg.getEntry(), constants);
        updateDeadCode(allStmt, visitedStmt, deadCodeStmt);
        visitedStmt.clear();

        return deadCodeStmt;
    }

    private static void controlFlowUnreachableAnalyze(CFG<Stmt> cfg, Set<Stmt> visitedStmt, Stmt curNode) {
        if (visitedStmt.contains(curNode))
            return;
        else
            visitedStmt.add(curNode);

        for (Stmt succ: cfg.getSuccsOf(curNode)) {
            controlFlowUnreachableAnalyze(cfg, visitedStmt, succ);
        }
    }

    private static void ifBranchUnreachableAnalyze(CFG <Stmt> cfg, Set<Stmt> visitedStmt, Stmt curNode,
                                                   DataflowResult<Stmt, CPFact> constants) {
        if (visitedStmt.contains(curNode))
            return;
        else
            visitedStmt.add(curNode);

        if (curNode instanceof If ifStmt &&
                ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt)).isConstant()) {
            int constant = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getInFact(ifStmt)).getConstant();

            // If constant is 1, we can only visit the true branch
            // If constant is 0, we can only visit the false branch
            for (Edge<Stmt> outEdge: cfg.getOutEdgesOf(ifStmt)) {
                if (outEdge.getKind() == Edge.Kind.IF_TRUE) {
                    if (constant != 0) {
                        ifBranchUnreachableAnalyze(cfg, visitedStmt, outEdge.getTarget(), constants);
                        break;
                    }
                }

                else if (outEdge.getKind() == Edge.Kind.IF_FALSE) {
                    if (constant == 0) {
                        ifBranchUnreachableAnalyze(cfg, visitedStmt, outEdge.getTarget(), constants);
                        break;
                    }
                }
            }

        } else {
            for (Stmt succ: cfg.getSuccsOf(curNode)) {
                ifBranchUnreachableAnalyze(cfg, visitedStmt, succ, constants);
            }
        }
    }

    private static void SwitchUnreachableAnalyze(CFG<Stmt> cfg, Set<Stmt> visitedStmt, Stmt curNode,
                                                 DataflowResult<Stmt, CPFact> constants) {
        if (visitedStmt.contains(curNode))
            return;
        else
            visitedStmt.add(curNode);

        if (curNode instanceof SwitchStmt switchStmt &&
                ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt)).isConstant()) {
            int constant = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getInFact(switchStmt)).getConstant();

            Map<Integer, Stmt> caseMap = new HashMap<>();
            for (Edge<Stmt> outEdge: cfg.getOutEdgesOf(switchStmt)) {
                if (outEdge.getKind() == Edge.Kind.SWITCH_CASE) {
                    int caseNum = outEdge.getCaseValue();
                    Stmt caseTarget = outEdge.getTarget();
                    caseMap.put(caseNum, caseTarget);
                }
            }

            if (caseMap.containsKey(constant)) {
                SwitchUnreachableAnalyze(cfg, visitedStmt, caseMap.get(constant), constants);
            } else {
                SwitchUnreachableAnalyze(cfg, visitedStmt, switchStmt.getDefaultTarget(), constants);
            }

        } else {
            for (Stmt succ: cfg.getSuccsOf(curNode))
                SwitchUnreachableAnalyze(cfg, visitedStmt, succ, constants);
        }

    }

    private static void updateDeadCode(Set<Stmt> allStmt, Set<Stmt> visitedStmt, Set<Stmt> deadCodeStmt) {
        for (Stmt stmt: allStmt) {
            if (!visitedStmt.contains(stmt))
                deadCodeStmt.add(stmt);
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
