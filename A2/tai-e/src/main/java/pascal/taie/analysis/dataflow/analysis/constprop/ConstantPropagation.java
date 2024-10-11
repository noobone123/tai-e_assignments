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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.HashSet;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        for (Var var : cfg.getMethod().getIR().getParams()) {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        var allVars = new HashSet<>(fact.keySet());
        allVars.addAll(target.keySet());

        for (var var : allVars) {
            var valueFromFact = fact.get(var);
            var valueFromTarget = target.get(var);
            target.update(var, meetValue(valueFromFact, valueFromTarget));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // NAC meet v = NAC
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
            // UNDEF meet v = v
        else if (v1.isUndef() || v2.isUndef()) {
            if (v1.isUndef())
                return v2;
            else
                return v1;
        }
        // v meet v = ?
        else if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2))
                return v1;
            else
                return Value.getNAC();
        }
        else
            return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // if it is a assignment statement (defStmt)
        if (stmt instanceof DefinitionStmt<?,?> defStmt &&
                defStmt.getLValue() instanceof Var lVar) {
            RValue rVal = defStmt.getRValue();

            Value genValue;
            genValue = evaluate(rVal, in);

            if (canHoldInt(lVar)) {
                out.copyFrom(in);
                return out.update(lVar, genValue);
            } else {
                // if LVar can not hold int, need to tag as Undef
                out.copyFrom(in);
                return out.update(lVar, Value.getUndef());
            }
        } else {
            if (in != null)
                return out.copyFrom(in);
        }
        return false;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // x = y
        if (exp instanceof Var tmpExp) {
            // may be question
            if (canHoldInt(tmpExp))
                return in.get(tmpExp);
            // x = 10
        } else if (exp instanceof IntLiteral tmpExp) {
            return Value.makeConstant(tmpExp.getValue());
            // x = y op z
        } else if (exp instanceof BinaryExp) {
            // types of binary expression
            if (exp instanceof ArithmeticExp arithmeticExp) {
                Var op1 = arithmeticExp.getOperand1();
                Var op2 = arithmeticExp.getOperand2();
                Value op1Value = in.get(op1);
                Value op2Value = in.get(op2);

                if (canHoldInt(op1) && canHoldInt(op2) && op1Value.isConstant() && op2Value.isConstant()) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD:
                            return Value.makeConstant(op1Value.getConstant() + op2Value.getConstant());
                        case SUB:
                            return Value.makeConstant(op1Value.getConstant() - op2Value.getConstant());
                        case MUL:
                            return Value.makeConstant(op1Value.getConstant() * op2Value.getConstant());
                        case DIV:
                            if (op2Value.getConstant() != 0) {
                                return Value.makeConstant(op1Value.getConstant() / op2Value.getConstant());
                            } else {
                                return Value.getUndef();
                            }
                        case REM:
                            if (op2Value.getConstant() != 0) {
                                return Value.makeConstant(op1Value.getConstant() % op2Value.getConstant());
                            } else {
                                return Value.getUndef();
                            }
                    }
                } else if ((canHoldInt(op1) && canHoldInt(op2)) && (op1Value.isNAC() || op2Value.isNAC())) {
                    var op = arithmeticExp.getOperator();
                    if (op2Value.isConstant() && (op2Value.getConstant() == 0)) {
                        if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)
                            return Value.getUndef();
                    }
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }
            } else if (exp instanceof ConditionExp conditionExp) {
                Var op1 = conditionExp.getOperand1();
                Var op2 = conditionExp.getOperand2();
                Value op1Value = in.get(op1);
                Value op2Value = in.get(op2);
                if (op1Value.isConstant() && op2Value.isConstant()) {
                    switch (conditionExp.getOperator()) {
                        case EQ:
                            if (op1Value.getConstant() == op2Value.getConstant())
                                return Value.makeConstant(1);
                            else
                                return Value.makeConstant(0);
                        case GE:
                            if (op1Value.getConstant() >= op2Value.getConstant())
                                return Value.makeConstant(1);
                            else
                                return Value.makeConstant(0);
                        case GT:
                            if (op1Value.getConstant() > op2Value.getConstant())
                                return Value.makeConstant(1);
                            else
                                return Value.makeConstant(0);
                        case LE:
                            if (op1Value.getConstant() <= op2Value.getConstant())
                                return Value.makeConstant(1);
                            else
                                return Value.makeConstant(0);
                        case LT:
                            if (op1Value.getConstant() < op2Value.getConstant())
                                return Value.makeConstant(1);
                            else
                                return Value.makeConstant(0);
                        case NE:
                            if (op1Value.getConstant() != op2Value.getConstant())
                                return Value.makeConstant(1);
                            else
                                return Value.makeConstant(0);
                    }
                } else if (op1Value.isNAC() || op2Value.isNAC()) {
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }

            } else if (exp instanceof ShiftExp shiftExp) {
                Var op1 = shiftExp.getOperand1();
                Var op2 = shiftExp.getOperand2();
                Value op1Value = in.get(op1);
                Value op2Value = in.get(op2);
                if (op1Value.isConstant() && op2Value.isConstant()) {
                    return switch (shiftExp.getOperator()) {
                        case SHL -> Value.makeConstant(op1Value.getConstant() << op2Value.getConstant());
                        case SHR -> Value.makeConstant(op1Value.getConstant() >> op2Value.getConstant());
                        case USHR -> Value.makeConstant(op1Value.getConstant() >>> op2Value.getConstant());
                    };
                } else if (op1Value.isNAC() || op2Value.isNAC()) {
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }
            } else if (exp instanceof BitwiseExp bitwiseExp) {
                Var op1 = bitwiseExp.getOperand1();
                Var op2 = bitwiseExp.getOperand2();
                Value op1Value = in.get(op1);
                Value op2Value = in.get(op2);
                if (op1Value.isConstant() && op2Value.isConstant()) {
                    return switch (bitwiseExp.getOperator()) {
                        case AND -> Value.makeConstant(op1Value.getConstant() & op2Value.getConstant());
                        case OR -> Value.makeConstant(op1Value.getConstant() | op2Value.getConstant());
                        case XOR -> Value.makeConstant(op1Value.getConstant() ^ op2Value.getConstant());
                    };
                } else if (op1Value.isNAC() || op2Value.isNAC()) {
                    return Value.getNAC();
                } else {
                    return Value.getUndef();
                }
            }
        }

        return Value.getNAC();
    }
}
