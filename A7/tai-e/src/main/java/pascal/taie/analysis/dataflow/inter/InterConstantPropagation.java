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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    public static PointerAnalysisResult pta;

    private final Map<Var, Set<Var>> aliasMap;
    private final HashMap<JField, Set<LoadField>> staticLoadFields;
    private final HashMap<JField, Set<StoreField>> staticStoreFields;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));

        // maintain alias information for instance/array/static
        aliasMap = new HashMap<>();
        staticLoadFields = new HashMap<>();
        staticStoreFields = new HashMap<>();
    }

    private void initializeAliasMap() {
        // Get alias information here
        Collection<Var> ptaVars =  pta.getVars();
        for (Var ptaVarX: ptaVars) {
            // Add self into aliasMap
            aliasMap.put(ptaVarX, new HashSet<>());
            aliasMap.get(ptaVarX).add(ptaVarX);

            Set<Obj> xPts = pta.getPointsToSet(ptaVarX);
            for (Var ptaVarY: ptaVars) {
                if (ptaVarX.equals(ptaVarY))
                    continue;

                // If XPts and yPts has common object, then add y into aliasMap
                for (Obj yPtsObj: pta.getPointsToSet(ptaVarY)) {
                    if (xPts.contains(yPtsObj)) {
                        aliasMap.get(ptaVarX).add(ptaVarY);
                        break;
                    }
                }
            }
        }
    }

    private void initializeStaticFieldMap() {
        // Map all static fields to their load and store statements
        for (Stmt stmt: icfg) {
            if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                if (!staticStoreFields.containsKey(field))
                    staticStoreFields.put(field, new HashSet<>());
                staticStoreFields.get(field).add(storeField);

            } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField field = loadField.getFieldRef().resolve();
                if (!staticLoadFields.containsKey(field))
                    staticLoadFields.put(field, new HashSet<>());
                staticLoadFields.get(field).add(loadField);
            }
        }
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        initializeAliasMap();
        initializeStaticFieldMap();
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    private Value handleLoadField(LoadField loadField) {
        Value res = Value.getUndef();
        JField field = loadField.getFieldRef().resolve();

        if (loadField.isStatic()) {
            // for staticLoad, we meet all values of the rvalue of the storeField that stores the same field
            for (StoreField storeField : staticStoreFields.getOrDefault(field, new HashSet<>())) {
                CPFact inFact = solver.getResult().getInFact(storeField);
                res = cp.meetValue(res, inFact.get(storeField.getRValue()));
            }
        } else {
            // for instanceLoad, we meet all values of the rvalue of the storeField with alias
            Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
            for (Var baseAlias: aliasMap.getOrDefault(base, new HashSet<>())) {
                for (StoreField storeField : baseAlias.getStoreFields()) {
                    if (storeField.getFieldRef().resolve().equals(field)) {
                        CPFact inFact = solver.getResult().getInFact(storeField);
                        res = cp.meetValue(res, inFact.get(storeField.getRValue()));
                    }
                }
            }
        }

        return res;
    }

    private void handleStoreField(StoreField storeField) {
        JField field = storeField.getFieldRef().resolve();
        if (storeField.isStatic())
            staticLoadFields.getOrDefault(field, new HashSet<>()).forEach(solver::addWorkList);
        else {
            Var base = ((InstanceFieldAccess) storeField.getFieldAccess()).getBase();
            for (Var baseAlias: aliasMap.getOrDefault(base, new HashSet<>())) {
                for (LoadField loadField : baseAlias.getLoadFields()) {
                    if (loadField.getFieldRef().resolve().equals(field))
                        solver.addWorkList(loadField);
                }
            }
        }
    }

    private boolean checkArrayIndex(Value x, Value y) {
        if (x.isUndef() || y.isUndef())
            return false;
        if (x.isConstant() && y.isConstant())
            return x.equals(y);
        return true;
    }

    private Value handleArrayLoad(LoadArray arrayLoad) {
        Value meetValue = Value.getUndef();
        ArrayAccess arrAccess = arrayLoad.getArrayAccess();
        Var arrBase = arrAccess.getBase();

        for (Var arrBaseAlias: aliasMap.getOrDefault(arrBase, new HashSet<>())) {
            for (StoreArray storeArray : arrBaseAlias.getStoreArrays()) {
                CPFact aliasInFact = solver.getResult().getInFact(storeArray);
                CPFact curInFact = solver.getResult().getInFact(arrayLoad);

                Value srcIndexValue = curInFact.get(arrAccess.getIndex());
                Value dstIndexValue = aliasInFact.get(storeArray.getArrayAccess().getIndex());

                if (checkArrayIndex(srcIndexValue, dstIndexValue))
                    meetValue = cp.meetValue(meetValue, aliasInFact.get(storeArray.getRValue()));
            }
        }
        return meetValue;
    }

    private void handleStoreArray(StoreArray storeArray) {
        ArrayAccess arrAccess = storeArray.getArrayAccess();
        for (Var x: aliasMap.getOrDefault(arrAccess.getBase(), new HashSet<>()))
            x.getLoadArrays().forEach(solver::addWorkList);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = !out.equals(in);
        if (changed)
            out.copyFrom(in);
        return changed;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof LoadField loadField) {
            // x = y.f / T.f
            Var lValue = loadField.getLValue();
            if (!ConstantPropagation.canHoldInt(lValue))
                return out.copyFrom(in);

            Value res = handleLoadField(loadField);
            CPFact in_copy = in.copy();
            in_copy.remove(lValue);
            in_copy.update(lValue, res);
            return out.copyFrom(in_copy);

        } else if (stmt instanceof StoreField storeField) {
            // x.f = y / T.f = y
            Var rValue = storeField.getRValue();
            if (ConstantPropagation.canHoldInt(rValue))
                handleStoreField(storeField);

            return out.copyFrom(in);

        } else if (stmt instanceof LoadArray loadArray) {
            // x = a[i]
            Var lValue = loadArray.getLValue();
            if (!ConstantPropagation.canHoldInt(lValue))
                return out.copyFrom(in);

            Value res = handleArrayLoad(loadArray);
            CPFact in_copy = in.copy();
            in_copy.remove(lValue);
            in_copy.update(lValue, res);
            return out.copyFrom(in_copy);

        } else if (stmt instanceof StoreArray storeArray) {
            // a[i] = x
            if (ConstantPropagation.canHoldInt(storeArray.getRValue()))
                handleStoreArray(storeArray);

            return out.copyFrom(in);

        } else {
            return cp.transferNode(stmt, in, out);
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact newOut = out.copy();
        Invoke callSite = (Invoke)edge.getSource();
        Var lVar = callSite.getLValue();
        if (lVar != null)
            newOut.remove(lVar);

        return newOut;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact res = new CPFact();
        List<Var> params = edge.getCallee().getIR().getParams();
        List<Var> args = ((Invoke)edge.getSource()).getInvokeExp().getArgs();

        for (int i = 0; i < params.size(); i++) {
            Var param = params.get(i);
            if (ConstantPropagation.canHoldInt(param))
                res.update(param, callSiteOut.get(args.get(i)));
        }

        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact callerIn = new CPFact();
        Invoke callSite = (Invoke)edge.getCallSite();
        Var lVar = callSite.getLValue();

        // There maybe have serveral return statements in a method
        Value resultValue = Value.getUndef();
        for (Var retVar: edge.getReturnVars())
            resultValue = cp.meetValue(resultValue, returnOut.get(retVar));

        if (lVar != null && ConstantPropagation.canHoldInt(lVar))
            callerIn.update(lVar, resultValue);

        return callerIn;
    }
}
