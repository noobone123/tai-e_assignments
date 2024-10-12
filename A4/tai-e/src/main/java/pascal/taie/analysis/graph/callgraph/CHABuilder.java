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

package pascal.taie.analysis.graph.callgraph;

import fj.P;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod method = workList.poll();

            // if callGraph changed because of adding Reachable Methods
            if (callGraph.addReachableMethod(method)) {
                callGraph.callSitesIn(method).forEach(callSite -> {
                    Set<JMethod> invokeTargetMethods = resolve(callSite);
                    for (JMethod tMethod: invokeTargetMethods) {
                        if (tMethod == null) continue;
                        callGraph.addEdge(new Edge<Invoke, JMethod>(
                                CallGraphs.getCallKind(callSite),
                                callSite, tMethod));
                        workList.add(tMethod);
                    }
                });
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> jMethods = new HashSet<>();
        JClass jMethodClass = callSite.getMethodRef().getDeclaringClass();
        Subsignature subsignature = callSite.getMethodRef().getSubsignature();

        CallKind callKind = CallGraphs.getCallKind(callSite);
        if (callKind == CallKind.STATIC) {
            jMethods.add(jMethodClass.getDeclaredMethod(subsignature));
        } else if (callKind == CallKind.SPECIAL) {
            jMethods.add(dispatch(jMethodClass, subsignature));
        } else if (callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            Set <JClass> subClasses = getAllSubJClasses(jMethodClass);
            for (JClass jclass: subClasses) {
                jMethods.add(dispatch(jclass, subsignature));
            }
        }
        return jMethods;
    }

    private Set<JClass> getAllSubJClasses(JClass jClass) {
        Set<JClass> jClasses = new HashSet<JClass>(),
                jNewClasses = new HashSet<JClass>();
        jClasses.addAll(hierarchy.getDirectSubclassesOf(jClass));
        jClasses.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
        jClasses.addAll(hierarchy.getDirectImplementorsOf(jClass));
        for (JClass jClassIter: jClasses) {
            jNewClasses.addAll(getAllSubJClasses(jClassIter));
        }
        jClasses.addAll(jNewClasses);
        jClasses.add(jClass); // Including the class itself
        return jClasses;
    }


    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null)
            return null;

        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract())
            return jMethod;

        // getSuperClass(): if curClass can not find SuperClass, just return null
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
