/*
 * Copyright (c) 2016, 2017, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */
package com.oracle.graal.pointsto;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.graalvm.compiler.options.OptionValues;

import com.oracle.graal.pointsto.constraints.UnsupportedFeatureException;
import com.oracle.graal.pointsto.flow.AbstractSpecialInvokeTypeFlow;
import com.oracle.graal.pointsto.flow.AbstractVirtualInvokeTypeFlow;
import com.oracle.graal.pointsto.flow.ActualReturnTypeFlow;
import com.oracle.graal.pointsto.flow.CloneTypeFlow;
import com.oracle.graal.pointsto.flow.ContextInsensitiveFieldTypeFlow;
import com.oracle.graal.pointsto.flow.MethodFlowsGraph;
import com.oracle.graal.pointsto.flow.MethodTypeFlow;
import com.oracle.graal.pointsto.flow.TypeFlow;
import com.oracle.graal.pointsto.flow.context.AnalysisContext;
import com.oracle.graal.pointsto.flow.context.BytecodeLocation;
import com.oracle.graal.pointsto.flow.context.free.DefaultAnalysisContextPolicy;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisField;
import com.oracle.graal.pointsto.meta.AnalysisMethod;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.meta.PointsToAnalysisMethod;
import com.oracle.graal.pointsto.typestate.MultiTypeState;
import com.oracle.graal.pointsto.typestate.PointsToStats;
import com.oracle.graal.pointsto.typestate.SingleTypeState;
import com.oracle.graal.pointsto.typestate.TypeState;
import com.oracle.graal.pointsto.typestate.TypeStateUtils;
import com.oracle.graal.pointsto.typestore.ArrayElementsTypeStore;
import com.oracle.graal.pointsto.typestore.FieldTypeStore;
import com.oracle.graal.pointsto.typestore.UnifiedArrayElementsTypeStore;
import com.oracle.graal.pointsto.typestore.UnifiedFieldTypeStore;
import com.oracle.graal.pointsto.util.AnalysisError;

import jdk.vm.ci.code.BytecodePosition;
import jdk.vm.ci.meta.JavaConstant;

public class DefaultAnalysisPolicy extends AnalysisPolicy {

    private DefaultAnalysisContextPolicy contextPolicy;

    public DefaultAnalysisPolicy(OptionValues options) {
        super(options);
        this.contextPolicy = new DefaultAnalysisContextPolicy();
    }

    @Override
    public DefaultAnalysisContextPolicy contextPolicy() {
        return contextPolicy;
    }

    @Override
    public boolean needsConstantCache() {
        return false;
    }

    @Override
    public boolean isSummaryObject(AnalysisObject object) {
        /* Context insensitive objects summarize context sensitive objects of the same type. */
        return object.isContextInsensitiveObject();
    }

    @Override
    public boolean isMergingEnabled() {
        // by default no merging is necessary
        return false;
    }

    @Override
    public void noteMerge(PointsToAnalysis bb, TypeState t) {
        // nothing to do
    }

    @Override
    public void noteMerge(PointsToAnalysis bb, AnalysisObject... a) {
        // nothing to do
    }

    @Override
    public void noteMerge(PointsToAnalysis bb, AnalysisObject a) {
        // nothing to do
    }

    @Override
    public boolean isContextSensitiveAllocation(PointsToAnalysis bb, AnalysisType type, AnalysisContext allocationContext) {
        return false;
    }

    @Override
    public AnalysisObject createHeapObject(PointsToAnalysis bb, AnalysisType type, BytecodeLocation allocationSite, AnalysisContext allocationContext) {
        return type.getContextInsensitiveAnalysisObject();
    }

    @Override
    public AnalysisObject createConstantObject(PointsToAnalysis bb, JavaConstant constant, AnalysisType exactType) {
        return exactType.getContextInsensitiveAnalysisObject();
    }

    @Override
    public TypeState dynamicNewInstanceState(PointsToAnalysis bb, TypeState currentState, TypeState newState, BytecodeLocation allocationSite, AnalysisContext allocationContext) {
        /* Just return the new type state as there is no allocation context. */
        return newState.forNonNull(bb);
    }

    @Override
    public TypeState cloneState(PointsToAnalysis bb, TypeState currentState, TypeState inputState, BytecodeLocation cloneSite, AnalysisContext allocationContext) {
        return inputState.forNonNull(bb);
    }

    @Override
    public void linkClonedObjects(PointsToAnalysis bb, TypeFlow<?> inputFlow, CloneTypeFlow cloneFlow, BytecodePosition source) {
        /*
         * Nothing to do for the context insensitive analysis. The source and clone flows are
         * identical, thus their elements are modeled by the same array or field flows.
         */
    }

    @Override
    public BytecodeLocation createAllocationSite(PointsToAnalysis bb, int bci, AnalysisMethod method) {
        return BytecodeLocation.create(bci, method);
    }

    @Override
    public FieldTypeStore createFieldTypeStore(AnalysisObject object, AnalysisField field, AnalysisUniverse universe) {
        return new UnifiedFieldTypeStore(field, object, new ContextInsensitiveFieldTypeFlow(field, field.getType(), object));
    }

    @Override
    public ArrayElementsTypeStore createArrayElementsTypeStore(AnalysisObject object, AnalysisUniverse universe) {
        if (object.type().isArray()) {
            if (aliasArrayTypeFlows) {
                /* Alias all array type flows using the elements type flow model of Object type. */
                if (object.type().getComponentType().isJavaLangObject()) {
                    return new UnifiedArrayElementsTypeStore(object);
                }
                return universe.objectType().getArrayClass().getContextInsensitiveAnalysisObject().getArrayElementsTypeStore();
            }
            return new UnifiedArrayElementsTypeStore(object);
        } else {
            return null;
        }
    }

    @Override
    public AbstractVirtualInvokeTypeFlow createVirtualInvokeTypeFlow(BytecodePosition invokeLocation, AnalysisType receiverType, PointsToAnalysisMethod targetMethod,
                    TypeFlow<?>[] actualParameters, ActualReturnTypeFlow actualReturn, BytecodeLocation location) {
        return new DefaultVirtualInvokeTypeFlow(invokeLocation, receiverType, targetMethod, actualParameters, actualReturn, location);
    }

    @Override
    public AbstractSpecialInvokeTypeFlow createSpecialInvokeTypeFlow(BytecodePosition invokeLocation, AnalysisType receiverType, PointsToAnalysisMethod targetMethod,
                    TypeFlow<?>[] actualParameters, ActualReturnTypeFlow actualReturn, BytecodeLocation location) {
        return new DefaultSpecialInvokeTypeFlow(invokeLocation, receiverType, targetMethod, actualParameters, actualReturn, location);
    }

    /** Explicitly context insensitive implementation of the invoke virtual type flow update. */
    private static class DefaultVirtualInvokeTypeFlow extends AbstractVirtualInvokeTypeFlow {

        private TypeState seenReceiverTypes = TypeState.forEmpty();

        protected DefaultVirtualInvokeTypeFlow(BytecodePosition invokeLocation, AnalysisType receiverType, PointsToAnalysisMethod targetMethod,
                        TypeFlow<?>[] actualParameters, ActualReturnTypeFlow actualReturn, BytecodeLocation location) {
            super(invokeLocation, receiverType, targetMethod, actualParameters, actualReturn, location);
        }

        protected DefaultVirtualInvokeTypeFlow(PointsToAnalysis bb, MethodFlowsGraph methodFlows, DefaultVirtualInvokeTypeFlow original) {
            super(bb, methodFlows, original);
        }

        @Override
        public TypeFlow<BytecodePosition> copy(PointsToAnalysis bb, MethodFlowsGraph methodFlows) {
            return new DefaultVirtualInvokeTypeFlow(bb, methodFlows, this);
        }

        @Override
        public void onObservedUpdate(PointsToAnalysis bb) {
            assert this.isClone() || this.isContextInsensitive();
            if (isSaturated()) {
                /* The receiver can saturate while the invoke update was waiting to be scheduled. */
                return;
            }
            TypeState receiverState = getReceiver().getState();
            if (!isContextInsensitive()) {
                /*
                 * The context insensitive invoke receiver doesn't need any filtering, the invoke is
                 * directly linked to its receiver type.
                 */
                receiverState = filterReceiverState(bb, receiverState);
            }

            for (AnalysisType type : receiverState.types(bb)) {
                if (isSaturated()) {
                    /*-
                     * The receiver can become saturated during the callees linking, which saturates
                     * the invoke, when linking the return flow of callees for code patterns like:
                     * 
                     *  Object cur = ...
                     *  while {
                     *      cur = cur.next();
                     *  }
                     */
                    return;
                }
                if (seenReceiverTypes.containsType(type)) {
                    /* Already resolved this type and linked the callee in a previous update. */
                    continue;
                }

                AnalysisMethod method = null;
                try {
                    method = type.resolveConcreteMethod(targetMethod);
                } catch (UnsupportedFeatureException ex) {
                    /* Register the ex with UnsupportedFeatures and allow analysis to continue. */
                    bb.getUnsupportedFeatures().addMessage("resolve_" + targetMethod.format("%H.%n(%p)"), targetMethod, ex.getMessage(), null, ex);
                }

                if (method == null || Modifier.isAbstract(method.getModifiers())) {
                    /*
                     * Type states can be conservative, i.e., we can have receiver types that do not
                     * implement the method. Just ignore such types.
                     */
                    continue;
                }

                assert !Modifier.isAbstract(method.getModifiers());

                MethodTypeFlow callee = PointsToAnalysis.assertPointsToAnalysisMethod(method).getTypeFlow();
                MethodFlowsGraph calleeFlows = callee.addContext(bb, bb.contextPolicy().emptyContext(), this);

                assert callee.getContexts()[0] == bb.contextPolicy().emptyContext();

                /*
                 * Different receiver type can yield the same target method; although it is correct
                 * in a context insensitive analysis to link the callee only if it was not linked
                 * before, in a context sensitive analysis the callee should be linked for each
                 * different context.
                 */
                if (addCallee(callee.getMethod())) {
                    linkCallee(bb, false, calleeFlows);
                }

                updateReceiver(bb, calleeFlows, TypeState.forExactType(bb, type, false));
            }

            /* Remember the types we have already linked. */
            seenReceiverTypes = receiverState;
        }

        @Override
        public void onObservedSaturated(PointsToAnalysis bb, TypeFlow<?> observed) {
            assert this.isClone() && !this.isContextInsensitive();

            setSaturated();

            /*
             * The receiver object flow of the invoke operation is saturated; it will stop sending
             * notifications. Swap the invoke flow with the unique, context-insensitive invoke flow
             * corresponding to the target method, which is already registered as an observer for
             * the type flow of the receiver type and therefore saturated. This is a conservative
             * approximation and this invoke will reach all possible callees.
             */

            /* Deregister the invoke as an observer of the receiver. */
            getReceiver().removeObserver(this);

            /* Unlink all callees. */
            for (AnalysisMethod callee : super.getCallees()) {
                MethodFlowsGraph calleeFlows = PointsToAnalysis.assertPointsToAnalysisMethod(callee).getTypeFlow().getFlows(bb.contextPolicy().emptyContext());
                /* Iterate over the actual parameters in caller context. */
                for (int i = 0; i < actualParameters.length; i++) {
                    /* Get the formal parameter from the callee. */
                    TypeFlow<?> formalParam = calleeFlows.getParameter(i);
                    /* Remove the link between the actual and the formal parameters. */
                    if (actualParameters[i] != null && formalParam != null) {
                        actualParameters[i].removeUse(formalParam);
                    }
                }
                /* Remove the link between the formal and the actual return, if present. */
                if (actualReturn != null && calleeFlows.getReturnFlow() != null) {
                    calleeFlows.getReturnFlow().removeUse(actualReturn);
                }
            }

            /* Link the saturated invoke. */
            AbstractVirtualInvokeTypeFlow contextInsensitiveInvoke = (AbstractVirtualInvokeTypeFlow) targetMethod.initAndGetContextInsensitiveInvoke(bb, source, false);
            contextInsensitiveInvoke.addInvokeLocation(getSource());

            /*
             * Link the call site actual parameters to the saturated invoke actual parameters. The
             * receiver is already set in the saturated invoke.
             */
            for (int i = 1; i < actualParameters.length; i++) {
                /* Primitive type parameters are not modeled, hence null. */
                if (actualParameters[i] != null) {
                    actualParameters[i].addUse(bb, contextInsensitiveInvoke.getActualParameter(i));
                }
            }
            if (actualReturn != null) {
                /* Link the actual return. */
                contextInsensitiveInvoke.getActualReturn().addUse(bb, actualReturn);
            }
        }

        @Override
        public void setSaturated() {
            super.setSaturated();
            if (this.isClone()) {
                /*
                 * If this is a clone, mark the original as saturated too such that
                 * originalInvoke.getCallees() is redirected to the context-insensitive invoke.
                 */
                originalInvoke.setSaturated();
            }
        }

        @Override
        public final Collection<AnalysisMethod> getCallees() {
            if (isSaturated()) {
                return targetMethod.getContextInsensitiveVirtualInvoke().getCallees();
            } else {
                return super.getCallees();
            }
        }

        @Override
        public Collection<MethodFlowsGraph> getCalleesFlows(PointsToAnalysis bb) {
            // collect the flow graphs, one for each analysis method, since it is context
            // insensitive
            Collection<AnalysisMethod> calleesList = getCallees();
            List<MethodFlowsGraph> methodFlowsGraphs = new ArrayList<>(calleesList.size());
            for (AnalysisMethod method : calleesList) {
                methodFlowsGraphs.add(PointsToAnalysis.assertPointsToAnalysisMethod(method).getTypeFlow().getFlows(bb.contextPolicy().emptyContext()));
            }
            return methodFlowsGraphs;
        }

    }

    private static final class DefaultSpecialInvokeTypeFlow extends AbstractSpecialInvokeTypeFlow {

        MethodFlowsGraph calleeFlows = null;

        DefaultSpecialInvokeTypeFlow(BytecodePosition invokeLocation, AnalysisType receiverType, PointsToAnalysisMethod targetMethod,
                        TypeFlow<?>[] actualParameters, ActualReturnTypeFlow actualReturn, BytecodeLocation location) {
            super(invokeLocation, receiverType, targetMethod, actualParameters, actualReturn, location);
        }

        private DefaultSpecialInvokeTypeFlow(PointsToAnalysis bb, MethodFlowsGraph methodFlows, DefaultSpecialInvokeTypeFlow original) {
            super(bb, methodFlows, original);
        }

        @Override
        public TypeFlow<BytecodePosition> copy(PointsToAnalysis bb, MethodFlowsGraph methodFlows) {
            return new DefaultSpecialInvokeTypeFlow(bb, methodFlows, this);
        }

        @Override
        public void onObservedUpdate(PointsToAnalysis bb) {
            assert (this.isClone() || this.isContextInsensitive()) && !isSaturated();
            /* The receiver state has changed. Process the invoke. */

            /*
             * If this is the first time the invoke is updated then set the callee and link the
             * calee's type flows. If this invoke is never updated then the callee will never be
             * set, therefore the callee will be unreachable from this call site.
             */
            initCallee();
            if (calleeFlows == null) {
                calleeFlows = callee.addContext(bb, bb.contextPolicy().emptyContext(), this);
                linkCallee(bb, false, calleeFlows);
            }

            /*
             * Every time the actual receiver state changes in the caller the formal receiver state
             * needs to be updated as there is no direct update link between actual and formal
             * receivers.
             */
            TypeState invokeState = filterReceiverState(bb, getReceiver().getState());
            updateReceiver(bb, calleeFlows, invokeState);
        }

        @Override
        public Collection<MethodFlowsGraph> getCalleesFlows(PointsToAnalysis bb) {
            if (callee == null) {
                /* This static invoke was not updated. */
                return Collections.emptyList();
            } else {
                MethodFlowsGraph methodFlows = callee.getFlows(bb.contextPolicy().emptyContext());
                return Collections.singletonList(methodFlows);
            }
        }
    }

    @Override
    public SingleTypeState singleTypeState(PointsToAnalysis bb, boolean canBeNull, int properties, AnalysisType type, AnalysisObject... objects) {
        return new SingleTypeState(bb, canBeNull, properties, type, objects);
    }

    @Override
    public MultiTypeState multiTypeState(PointsToAnalysis bb, boolean canBeNull, int properties, BitSet typesBitSet, AnalysisObject... objects) {
        return new MultiTypeState(bb, canBeNull, properties, typesBitSet);
    }

    @Override
    public TypeState doUnion(PointsToAnalysis bb, SingleTypeState s1, SingleTypeState s2) {
        if (s1.equals(s2)) {
            return s1;
        }

        boolean resultCanBeNull = s1.canBeNull() || s2.canBeNull();
        if (s1.exactType().equals(s2.exactType())) {

            /* The inputs have the same type, so the result is a SingleTypeState. */

            /* Check if any of the states has the right null state. */
            if (s1.canBeNull() == resultCanBeNull) {
                return s1;
            } else if (s2.canBeNull() == resultCanBeNull) {
                return s2;
            }
            throw AnalysisError.shouldNotReachHere();
        } else {
            /* The inputs have different types, so the result is a MultiTypeState. */
            /* We know the types, construct the types bit set without walking the objects. */
            BitSet typesBitSet = new BitSet();
            typesBitSet.set(s1.exactType().getId());
            typesBitSet.set(s2.exactType().getId());

            TypeState result = new MultiTypeState(bb, resultCanBeNull, 0, typesBitSet);
            PointsToStats.registerUnionOperation(bb, s1, s2, result);
            return result;
        }
    }

    @Override
    public TypeState doUnion(PointsToAnalysis bb, MultiTypeState s1, SingleTypeState s2) {
        boolean resultCanBeNull = s1.canBeNull() || s2.canBeNull();

        if (s1.containsType(s2.exactType())) {
            /* Objects of the same type as s2 are contained in s1. */
            return s1.forCanBeNull(bb, resultCanBeNull);
        } else {
            BitSet typesBitSet = TypeStateUtils.set(s1.typesBitSet(), s2.exactType().getId());
            MultiTypeState result = new MultiTypeState(bb, resultCanBeNull, 0, typesBitSet);
            PointsToStats.registerUnionOperation(bb, s1, s2, result);
            return result;
        }
    }

    @Override
    public TypeState doUnion(PointsToAnalysis bb, MultiTypeState s1, MultiTypeState s2) {
        assert s1.objectsCount() >= s2.objectsCount();

        boolean resultCanBeNull = s1.canBeNull() || s2.canBeNull();

        /*
         * No need for a deep equality check (which would need to iterate the arrays), since the
         * speculation logic below is doing that anyway.
         */
        if (s1.typesBitSet() == s2.typesBitSet()) {
            return s1.forCanBeNull(bb, resultCanBeNull);
        }

        /* Speculate that s1 is a superset of s2. */
        if (TypeStateUtils.isSuperset(s1.typesBitSet(), s2.typesBitSet())) {
            return s1.forCanBeNull(bb, resultCanBeNull);
        }

        /* Logical OR the type bit sets. */
        BitSet resultTypesBitSet = TypeStateUtils.or(s1.typesBitSet(), s2.typesBitSet());

        MultiTypeState result = new MultiTypeState(bb, resultCanBeNull, 0, resultTypesBitSet);
        /* The result can be equal to s2 only if s1 and s2 have the same number of types. */
        if (s1.typesCount() == s2.typesCount() && result.equals(s2)) {
            return s2.forCanBeNull(bb, resultCanBeNull);
        }

        PointsToStats.registerUnionOperation(bb, s1, s2, result);

        return result;

    }

    @Override
    public TypeState doIntersection(PointsToAnalysis bb, MultiTypeState s1, SingleTypeState s2) {
        /* See comment above for the limitation explanation. */
        assert !bb.extendedAsserts() || TypeStateUtils.isContextInsensitiveTypeState(s2) : "Current implementation limitation.";

        boolean resultCanBeNull = s1.canBeNull() && s2.canBeNull();
        if (s1.containsType(s2.exactType())) {
            /* The s2's type is contained in s1, so pick all objects of the same type from s1. */
            // return new SingleTypeState(bb, resultCanBeNull, 0, s2.exactType());
            return s2.forCanBeNull(bb, resultCanBeNull);
        } else {
            return TypeState.forEmpty().forCanBeNull(bb, resultCanBeNull);
        }
    }

    @Override
    public TypeState doIntersection(PointsToAnalysis bb, MultiTypeState s1, MultiTypeState s2) {
        /* Speculate that s1 and s2 have either the same types, or no types in common. */
        boolean resultCanBeNull = s1.canBeNull() && s2.canBeNull();

        if (s1.typesBitSet().equals(s2.typesBitSet())) {
            /* Speculate that s1 and s2 have the same types, i.e., the result is s1. */
            return s1.forCanBeNull(bb, resultCanBeNull);
        }

        if (!s1.typesBitSet().intersects(s2.typesBitSet())) {
            /* Speculate that s1 and s2 have no types in common, i.e., the result is empty. */
            return TypeState.forEmpty().forCanBeNull(bb, resultCanBeNull);
        }

        /*
         * Speculate that s2 contains all types of s1, i.e., the filter is broader than s1, thus the
         * result is s1.
         */
        if (TypeStateUtils.isSuperset(s2.typesBitSet(), s1.typesBitSet())) {
            return s1.forCanBeNull(bb, resultCanBeNull);
        }

        BitSet resultTypesBitSet = TypeStateUtils.and(s1.typesBitSet(), s2.typesBitSet());
        if (resultTypesBitSet.cardinality() == 0) {
            return TypeState.forEmpty().forCanBeNull(bb, resultCanBeNull);
        } else if (resultTypesBitSet.cardinality() == 1) {
            AnalysisType type = bb.universe.getType(resultTypesBitSet.nextSetBit(0));
            return new SingleTypeState(bb, resultCanBeNull, 0, type);
        } else {
            MultiTypeState result = new MultiTypeState(bb, resultCanBeNull, 0, resultTypesBitSet);

            /*
             * The result can be equal to s1 if and only if s1 and s2 have the same type count.
             */
            if (s1.typesCount() == s2.typesCount() && result.equals(s1)) {
                return s1.forCanBeNull(bb, resultCanBeNull);
            }

            return result;
        }
    }

    @Override
    public TypeState doSubtraction(PointsToAnalysis bb, MultiTypeState s1, SingleTypeState s2) {
        assert !bb.extendedAsserts() || TypeStateUtils.isContextInsensitiveTypeState(s2) : "Current implementation limitation.";
        boolean resultCanBeNull = s1.canBeNull() && !s2.canBeNull();
        if (s1.containsType(s2.exactType())) {
            /* s2 is contained in s1, so remove all objects of the same type from s1. */
            BitSet resultTypesBitSet = TypeStateUtils.clear(s1.typesBitSet(), s2.exactType().getId());
            assert resultTypesBitSet.cardinality() > 0;
            if (resultTypesBitSet.cardinality() == 1) {
                AnalysisType type = bb.universe.getType(resultTypesBitSet.nextSetBit(0));
                return new SingleTypeState(bb, resultCanBeNull, 0, type);
            } else {
                return new MultiTypeState(bb, resultCanBeNull, 0, resultTypesBitSet);
            }
        } else {
            return s1.forCanBeNull(bb, resultCanBeNull);
        }
    }

    @Override
    public TypeState doSubtraction(PointsToAnalysis bb, MultiTypeState s1, MultiTypeState s2) {
        boolean resultCanBeNull = s1.canBeNull() && !s2.canBeNull();

        /* Speculate that s1 and s2 have either the same types, or no types in common. */
        if (s1.typesBitSet().equals(s2.typesBitSet())) {
            /* Speculate that s1 and s2 have the same types, i.e., the result is empty set. */
            return TypeState.forEmpty().forCanBeNull(bb, resultCanBeNull);
        }

        if (!s1.typesBitSet().intersects(s2.typesBitSet())) {
            /* Speculate that s1 and s2 have no types in common, i.e., the result is s1. */
            return s1.forCanBeNull(bb, resultCanBeNull);
        }

        /*
         * Speculate that s2 contains all types of s1, i.e., the filter is broader than s1, thus the
         * result is empty.
         */
        if (TypeStateUtils.isSuperset(s2.typesBitSet(), s1.typesBitSet())) {
            return TypeState.forEmpty().forCanBeNull(bb, resultCanBeNull);
        }

        BitSet resultTypesBitSet = TypeStateUtils.andNot(s1.typesBitSet(), s2.typesBitSet());
        if (resultTypesBitSet.cardinality() == 0) {
            return TypeState.forEmpty().forCanBeNull(bb, resultCanBeNull);
        } else if (resultTypesBitSet.cardinality() == 1) {
            AnalysisType type = bb.universe.getType(resultTypesBitSet.nextSetBit(0));
            return new SingleTypeState(bb, resultCanBeNull, 0, type);
        } else {
            return new MultiTypeState(bb, resultCanBeNull, 0, resultTypesBitSet);
        }
    }

}
