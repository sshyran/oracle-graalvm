/*
 * Copyright (c) 2013, 2021, Oracle and/or its affiliates. All rights reserved.
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
package com.oracle.graal.pointsto.typestate;

import java.lang.reflect.Modifier;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.Iterator;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

import com.oracle.graal.pointsto.AnalysisPolicy;
import com.oracle.graal.pointsto.BigBang;
import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.api.PointstoOptions;
import com.oracle.graal.pointsto.flow.context.AnalysisContext;
import com.oracle.graal.pointsto.flow.context.BytecodeLocation;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.util.BitArrayUtils;

import com.oracle.graal.pointsto.util.ListUtils;
import jdk.vm.ci.meta.JavaConstant;

public abstract class TypeState {

    /** TypeState id is only be used for statistics. */
    private int id = -1;

    /** A bit array of properties for this type state. */
    protected final int properties;

    public TypeState(int properties) {
        this.properties = properties;
    }

    /* Instance methods. */

    public int getProperties() {
        return properties;
    }

    /* Types accessing methods. */

    /** Returns true if the type state contains exact the same types as the bit set. */
    public abstract boolean hasExactTypes(BitSet typesBitSet);

    /** Get the number of types. */
    public abstract int typesCount();

    /**
     * If this type state has a single, exact type it returns that type, otherwise it returns null.
     */
    public abstract AnalysisType exactType();

    /** Provides an iterator over the types. */
    protected abstract Iterator<AnalysisType> typesIterator(BigBang bb);

    /** Provides an iterable for the types for easy "for-each loop" iteration. */
    public Iterable<AnalysisType> types(BigBang bb) {
        return () -> typesIterator(bb);
    }

    /** Provides a stream for the types. */
    public Stream<AnalysisType> typesStream(BigBang bb) {
        return StreamSupport.stream(types(bb).spliterator(), false);
    }

    /** Returns true if this type state contains the type, otherwise it returns false. */
    public abstract boolean containsType(AnalysisType exactType);

    /* Objects accessing methods. */

    /** Get the number of objects. */
    public abstract int objectsCount();

    /** Returns the objects as an array. */
    public abstract AnalysisObject[] objects();

    public abstract Iterable<AnalysisObject> objectsIterable();

    /** Returns the objects corresponding to the type. It copies those objects to a new array. */
    public abstract AnalysisObject[] objectsArray(AnalysisType type);

    /**
     * Provides an iterator for the objects corresponding to the type. The objects are returned from
     * the internal objects array and are not materialized to a different data structure.
     */
    protected abstract Iterator<AnalysisObject> objectsIterator(AnalysisType type);

    /**
     * Provides an iterable for the objects corresponding to the type. The objects are returned from
     * the internal objects array and are not materialized to a different data structure.
     */
    public Iterable<AnalysisObject> objects(AnalysisType type) {
        return () -> objectsIterator(type);
    }

    /** Provides a stream for the objects. */
    public Stream<AnalysisObject> objectsStream() {
        return Arrays.stream(objects());
    }

    /** Returns true if this type state contains the object, otherwise it returns false. */
    public boolean containsObject(AnalysisObject object) {
        /* AnalysisObject implements Comparable and the objects array is always sorted by ID. */
        return containsType(object.type()) && Arrays.binarySearch(objects(), object) >= 0;
    }

    /**
     * Provides a special iterator for the type state. It iterates over analysis types and objects
     * in tandem doing a single pass over the objects array. See {@link TypesObjectsIterator} for a
     * complete explanation.
     */
    public TypesObjectsIterator getTypesObjectsIterator() {
        return new TypesObjectsIterator(this);
    }

    /**
     * This is a special iterator for the type state. It iterates over analysis types and objects in
     * tandem doing a single pass over the objects array. It relies on the fact that the types and
     * objects are sorted by ID. It is meant for situations where the types need some pre-processing
     * or checking before processing their respective objects, e.g., as in virtual method resolution
     * for InvokeTypeFlow. It those situations it avoids iterating over the types first and then
     * searching for the range of objects corresponding to that type. When only objects, or only
     * types, or only objects of a certain type need to be iterated use the other provided
     * iterators. A correct use of this iterator is as follows:
     *
     * <code>
     * TypesObjectsIterator toi = state.getTypesObjectsIterator();
     *
     * while(toi.hasNextType()) {
     *      AnalysisType t = toi.nextType();
     *      // use type here
     *
     *      while(toi.hasNextObject(t)) {
     *          AnalysisObject o = toi.nextObject(t);
     *          // use object here
     *      }
     * }
     * </code>
     */
    public static class TypesObjectsIterator {

        private final TypeState state;
        private int typeIdx = 0;
        private int objectIdx = 0;

        public TypesObjectsIterator(TypeState state) {
            this.state = state;
        }

        /**
         * Returns true if there is a next type in the objects array, i.e., there are objects of a
         * type other than the current type.
         */
        public boolean hasNextType() {
            return typeIdx < state.typesCount();
        }

        /** Returns true if there are more objects of the current type. */
        public boolean hasNextObject(AnalysisType type) {
            return objectIdx < state.objects().length && state.objects()[objectIdx].getTypeId() == type.getId();
        }

        /** Gets the next type. */
        public AnalysisType nextType() {
            /* Check that there is a next type. */
            assert hasNextType();
            /* Increment the type index. */
            typeIdx++;
            /* Return the type at the 'objectIdx. */
            return state.objects()[objectIdx].type();
        }

        /** Gets the next object. */
        public AnalysisObject nextObject(AnalysisType type) {
            /* Check that there is a next object of the desired type. */
            assert hasNextObject(type);
            /* Return the next object and increment objectIdx. */
            return state.objects()[objectIdx++];
        }
    }

    public boolean isAllocation() {
        return objects().length == 1 && objects()[0].isAllocationContextSensitiveObject();
    }

    public boolean isConstant() {
        return objects().length == 1 && objects()[0].isConstantContextSensitiveObject();
    }

    public boolean isEmpty() {
        return this == EmptyTypeState.SINGLETON;
    }

    public boolean isSingleTypeState() {
        return this.typesCount() == 1;
    }

    public boolean isMultiTypeState() {
        return this instanceof MultiTypeState;
    }

    public boolean isNull() {
        return this == NullTypeState.SINGLETON;
    }

    public abstract boolean canBeNull();

    /** Note that the objects of this type state have been merged. */
    public void noteMerge(@SuppressWarnings("unused") PointsToAnalysis bb) {
    }

    public boolean isMerged() {
        return false;
    }

    /**
     * This method is needed for accessing the SingleTypeState associated with an specific type of a
     * MutiTypeState, e.g. for transferring the state from a virtual invoke type flow to the formal
     * receiver flow of a specific callee resolved on the specified type.
     */
    public abstract TypeState exactTypeState(PointsToAnalysis bb, AnalysisType exactType);

    public boolean verifyDeclaredType(BigBang bb, AnalysisType declaredType) {
        if (declaredType != null) {
            for (AnalysisType e : types(bb)) {
                if (!declaredType.isAssignableFrom(e)) {
                    return false;
                }
            }
        }
        return true;
    }

    @Override
    public int hashCode() {
        return super.hashCode();
    }

    @Override
    public abstract boolean equals(Object o);

    public int getId(PointsToAnalysis bb) {
        assert bb.reportAnalysisStatistics() : "TypeState id should only be used for statistics.";
        return id;
    }

    public void setId(PointsToAnalysis bb, int id) {
        assert bb.reportAnalysisStatistics() : "TypeState id should only be used for statistics.";
        this.id = id;
    }

    /* Static methods. */

    public static TypeState forEmpty() {
        return EmptyTypeState.SINGLETON;
    }

    public static TypeState forNull() {
        return NullTypeState.SINGLETON;
    }

    /** Wraps an analysis object into a non-null type state. */
    public static TypeState forNonNullObject(PointsToAnalysis bb, AnalysisObject object) {
        return bb.analysisPolicy().singleTypeState(bb, false, bb.analysisPolicy().makeProperties(bb, object), object.type(), object);
    }

    /** Wraps the analysis object corresponding to a JavaConstant into a non-null type state. */
    public static TypeState forConstant(PointsToAnalysis bb, JavaConstant constant, AnalysisType exactType) {
        assert !constant.isNull();
        assert exactType.isArray() || (exactType.isInstanceClass() && !Modifier.isAbstract(exactType.getModifiers())) : exactType;

        AnalysisObject constantObject = bb.analysisPolicy().createConstantObject(bb, constant, exactType);
        return forNonNullObject(bb, constantObject);
    }

    /** Wraps the analysis object corresponding to an allocation site into a non-null type state. */
    public static TypeState forAllocation(PointsToAnalysis bb, BytecodeLocation allocationLabel, AnalysisType exactType) {
        return forAllocation(bb, allocationLabel, exactType, bb.contextPolicy().emptyContext());
    }

    /**
     * Wraps the analysis object corresponding to an allocation site for a given context into a
     * non-null type state.
     */
    public static TypeState forAllocation(PointsToAnalysis bb, BytecodeLocation allocationSite, AnalysisType objectType, AnalysisContext allocationContext) {
        assert objectType.isArray() || (objectType.isInstanceClass() && !Modifier.isAbstract(objectType.getModifiers())) : objectType;

        AnalysisObject allocationObject = bb.analysisPolicy().createHeapObject(bb, objectType, allocationSite, allocationContext);
        return forNonNullObject(bb, allocationObject);
    }

    /**
     * Wraps the analysis object corresponding to a clone site for a given context into a non-null
     * type state.
     */
    public static TypeState forClone(PointsToAnalysis bb, BytecodeLocation cloneSite, AnalysisType type, AnalysisContext allocationContext) {
        return forAllocation(bb, cloneSite, type, allocationContext);
    }

    public static TypeState forExactType(PointsToAnalysis bb, AnalysisType exactType, boolean canBeNull) {
        return forExactType(bb, exactType.getContextInsensitiveAnalysisObject(), canBeNull);
    }

    public static TypeState forExactType(PointsToAnalysis bb, AnalysisObject object, boolean canBeNull) {
        assert object.type().isArray() || (object.type().isInstanceClass() && !Modifier.isAbstract(object.type().getModifiers())) : object.type();
        return bb.analysisPolicy().singleTypeState(bb, canBeNull, bb.analysisPolicy().makeProperties(bb, object), object.type(), object);
    }

    public static TypeState forType(PointsToAnalysis bb, AnalysisType type, boolean canBeNull) {
        return forType(bb, type.getContextInsensitiveAnalysisObject(), canBeNull);
    }

    public static TypeState forType(PointsToAnalysis bb, AnalysisObject object, boolean canBeNull) {
        return bb.analysisPolicy().singleTypeState(bb, canBeNull, bb.analysisPolicy().makeProperties(bb, object), object.type(), object);
    }

    /**
     * Simplifies a type state by replacing all context sensitive objects with context insensitive
     * objects.
     */
    public static TypeState forContextInsensitiveTypeState(PointsToAnalysis bb, TypeState state) {
        if (!PointstoOptions.AllocationSiteSensitiveHeap.getValue(bb.getOptions()) ||
                        state.isEmpty() || state.isNull()) {
            /* The type state is already context insensitive. */
            return state;
        } else {
            if (state.isSingleTypeState()) {
                AnalysisType type = state.exactType();
                AnalysisObject analysisObject = type.getContextInsensitiveAnalysisObject();
                return new SingleTypeState(bb, state.canBeNull(), bb.analysisPolicy().makeProperties(bb, analysisObject), analysisObject.type());
            } else {
                MultiTypeState multiState = (MultiTypeState) state;
                AnalysisObject[] objectsArray = new AnalysisObject[multiState.typesCount()];

                int i = 0;
                for (AnalysisType type : multiState.types(bb)) {
                    objectsArray[i++] = type.getContextInsensitiveAnalysisObject();
                }
                /*
                 * For types use the already created bit set. Since the original type state is
                 * immutable its types bit set cannot change.
                 */

                BitSet typesBitSet = multiState.typesBitSet;
                int properties = bb.analysisPolicy().makeProperties(bb, objectsArray);
                return new ContextSensitiveMultiTypeState(bb, multiState.canBeNull(), properties, typesBitSet, objectsArray);
            }
        }
    }

    public final TypeState forNonNull(PointsToAnalysis bb) {
        return forCanBeNull(bb, false);
    }

    public abstract TypeState forCanBeNull(PointsToAnalysis bb, boolean stateCanBeNull);

    public static TypeState forUnion(PointsToAnalysis bb, TypeState s1, TypeState s2) {
        if (s1.isEmpty()) {
            return s2;
        } else if (s1.isNull()) {
            return s2.forCanBeNull(bb, true);
        } else if (s2.isEmpty()) {
            return s1;
        } else if (s2.isNull()) {
            return s1.forCanBeNull(bb, true);
        } else if (s1 instanceof SingleTypeState && s2 instanceof SingleTypeState) {
            return bb.analysisPolicy().doUnion(bb, (SingleTypeState) s1, (SingleTypeState) s2);
        } else if (s1 instanceof SingleTypeState && s2 instanceof MultiTypeState) {
            return bb.analysisPolicy().doUnion(bb, (MultiTypeState) s2, (SingleTypeState) s1);
        } else if (s1 instanceof MultiTypeState && s2 instanceof SingleTypeState) {
            return bb.analysisPolicy().doUnion(bb, (MultiTypeState) s1, (SingleTypeState) s2);
        } else {
            assert s1 instanceof MultiTypeState && s2 instanceof MultiTypeState;
            if (s1.objectsCount() >= s2.objectsCount()) {
                return bb.analysisPolicy().doUnion(bb, (MultiTypeState) s1, (MultiTypeState) s2);
            } else {
                return bb.analysisPolicy().doUnion(bb, (MultiTypeState) s2, (MultiTypeState) s1);
            }
        }
    }

    public static TypeState forIntersection(PointsToAnalysis bb, TypeState s1, TypeState s2) {
        /*
         * All filtered types (s1) must be marked as instantiated to ensures that the filter state
         * (s2) has been updated before a type appears in the input, otherwise types can be missed.
         */
        assert !bb.extendedAsserts() || checkTypes(bb, s1);
        if (s1.isEmpty()) {
            return s1;
        } else if (s1.isNull()) {
            return s1.forCanBeNull(bb, s2.canBeNull());
        } else if (s2.isEmpty()) {
            return s2;
        } else if (s2.isNull()) {
            return s2.forCanBeNull(bb, s1.canBeNull());
        } else if (s1 instanceof SingleTypeState && s2 instanceof SingleTypeState) {
            return bb.analysisPolicy().doIntersection(bb, (SingleTypeState) s1, (SingleTypeState) s2);
        } else if (s1 instanceof SingleTypeState && s2 instanceof MultiTypeState) {
            return bb.analysisPolicy().doIntersection(bb, (SingleTypeState) s1, (MultiTypeState) s2);
        } else if (s1 instanceof MultiTypeState && s2 instanceof SingleTypeState) {
            return bb.analysisPolicy().doIntersection(bb, (MultiTypeState) s1, (SingleTypeState) s2);
        } else {
            assert s1 instanceof MultiTypeState && s2 instanceof MultiTypeState;
            return bb.analysisPolicy().doIntersection(bb, (MultiTypeState) s1, (MultiTypeState) s2);
        }
    }

    public static TypeState forSubtraction(PointsToAnalysis bb, TypeState s1, TypeState s2) {
        /*
         * All filtered types (s1) must be marked as instantiated to ensures that the filter state
         * (s2) has been updated before a type appears in the input, otherwise types can be missed.
         */
        assert !bb.extendedAsserts() || checkTypes(bb, s1);
        if (s1.isEmpty()) {
            return s1;
        } else if (s1.isNull()) {
            return s1.forCanBeNull(bb, !s2.canBeNull());
        } else if (s2.isEmpty()) {
            return s1;
        } else if (s2.isNull()) {
            return s1.forCanBeNull(bb, false);
        } else if (s1 instanceof SingleTypeState && s2 instanceof SingleTypeState) {
            return bb.analysisPolicy().doSubtraction(bb, (SingleTypeState) s1, (SingleTypeState) s2);
        } else if (s1 instanceof SingleTypeState && s2 instanceof MultiTypeState) {
            return bb.analysisPolicy().doSubtraction(bb, (SingleTypeState) s1, (MultiTypeState) s2);
        } else if (s1 instanceof MultiTypeState && s2 instanceof SingleTypeState) {
            return bb.analysisPolicy().doSubtraction(bb, (MultiTypeState) s1, (SingleTypeState) s2);
        } else {
            assert s1 instanceof MultiTypeState && s2 instanceof MultiTypeState;
            return bb.analysisPolicy().doSubtraction(bb, (MultiTypeState) s1, (MultiTypeState) s2);
        }
    }

    private static boolean checkTypes(BigBang bb, TypeState state) {
        for (AnalysisType type : state.types(bb)) {
            if (!type.isInstantiated()) {
                System.out.println("Processing a type not yet marked as instantiated: " + type.getName());
                return false;
            }
        }
        return true;
    }

}

final class EmptyTypeState extends TypeState {

    protected static final TypeState SINGLETON = new EmptyTypeState();

    private EmptyTypeState() {
        super(BitArrayUtils.EMPTY_BIT_ARRAY);
    }

    @Override
    public boolean hasExactTypes(BitSet typesBitSet) {
        if (typesBitSet.isEmpty()) {
            return true;
        }
        return false;
    }

    @Override
    public AnalysisType exactType() {
        return null;
    }

    @Override
    public int typesCount() {
        return 0;
    }

    @Override
    public Iterator<AnalysisType> typesIterator(BigBang bb) {
        return Collections.emptyIterator();
    }

    @Override
    public AnalysisObject[] objectsArray(AnalysisType type) {
        return AnalysisObject.EMPTY_ARRAY;
    }

    @Override
    public Iterator<AnalysisObject> objectsIterator(AnalysisType type) {
        return Collections.emptyIterator();
    }

    @Override
    public boolean containsType(AnalysisType exactType) {
        return false;
    }

    @Override
    public boolean containsObject(AnalysisObject object) {
        return false;
    }

    @Override
    public TypeState exactTypeState(PointsToAnalysis bb, AnalysisType exactType) {
        return this;
    }

    @Override
    public TypeState forCanBeNull(PointsToAnalysis bb, boolean stateCanBeNull) {
        return stateCanBeNull ? NullTypeState.SINGLETON : EmptyTypeState.SINGLETON;
    }

    @Override
    public int objectsCount() {
        return 0;
    }

    @Override
    public AnalysisObject[] objects() {
        return AnalysisObject.EMPTY_ARRAY;
    }

    @Override
    public Iterable<AnalysisObject> objectsIterable() {
        return Collections.emptyList();
    }

    @Override
    public boolean canBeNull() {
        return false;
    }

    @Override
    public boolean equals(Object obj) {
        return this == obj;
    }

    @Override
    public String toString() {
        return "Empty";
    }
}

final class NullTypeState extends TypeState {

    protected static final TypeState SINGLETON = new NullTypeState();

    private NullTypeState() {
        super(BitArrayUtils.EMPTY_BIT_ARRAY);
    }

    @Override
    public boolean hasExactTypes(BitSet typesBitSet) {
        if (typesBitSet.isEmpty()) {
            return true;
        }
        return false;
    }

    @Override
    public AnalysisType exactType() {
        return null;
    }

    @Override
    public int typesCount() {
        return 0;
    }

    @Override
    public Iterator<AnalysisType> typesIterator(BigBang bb) {
        return Collections.emptyIterator();
    }

    @Override
    public Iterator<AnalysisObject> objectsIterator(AnalysisType type) {
        return Collections.emptyIterator();
    }

    @Override
    public AnalysisObject[] objectsArray(AnalysisType type) {
        return AnalysisObject.EMPTY_ARRAY;
    }

    @Override
    public boolean containsType(AnalysisType exactType) {
        return false;
    }

    @Override
    public boolean containsObject(AnalysisObject object) {
        return false;
    }

    @Override
    public TypeState exactTypeState(PointsToAnalysis bb, AnalysisType exactType) {
        return this;
    }

    @Override
    public TypeState forCanBeNull(PointsToAnalysis bb, boolean stateCanBeNull) {
        return stateCanBeNull ? NullTypeState.SINGLETON : EmptyTypeState.SINGLETON;
    }

    @Override
    public boolean equals(Object obj) {
        return this == obj;
    }

    @Override
    public int objectsCount() {
        return 0;
    }

    @Override
    public AnalysisObject[] objects() {
        return AnalysisObject.EMPTY_ARRAY;
    }

    @Override
    public Iterable<AnalysisObject> objectsIterable() {
        return Collections.emptyList();
    }

    @Override
    public boolean canBeNull() {
        return true;
    }

    @Override
    public String toString() {
        return "Null";
    }

}
