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

import java.util.BitSet;
import java.util.Iterator;
import java.util.stream.Collectors;

import com.oracle.graal.pointsto.BigBang;
import com.oracle.graal.pointsto.PointsToAnalysis;
import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;
import com.oracle.graal.pointsto.meta.AnalysisType;
import com.oracle.graal.pointsto.meta.AnalysisUniverse;
import com.oracle.graal.pointsto.util.AnalysisError;

public class MultiTypeState extends TypeState {

    /**
     * Keep a bit set for types to easily answer queries like contains type or types count, and
     * quickly iterate over the types. It costs us one linear pass over the objects when the state
     * is first created but the cost is amortized for frequently used states.
     */
    protected final BitSet typesBitSet;
    /** Cache the number of types since BitSet.cardinality() computes it every time is called. */
    protected final int typesCount;
    /** Can this type state represent the null value? */
    protected final boolean canBeNull;
    /** Has this type state been merged with the all-instantiated type state? */
    protected boolean merged;
    protected final BigBang bb;

    /** Creates a new type state using the provided types bit set and objects. */
    public MultiTypeState(PointsToAnalysis bb, boolean canBeNull, int properties, BitSet typesBitSet) {
        super(properties);
        /*
         * Trim the typesBitSet to size eagerly. The typesBitSet is effectively immutable, i.e., no
         * calls to mutating methods are made on it after it is set in the MultiTypeState, thus we
         * don't need to use any external synchronization. However, to keep it immutable we use
         * BitSet.clone() when deriving a new BitSet since the set operations (and, or, etc.) mutate
         * the original object. The problem is that BitSet.clone() breaks the informal contract that
         * the clone method should not modify the original object; it calls trimToSize() before
         * creating a copy. Thus, trimming the bit set here ensures that cloning does not modify the
         * typesBitSet. Since BitSet is not thread safe mutating it during cloning is problematic in
         * a multithreaded environment. If for example you iterate over the bits at the same time as
         * another thread calls clone() the words[] array can be in an inconsistent state.
         */
        TypeStateUtils.trimBitSetToSize(typesBitSet);
        this.typesBitSet = typesBitSet;
        long cardinality = typesBitSet.cardinality();
        assert cardinality < Integer.MAX_VALUE : "We don't expect so much types.";
        this.typesCount = (int) cardinality;
        this.canBeNull = canBeNull;
        this.merged = false;
        this.bb = bb;
        assert typesCount > 1 : "Multi type state with single type.";
        PointsToStats.registerTypeState(bb, this);
    }

    /** Create a type state with the same content and a reversed canBeNull value. */
    protected MultiTypeState(PointsToAnalysis bb, boolean canBeNull, MultiTypeState other) {
        super(other.properties);
        this.typesBitSet = other.typesBitSet;
        this.typesCount = other.typesCount;
        this.canBeNull = canBeNull;
        this.merged = other.merged;
        this.bb = other.bb;
        PointsToStats.registerTypeState(bb, this);
    }

    /** Get the number of objects. */
    @Override
    public int objectsCount() {
        return typesCount;
    }

    /** Returns the objects as an array. */
    @Override
    public AnalysisObject[] objects() {
        return typesStream(bb).map(AnalysisType::getContextInsensitiveAnalysisObject).toArray(AnalysisObject[]::new);
    }

    @Override
    public Iterable<AnalysisObject> objectsIterable() {
        return typesStream(bb).map(AnalysisType::getContextInsensitiveAnalysisObject).collect(Collectors.toList());
    }

    @Override
    public boolean hasExactTypes(BitSet inputTypesBitSet) {
        return typesBitSet.equals(inputTypesBitSet);
    }

    @Override
    public AnalysisType exactType() {
        return typesCount == 1 ? typesIterator(bb).next() : null;
    }

    @Override
    public int typesCount() {
        return typesCount;
    }

    public BitSet typesBitSet() {
        return typesBitSet;
    }

    /**
     * It iterates over the types bit set and gets the types using
     * {@link AnalysisUniverse#getType(int)}. The types are iterated in ascending order of their IDs
     * by way of bit set iteration.
     */
    @Override
    public Iterator<AnalysisType> typesIterator(BigBang bb) {
        return new Iterator<>() {

            /** Initialize to the index of the first set bit. */
            private int currentTypeId = typesBitSet.nextSetBit(0);

            @Override
            public boolean hasNext() {
                return currentTypeId >= 0;
            }

            @Override
            public AnalysisType next() {
                AnalysisType next = bb.getUniverse().getType(currentTypeId);
                currentTypeId = typesBitSet.nextSetBit(currentTypeId + 1);
                return next;
            }
        };
    }

    @Override
    public boolean containsType(AnalysisType exactType) {
        return typesBitSet.get(exactType.getId());
    }

    @Override
    public TypeState exactTypeState(PointsToAnalysis bb, AnalysisType exactType) {
        if (containsType(exactType)) {
            AnalysisObject[] resultObjects = objectsArray(exactType);
            return new SingleTypeState(bb, canBeNull, bb.analysisPolicy().makeProperties(bb, resultObjects), resultObjects);
        } else {
            return EmptyTypeState.SINGLETON;
        }
    }

    @Override
    public TypeState forCanBeNull(PointsToAnalysis bb, boolean resultCanBeNull) {
        if (resultCanBeNull == this.canBeNull()) {
            return this;
        } else {
            /* Just flip the canBeNull flag and copy the rest of the values from this. */
            return new MultiTypeState(bb, resultCanBeNull, this);
        }
    }

    @Override
    public AnalysisObject[] objectsArray(AnalysisType type) {
        throw AnalysisError.shouldNotReachHere("unimplemented");
    }

    @Override
    public Iterator<AnalysisObject> objectsIterator(AnalysisType exactType) {
        throw AnalysisError.shouldNotReachHere("unimplemented");
    }

    @Override
    public final boolean canBeNull() {
        return canBeNull;
    }

    /** Note that the objects of this type state have been merged. */
    @Override
    public void noteMerge(PointsToAnalysis bb) {
        assert bb.analysisPolicy().isMergingEnabled();

        if (!merged) {
            for (AnalysisType type : types(bb)) {
                type.getContextInsensitiveAnalysisObject().noteMerge(bb);
            }
            merged = true;
        }
    }

    @Override
    public boolean isMerged() {
        return merged;
    }

    @Override
    public int hashCode() {
        int result = 1;
        result = 31 * result + typesBitSet.hashCode();
        result = 31 * result + (canBeNull ? 1 : 0);
        return result;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }

        MultiTypeState that = (MultiTypeState) o;
        return this.canBeNull == that.canBeNull &&
                        this.typesCount == that.typesCount && this.typesBitSet.equals(that.typesBitSet);
    }

    @Override
    public String toString() {
        return "MType<" + typesCount + ":" + (canBeNull ? "null," : "") + "TODO" + ">";
    }
}
