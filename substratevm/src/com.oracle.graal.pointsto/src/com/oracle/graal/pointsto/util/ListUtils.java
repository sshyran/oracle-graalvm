package com.oracle.graal.pointsto.util;

import com.oracle.graal.pointsto.flow.context.object.AnalysisObject;

import java.util.Arrays;

public class ListUtils {

    public static final class UnsafeArrayListClosable<E> implements AutoCloseable {
        private UnsafeArrayList<E> list;
        private boolean closed = true;

        private UnsafeArrayListClosable(UnsafeArrayList<E> list) {
            this.list = list;
        }

        public UnsafeArrayList<E> list() {
            return list;
        }

        @Override
        public void close() {
            list.clear();
            closed = true;
        }
    }

    public static UnsafeArrayListClosable<AnalysisObject> getTLArrayList(ThreadLocal<UnsafeArrayListClosable<AnalysisObject>> tl, int initialCapacity) {
        UnsafeArrayListClosable<AnalysisObject> result = tl.get();
        if (result == null) {
            result = new UnsafeArrayListClosable<>(new UnsafeArrayList<>(new AnalysisObject[initialCapacity]));
            tl.set(result);
        }
        if (result.closed) {
            result.closed = false;
            return result;
        } else {
            /*
             * Happens very rarely that the same operation is done recursively. If this happens more
             * often we should introduce a stack of arrays.
             */
            return new UnsafeArrayListClosable<>(new UnsafeArrayList<>(new AnalysisObject[initialCapacity]));
        }
    }

    public static class UnsafeArrayList<E> {

        static final int MAX_ARRAY_SIZE = Integer.MAX_VALUE - 8;
        E[] elementData;
        int size;

        UnsafeArrayList(E[] initial) {
            elementData = initial;
        }

        public <T> T[] copyToArray(T[] a) {
            System.arraycopy(elementData, 0, a, 0, size);
            return a;
        }

        public <T> T[] copyToArray(T[] a, int dstPos) {
            System.arraycopy(elementData, 0, a, dstPos, size);
            return a;
        }

        public <E1 extends E> void addAll(E1[] c, int startIndex, int endIndex) {
            assert startIndex <= endIndex : "start index can't be smaller than the end index.";
            int newElements = endIndex - startIndex;
            ensureCapacity(size() + newElements);
            System.arraycopy(c, startIndex, elementData, size, newElements);
            size += newElements;
        }

        public int size() {
            return size;
        }

        public E[] elementData() {
            return elementData;
        }

        public void add(E e) {
            ensureCapacity(size + 1);
            elementData[size] = e;
            size = size + 1;
        }

        public void clear() {
            for (int i = 0; i < size; i++) {
                elementData[i] = null;
            }

            size = 0;
        }

        public E get(int i) {
            assert i < size && i >= 0;
            return elementData[i];
        }

        private void ensureCapacity(int minCapacity) {
            if (minCapacity - elementData.length > 0) {
                grow(minCapacity);
            }
        }

        private void grow(int minCapacity) {
            int oldCapacity = elementData.length;
            int newCapacity = oldCapacity + (oldCapacity >> 1);
            if (newCapacity - minCapacity < 0) {
                newCapacity = minCapacity;
            }
            if (newCapacity - MAX_ARRAY_SIZE > 0) {
                if (minCapacity < 0) {
                    throw new OutOfMemoryError();
                }
                newCapacity = (minCapacity > MAX_ARRAY_SIZE) ? Integer.MAX_VALUE : MAX_ARRAY_SIZE;
            }
            elementData = Arrays.copyOf(elementData, newCapacity);
        }

    }

}
