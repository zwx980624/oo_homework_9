package com.oocourse.specs1;

import com.oocourse.specs1.models.Path;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.TreeSet;

public class MyPath implements Path {

    private ArrayList<Integer> list;
    private TreeSet<Integer> nodeSet;

    public MyPath(int[] nodeList) {
        list = new ArrayList<>();
        for (int i : nodeList) {
            list.add(i);
        }
        nodeSet = new TreeSet<>(list);
    }

    public /*@pure@*/int size() {
        return list.size();
    }

    public /*@pure@*/ int getNode(int index) {
        if (index < 0 || index >= list.size()) {
            throw new IndexOutOfBoundsException();
        }
        return list.get(index);
    }

    public /*@pure@*/ boolean containsNode(int node) {
        return nodeSet.contains(node);
    }

    public /*pure*/ int getDistinctNodeCount() {
        return nodeSet.size();
    }

    public boolean equals(Object obj) {
        if (!(obj instanceof Path)) {
            return false;
        }
        Path pathobj = (Path) obj;
        if (this.size() != pathobj.size()) {
            return false;
        }
        for (int i = 0; i < this.size(); ++i) {
            if (this.getNode(i) != pathobj.getNode(i)) {
                return false;
            }
        }
        return true;
    }

    public /*@pure@*/ boolean isValid() {
        return list.size() >= 2;
    }

    public Iterator<Integer> iterator() {
        return list.iterator();
    }

    public int compareTo(Path o) {
        if (o == null) {
            throw new NullPointerException();
        }
        int len = Integer.min(o.size(), list.size());
        for (int i = 0; i < len; ++i) {
            if (list.get(i) != o.getNode(i)) {
                return Integer.compare(list.get(i),o.getNode(i));
            }
        }
        return Integer.compare(list.size(), o.size());
    }
}