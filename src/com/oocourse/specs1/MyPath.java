package com.oocourse.specs1;

import com.oocourse.specs1.models.Path;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;

public class MyPath implements Path {

    private ArrayList<Integer> list;

    public MyPath(int[] nodeList) {
        list = new ArrayList<>();
        for (int i : nodeList) {
            list.add(i);
        }
        //list = new ArrayList<Integer>(Arrays.asList(nodeList));
    }
    // Iterable<Integer>和Comparable<Path>接口的规格请参阅JDK
    //@ public instance model non_null int[] nodes;

    //@ ensures \result == nodes.length;
    public /*@pure@*/int size() {
        return list.size();
    }

    /*@ requires index >= 0 && index < size();
      @ assignable \nothing;
      @ ensures \result == nodes[index];
      @*/
    public /*@pure@*/ int getNode(int index) {
        if (index < 0 || index >= list.size()) {
            throw new IndexOutOfBoundsException();
        }
        return list.get(index);
    }

    //@ ensures \result == (\exists int i; 0 <= i && i < nodes.length; nodes[i] == node);
    public /*@pure@*/ boolean containsNode(int node) {
        return list.contains(node);
    }

    /*@ ensures \result == (\num_of int i, j; 0 <= i && i < j && j < nodes.length;
                             nodes[i] != nodes[j]);
      @*/
    public /*pure*/ int getDistinctNodeCount() {
        HashSet<Integer> s = new HashSet<>(list);
        return s.size();
    }

    /*@ also
      @ public normal_behavior
      @ requires obj != null && obj instanceof Path;
      @ assignable \nothing;
      @ ensures \result == ((Path) obj).nodes.length == nodes.length) &&
      @                      (\forall int i; 0 <= i && i < nodes.length; nodes[i] == ((Path) obj).nodes[i]);
      @ also
      @ public normal_behavior
      @ requires obj == null || !(obj instanceof Path);
      @ assignable \nothing;
      @ ensures \result == false;
      @*/
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

    //@ ensures \result == (nodes.length >= 2);
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
                return list.get(i) - o.getNode(i);
            }
        }
        return list.size() - o.size();
    }
}
