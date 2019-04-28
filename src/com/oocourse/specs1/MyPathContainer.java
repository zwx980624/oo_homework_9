package com.oocourse.specs1;

import com.oocourse.specs1.models.Path;
import com.oocourse.specs1.models.PathContainer;
import com.oocourse.specs1.models.PathIdNotFoundException;
import com.oocourse.specs1.models.PathNotFoundException;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

public class MyPathContainer implements PathContainer {

    private static int id = 1;
    private ArrayList<Path> pList;
    private ArrayList<Integer> pidList;

    public MyPathContainer() {
        pList = new ArrayList<>();
        pidList = new ArrayList<>();
    }
    //@ public instance model non_null Path[] pList;
    //@ public instance model non_null int[] pidList;

    //@ ensures \result == pList.length;
    public /*@pure@*/int size() {
        return pList.size();
    }

    /*@ requires path != null;
      @ assignable \nothing;
      @ ensures \result == (\exists int i; 0 <= i && i < pList.length;
      @                     pList[i].equals(path));
      @*/
    public /*@pure@*/ boolean containsPath(Path path) {
        if (path == null) {
            throw new NullPointerException();
        }
        for (Path p : pList) {
            if (p.equals(path)) {
                return true;
            }
        }
        return false;
    }

    /*@ ensures \result == (\exists int i; 0 <= i && i < pidList.length;
      @                      pidList[i] == pathId);
      @*/
    public /*@pure@*/ boolean containsPathId(int pathId) {
        return pidList.contains(pathId);
    }

    /*@ public normal_behavior
      @ requires containsPathId(pathId);
      @ assignable \nothing;
      @ ensures (pidList.length == pList.length)&&(\exists int i; 0 <= i && i < pList.length; pidList[i] == pathId && \result == pList[i]);
      @ also
      @ public exceptional_behavior
      @ requires !containsPathId(pathId);
      @ assignable \nothing;
      @ signals_only PathIdNotFoundException;
      @*/
    public /*@pure@*/ Path getPathById(int pathId) throws PathIdNotFoundException {
        if (!containsPathId(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }
        return pList.get(pidList.indexOf(pathId));
    }

    /*@ public normal_behavior
      @ requires path != null && path.isValid() && containsPath(path);
      @ assignable \nothing;
      @ ensures (pidList.length == pList.length) && (\exists int i; 0 <= i && i < pList.length; pList[i].equals(path) && pidList[i] == \result);
      @ also
      @ public exceptional_behavior
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) !path.isValid();
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }
        for (int i = 0; i < pList.size(); i++) {
            if (pList.get(i).equals(path)) {
                return pidList.get(i);
            }
        }
        return 0; // cannot be executed
    }

    /*@ normal_behavior
      @ requires path != null && path.isValid();
      @ assignable pList, pidList;
      @ ensures (pidList.length == pList.length);
      @ ensures (\exists int i; 0 <= i && i < pList.length; pList[i] == path &&
      @           \result == pidList[i]);
      @ ensures !\old(containsPath(path)) ==>
      @          pList.length == (\old(pList.length) + 1) &&
      @          pidList.length == (\old(pidList.length) + 1);
      @ ensures (\forall int i; 0 <= i && i < \old(pList.length);
      @          containsPath(\old(pList[i])) && containsPathId(\old(pidList[i])));
      @ also
      @ normal_behavior
      @ requires path == null || path.isValid() == false;
      @ assignable \nothing;
      @ ensures \result == 0;
      @*/
    public int addPath(Path path) {
        if (path == null || !path.isValid()) {
            return 0;
        }
        if (containsPath(path)) {
            try {
                return getPathId(path);
            } catch (PathNotFoundException e) {
                return 0;
            }
        } else {
            pList.add(path);
            pidList.add(id);
            return id++;
        }
    }

    /*@ public normal_behavior
      @ requires path != null && path.isValid() && \old(containsPath(path));
      @ assignable pList, pidList;
      @ ensures containsPath(path) == false;
      @ ensures (pidList.length == pList.length);
      @ ensures (\exists int i; 0 <= i && i < \old(pList.length); \old(pList[i].equals(path)) &&
      @           \result == \old(pidList[i]));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathNotFoundException e) path == null;
      @ signals (PathNotFoundException e) path.isValid()==false;
      @ signals (PathNotFoundException e) !containsPath(path);
      @*/
    public int removePath(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }
        int ret = getPathId(path);
        pList.remove(path);
        pidList.remove((Integer)ret);
        return ret;
    }

    /*@ public normal_behavior
      @ requires \old(containsPathId(pathId));
      @ assignable pList, pidList;
      @ ensures pList.length == pidList.length;
      @ ensures (\forall int i; 0 <= i && i < pidList.length; pidList[i] != pathId);
      @ ensures (\forall int i; 0 <= i && i < pList.length;!pList[i].equals(\old(getPathById(pathId))));
      @ also
      @ public exceptional_behavior
      @ assignable \nothing;
      @ signals (PathIdNotFoundException e) !containsPathId(pathId);
      @*/
    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (!containsPathId(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }
        Path p = getPathById(pathId);
        pidList.remove((Integer)pathId);
        pList.remove(p);
    }

    /*@ ensures \result == (\num_of int[] nlist;
           (\forall int i,j; 0 <= i && i < pList.length && 0 <= j && j < pList[i].size();
           (\exists int k; 0 <= k && k < nlist.length; nlist[k] == pList[i].getNode(j)));
           (\forall int m, n; 0 <= m && m < n && n < nlist.length; nlist[m] != nlist[n]));
      @*/
    public /*@pure@*/int getDistinctNodeCount() { //在容器全局范围内查找不同的节点数
        Set<Integer> s = new HashSet<>();
        for (Path p : pList) {
            for (int j = 0; j < p.size(); ++j) {
                s.add(p.getNode(j));
            }
        }
        return s.size();
    }
}
