package com.oocourse.specs1;

import com.oocourse.specs1.models.Path;
import com.oocourse.specs1.models.PathContainer;
import com.oocourse.specs1.models.PathIdNotFoundException;
import com.oocourse.specs1.models.PathNotFoundException;

import java.util.*;

public class MyPathContainer implements PathContainer {

    private static int id = 1;
    private TreeMap<Path, Integer> plist;
    private Path[] pidList;
    private TreeMap<Integer, Integer> nodes;

    public MyPathContainer() {
        plist = new TreeMap<>();
        pidList = new Path[3005];
        nodes = new TreeMap<>();
    }
    //@ public instance model non_null Path[] pList;
    //@ public instance model non_null int[] pidList;

    //@ ensures \result == pList.length;
    public /*@pure@*/int size() {
        return plist.size();
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
        return plist.containsKey(path);
    }

    /*@ ensures \result == (\exists int i; 0 <= i && i < pidList.length;
      @                      pidList[i] == pathId);
      @*/
    public /*@pure@*/ boolean containsPathId(int pathId) {
        if (pathId <= 0 || pathId > 3000) {
            return false;
        }
        return pidList[pathId] != null;
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
        return pidList[pathId];
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
        return plist.get(path);
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
            return plist.get(path);
        } else {
            plist.put(path, id);
            pidList[id] = path;
            for (int i : path) {
                if (nodes.containsKey(i)) {
                    nodes.put(i,nodes.get(i)+1);
                }
                else {
                    nodes.put(i,1);
                }
            }
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
        int ret = plist.get(path);
        plist.remove(path);
        pidList[ret] = null;
        for (int i : path) {
            int tmp = nodes.get(i);
            nodes.put(i,tmp-1);
            if (tmp == 1) {
                nodes.remove(i);
            }
        }
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
        Path path = pidList[pathId];
        pidList[pathId] = null;
        plist.remove(path);
        for (int i : path) {
            int tmp = nodes.get(i);
            nodes.put(i,tmp-1);
            if (tmp == 1) {
                nodes.remove(i);
            }
        }
    }

    /*@ ensures \result == (\num_of int[] nlist;
           (\forall int i,j; 0 <= i && i < pList.length && 0 <= j && j < pList[i].size();
           (\exists int k; 0 <= k && k < nlist.length; nlist[k] == pList[i].getNode(j)));
           (\forall int m, n; 0 <= m && m < n && n < nlist.length; nlist[m] != nlist[n]));
      @*/
    public /*@pure@*/int getDistinctNodeCount() { //在容器全局范围内查找不同的节点数
        return nodes.size();
    }
}
