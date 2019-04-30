package com.oocourse.specs1;

import com.oocourse.specs1.models.Path;
import com.oocourse.specs1.models.PathContainer;
import com.oocourse.specs1.models.PathIdNotFoundException;
import com.oocourse.specs1.models.PathNotFoundException;

import java.util.TreeMap;

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

    public /*@pure@*/int size() {
        return plist.size();
    }

    public /*@pure@*/ boolean containsPath(Path path) {
        if (path == null) {
            throw new NullPointerException();
        }
        return plist.containsKey(path);
    }

    public /*@pure@*/ boolean containsPathId(int pathId) {
        if (pathId <= 0 || pathId > 3000) {
            return false;
        }
        return pidList[pathId] != null;
    }

    public /*@pure@*/ Path getPathById(int pathId)
            throws PathIdNotFoundException {
        if (!containsPathId(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }
        return pidList[pathId];
    }

    public /*@pure@*/ int getPathId(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }
        return plist.get(path);
    }

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
                    nodes.put(i, nodes.get(i) + 1);
                } else {
                    nodes.put(i, 1);
                }
            }
            return id++;
        }
    }

    public int removePath(Path path) throws PathNotFoundException {
        if (path == null || !path.isValid() || !containsPath(path)) {
            throw new PathNotFoundException(path);
        }
        int ret = plist.get(path);
        plist.remove(path);
        pidList[ret] = null;
        for (int i : path) {
            int tmp = nodes.get(i);
            nodes.put(i, tmp - 1);
            if (tmp == 1) {
                nodes.remove(i);
            }
        }
        return ret;
    }

    public void removePathById(int pathId) throws PathIdNotFoundException {
        if (!containsPathId(pathId)) {
            throw new PathIdNotFoundException(pathId);
        }
        Path path = pidList[pathId];
        pidList[pathId] = null;
        plist.remove(path);
        for (int i : path) {
            int tmp = nodes.get(i);
            nodes.put(i, tmp - 1);
            if (tmp == 1) {
                nodes.remove(i);
            }
        }
    }

    public /*@pure@*/int getDistinctNodeCount() { //在容器全局范围内查找不同的节点数
        return nodes.size();
    }
}
