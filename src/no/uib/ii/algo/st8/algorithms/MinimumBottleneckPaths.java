package no.uib.ii.algo.st8.algorithms;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;

import no.uib.ii.algo.st8.util.Neighbors;

import org.jgrapht.graph.SimpleGraph;

/**
 * Node weighted minimal bottleneck path
 * Finds all paths from an unnumbered node to other unnumbered nodes that go through
 * unnumbered nodes of weight lower than that of the destination node
 * 
 * @author haavard
 * 
 */
public class MinimumBottleneckPaths<V, E> {

  SimpleGraph<V, E> graph;

  /**
   * constructor to initialize all variables
   * @param graph the graph to run mbp on
   */
  public MinimumBottleneckPaths(SimpleGraph<V, E> graph) {
    this.graph = graph;
    // TODO Auto-generated constructor stub
  }

  /**
   * Method to find the set of all nodes that can be reached by the mbp criteria
   * @param unNumbered list of vertices that can be used as part of a path or a destination node
   * @param vertex the starting vertex
   * @param w weights of all vertices in the graph. 
   * @return set of nodes that can be reached from vertex by mbp
   */
  public Set<V> mbp(Collection<V> unNumbered, V vertex, Map<V, Integer> w) {
    Set<V> S = new HashSet<V>();
    Queue<Pair<V>> q = new PriorityQueue<Pair<V>>();
    Map<V, Integer> d = new HashMap<V, Integer>();
    Map<V, Integer> o = new HashMap<V, Integer>();
    for (V v : unNumbered) {
      d.put(v, Integer.MAX_VALUE);
      o.put(v, Integer.MAX_VALUE);
    }
    Set<V> onV = Neighbors.openNeighborhood(graph, vertex);
    for (V v : onV) {
      if (unNumbered.contains(v)) {
        S.add(v);
      }
    }
    q.add(new Pair<V>(vertex, 0));
    while (!q.isEmpty()) {
      Pair<V> xt = q.poll();
      if (!unNumbered.contains(xt.x) || o.get(xt.x) <= xt.t) {
        continue;
      }
      o.put(xt.x, xt.t);
      if (!xt.x.equals(vertex))
        d.put(xt.x, Math.max(xt.t, w.get(xt.x)));
      else
        d.put(xt.x, xt.t);
      for (V v : Neighbors.openNeighborhood(graph, xt.x)) {
        q.add(new Pair<V>(v, d.get(xt.x)));
      }
    }
    for (V v : o.keySet()) {
      if (w.get(v) > o.get(v))
        S.add(v);
    }
    S.remove(vertex);
    return S;

  }

  private class Pair<V> implements Comparable<Pair<V>> {
    public V x;
    public Integer t;

    public Pair(V v, Integer i) {
      x = v;
      t = i;
    }

    @Override
    public int compareTo(Pair<V> another) {
      return t - another.t;
    }
  }

}
