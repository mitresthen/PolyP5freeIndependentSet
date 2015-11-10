package no.uib.ii.algo.st8.algorithms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import no.uib.ii.algo.st8.util.Neighbors;

import org.jgrapht.graph.SimpleGraph;

/**
 * Minimal triangulation algorithm based on
 * "Maximum Cardinality Search for Computing Minimal Triangulations of Graphs*"
 * by Anne Berry, Jean R. S. Blair and Pinar Heggernes.
 * 
 * @author Håvard Haug
 * 
 * @param <V>
 * @param <E>
 */
public class MinimalTriangulation<V, E> extends Algorithm<V, E, Set<E>> {

	//Mappings to create some ordering of the vertices and easy lookup.
	public Map<V,Integer> peoMap;
	public List<List<V>> peoOrders;
	/**
	 * List of maximal cliques contained in the minimal triangulation.
	 * This is bound to be of size at most n as the graph created
	 * by the minimal triangulation is a chordal graph.
	 */
	public List<Set<V>> maximalCliques;
	
	/**
	 * Constructor that initializes everything necessary to run minimal triangulation
	 * @param graph a graph to triangulate
	 */
	public MinimalTriangulation(SimpleGraph<V, E> graph) {
		super(graph);
	}

	/**
	 * Run the method to create a minimal triangulation 
	 * and get the set of edges that was added as a return value.
	 */
	public Set<E> execute() {
		return minimalFill();
	}

	/**
	 * Method to calculate the fill-set of a given graph, 
	 * use the fill-set to fill in the graph and get a chordal graph based on the
	 * given minimal triangulation.
	 * It also calculates the set of maximal cliques contained in the minimal triangulation
	 * and returns the fill-set.
	 * @return the fill-set (set of edges to add such that a minimal triangulation is achieved)
	 */
	public Set<E> minimalFill() {
		peoMap = new HashMap<V,Integer>();
		peoOrders = new ArrayList<List<V>>();
		maximalCliques = new ArrayList<Set<V>>();
		// SimpleGraph<V, E> filled = new SimpleGraph<V, E>(graph.getEdgeFactory());
		Set<E> FillSet = new HashSet<E>();
		Map<V, Integer> w = new HashMap<V, Integer>();
		for (V v : graph.vertexSet()) {
			w.put(v, 0);
		}
		int n = graph.vertexSet().size();
		Map<V, Integer> numbered = new HashMap<V, Integer>();
		List<V> unNumbered = new ArrayList<V>();
		for (V v : graph.vertexSet()) {
			unNumbered.add(v);
		}
		int currComp = 0;
		peoOrders.add(new ArrayList<V>());
		Map<V, HashSet<V>> adjList = new HashMap<V, HashSet<V>>();
		for (int i = n; i > 0; i--) {
			V maxV = unNumbered.get(0);
			for (V v : unNumbered) {
				if (w.get(v) > w.get(maxV))
					maxV = v;
			}
			if(i != n && w.get(maxV) == 0){
				currComp++;
				peoOrders.add(new ArrayList<V>());
			}
			MinimumBottleneckPaths<V, E> minBot = new MinimumBottleneckPaths<V, E>(graph);
			Set<V> S = minBot.mbp(unNumbered, maxV, w);
			adjList.put(maxV, new HashSet<V>(S));
			for (V v : S) {
				w.put(v, w.get(v) + 1);
			}
			numbered.put(maxV, i);
			unNumbered.remove(maxV);
			peoMap.put(maxV, i);
			peoOrders.get(currComp).add(maxV);
		}
		for (V v : adjList.keySet()) {
			for (V u : adjList.get(v)) {
				if (!graph.containsEdge(v, u))
					FillSet.add(graph.addEdge(v, u)); //Add edge to graph and get id of edge to put in fillset
			}
		}
		List<List<V>> revPeo = new ArrayList<List<V>>();
		for(int j = 0; j < peoOrders.size(); j++){
			revPeo.add(new ArrayList<V>());
			for (int i = peoOrders.get(j).size()-1; i >= 0 ; i--) {
				revPeo.get(j).add(peoOrders.get(j).get(i));
			}
		}
		peoOrders = revPeo;
		for(int i = 0; i<peoOrders.size(); i++){
			if(!peoOrders.get(i).isEmpty()){
				Set<V> nextSet = new HashSet<V>();
				nextSet.add(peoOrders.get(i).get(0));
				nextSet.addAll(madj(peoOrders.get(i).get(0)));
				maximalCliques.add(new HashSet<V>(nextSet));
				for(int j = 1; j< peoOrders.get(i).size(); j++){
					nextSet = new HashSet<V>();
					Set<V> prevSet = new HashSet<V>();
					V prev = peoOrders.get(i).get(j-1);
					V vi = peoOrders.get(i).get(j);
					nextSet.add(vi);
					nextSet.addAll(madj(vi));
					prevSet.add(prev);
					prevSet.addAll(madj(prev));
					if(prevSet.size() <= nextSet.size())
						maximalCliques.add(nextSet);
				}
			}
		}

		return FillSet;

	}

	/**
	 * Method that finds the set of vertices that are 1. neighbours of v
	 * and 2. occur later in the perfect elimination ordering.
	 * @param v vertex to find madj for
	 * @return set of vertices according to descriptioni of method
	 */
	private Set<V> madj(V v){
		Set<V> adj = new HashSet<V>();
		for(V v2 : Neighbors.openNeighborhood(graph, v)){
			if(peoMap.get(v) < peoMap.get(v2))
				adj.add(v2);
		}
		return adj;
	}

}
