package no.uib.ii.algo.st8.tests;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Random;
import java.util.Set;

import no.uib.ii.algo.st8.util.InducedSubgraph;
import no.uib.ii.algo.st8.util.NChooseKIterator;
import no.uib.ii.algo.st8.util.Neighbors;
import android.util.SparseIntArray;

public class GraphGenerator {
	public static final Random RANDOM = new Random();

	public static TestGraph clique(int n) {
		TestGraph c = new TestGraph();
		for (int i = 0; i < n; i++) {
			c.addVertex(i);
		}
		for (int i = 0; i < n; i++) {
			for (int j = i + 1; j < n; j++) {
				c.addEdge(i, j);
			}
		}
		return c;
	}

	public static TestGraph star(int n){
		TestGraph g = new TestGraph();
		g.addVertex(0);
		for(int i = 1; i<n; i++){
			g.addVertex(i);
			g.addEdge(0, i);
		}
		return g;
	}
	public static TestGraph path(int n) {
		TestGraph g = new TestGraph();
		g.addVertex(0);
		for (int i = 1; i < n; i++) {
			g.addVertex(i);
			g.addEdge(i - 1, i);
		}
		return g;
	}

	public static TestGraph cycle(int n) {
		TestGraph g = new TestGraph();
		g.addVertex(0);
		for (int i = 1; i < n; i++) {
			g.addVertex(i);
			g.addEdge(i - 1, i);
		}
		g.addEdge(n - 1, 0);
		return g;
	}

	public static TestGraph random(int n, float pEdge) {
		TestGraph g = new TestGraph();
		for (int i = 0; i < n; i++) {
			g.addVertex(i);
		}

		for (int i = 0; i < n; i++) {
			for (int j = i + 1; j < n; j++) {
				if (RANDOM.nextFloat() <= pEdge) {
					g.addEdge(i, j);
				}
			}
		}

		return g;
	}

	public static TestGraph randP5Free(int n){
		TestGraph g = new TestGraph();
		for(int i = 0; i<n; i++){
			g.addVertex(i);
		}
		for(int i = 0; i<n-1; i++){
			g.addEdge(i, n-1);
		}
		int iterations = n*n*10;
		for(int k = 0; k<iterations; k++){
			int i = RANDOM.nextInt(n);
			int j = RANDOM.nextInt(n);
			if(i == j)
				continue;

			if(g.containsEdge(i, j)){
				g.removeEdge(i, j);
				if(containsP5uv(g,i,j)){
					g.addEdge(i, j);
				}
			}else {
				g.addEdge(i, j);
				if(containsUVP5(g,i,j)){
					g.removeEdge(i, j);
				}
			}
		}
		return g;

	}




	/**
	 * Check if contains p5 of the form uvwxy given either a valid u or a valid v
	 * @param g
	 * @param u
	 * @param v
	 * @return true if contains p5, false otherwise
	 */
	public static boolean containsP5uv(TestGraph g, Integer u, Integer v){
		if(containsP5v(g, u) || containsP5v(g, v) || containsP5u(g,v) || containsP5u(g,u))
			return true;
		else
			return false;
	}

	/**
	 * Find P5 on the form uvwxy given v
	 * @param g
	 * @param v1
	 * @param v2
	 * @return
	 */
	public static boolean containsP5v(TestGraph g, Integer v){
		Set<Integer> Nv = Neighbors.openNeighborhood(g, v);
		for(Integer u : Nv){
			Set<Integer> Nu = Neighbors.openNeighborhood(g, u);
			Set<Integer> GminNvNu = new HashSet<Integer>(g.vertexSet());
			GminNvNu.removeAll(Nu); GminNvNu.removeAll(Nv);
			List<HashSet<Integer>> C = listComponents(g, GminNvNu);
			Map<Integer, Integer> compMap = componentMapping(g, GminNvNu);
			Integer c[] = new Integer[C.size()];
			for(int i = 0; i<C.size(); i++){
				c[i] = 0;
			}
			List<Integer> L = new ArrayList<Integer>();

			Set<Integer> NaB = new HashSet<Integer>(Nv);
			NaB.removeAll(Nu); NaB.remove(u);
			for(Integer b : NaB ){
				Set<Integer> NbBp = new HashSet<Integer>(Neighbors.openNeighborhood(g, b));
				NbBp.retainAll(GminNvNu);
				for(Integer tmpc : NbBp){
					int j = compMap.get(tmpc);
					c[j]++;
					if(c[j] == 1)
						L.add(j);
				}
				List<Integer> Ldone = new ArrayList<Integer>();
				for(Integer j : L){
					if(c[j] < C.get(j).size()){
						return true;
					}
					c[j] = 0;
					Ldone.add(j);
				}
				L.removeAll(Ldone);
			}
		}


		return false;
	}

	/**
	 * Determine if the graph contains a p5 involving edge (v1,v2)
	 * @param g
	 * @param v1
	 * @param v2
	 * @return true if graph contains p5 including v1 and v2, false if not
	 */
	private static boolean containsUVP5(TestGraph g, Integer v1, Integer v2){
		if(vuP5free(g,v1,v2) && !containsMiddleP5(g, v1, v2)){
			return false;
		}
		else{
			return true;
		}
	}

	/**
	 * Executes containsMiddle on both directions of v1 v2
	 * @param g
	 * @param v1
	 * @param v2
	 * @return
	 */
	private static boolean containsMiddleP5(TestGraph g, Integer v1, Integer v2){
		if(!containsMiddleP5unFlipped(g, v1, v2) && !containsMiddleP5unFlipped(g, v2, v1))
			return false;
		return true;
	}

	/**
	 * Test if graph contains a p5 of the form uvwxy given the edge wx in time O(nm)
	 * @param g
	 * @param v1
	 * @param v2
	 * @return true if contains specified p5, false otherwise
	 */
	private static boolean containsMiddleP5unFlipped(TestGraph g, Integer v1, Integer v2){
		if(!g.containsEdge(v1, v2))
			return false;
		Integer w = v1;
		Integer x = v2;
		Set<Integer> Nx = Neighbors.openNeighborhood(g, x);
		Set<Integer> NxminNw = Neighbors.openNeighborhood(g, x);
		Set<Integer> Nw = Neighbors.openNeighborhood(g, w);
		NxminNw.removeAll(Nw); NxminNw.remove(w);
		for(Integer y : NxminNw){
			Set<Integer> Ny = Neighbors.openNeighborhood(g, y);
			Set<Integer> B = new HashSet<Integer>(g.vertexSet());
			B.removeAll(Ny);
			B.remove(y);
			Set<Integer> Bp = new HashSet<Integer>(B);
			Bp.removeAll(Nx);
			Bp.remove(w);
			List<HashSet<Integer>> C = listComponents(g, Bp);
			//			System.out.println(w + " " + x + " " + y + " " + C);
			Map<Integer, Integer> compMap = componentMapping(g, Bp);
			Integer c[] = new Integer[C.size()];
			for(int i = 0; i<C.size(); i++){
				c[i] = 0;
			}
			List<Integer> L = new ArrayList<Integer>();

			Set<Integer> NbBp = new HashSet<Integer>(Neighbors.openNeighborhood(g, w));
			NbBp.retainAll(Bp);
			for(Integer tmpc : NbBp){
				int j = compMap.get(tmpc);
				c[j]++;
				if(c[j] == 1)
					L.add(j);
			}
			for(Integer j : L){
				if(c[j] < C.get(j).size()){
					return true;
				}
			}
		}
		return false;

	}

	private static boolean vuP5free(TestGraph g, Integer v1, Integer v2){
		if(vuP5freeunFlipped(g,v1,v2) && vuP5freeunFlipped(g,v2,v1))
			return true;
		else
			return false;

	}

	/**
	 * Method to determine if graph contains a p5 with (v1,v2) as edge uv in uvwxy in time O(m)
	 * @param g Graph to test in
	 * @return true if P5-free, false otherwise
	 */
	private static boolean vuP5freeunFlipped(TestGraph g, Integer v1, Integer v2){
		Integer v = v1;
		Integer u = v2;
		Set<Integer> Nv = Neighbors.openNeighborhood(g, v);
		Set<Integer> B = new HashSet<Integer>(g.vertexSet());
		B.removeAll(Nv);
		Set<Integer> Nu = Neighbors.openNeighborhood(g, u);
		Set<Integer> Bp = new HashSet<Integer>(B);
		Bp.removeAll(Nu);
		List<HashSet<Integer>> C = listComponents(g, Bp);
		Map<Integer, Integer> compMap = componentMapping(g, Bp);
		Integer c[] = new Integer[C.size()];
		for(int i = 0; i<C.size(); i++){
			c[i] = 0;
		}
		List<Integer> L = new ArrayList<Integer>();

		Set<Integer> NaB = new HashSet<Integer>(Nu);
		NaB.retainAll(B);
		for(Integer b : NaB ){
			Set<Integer> NbBp = new HashSet<Integer>(Neighbors.openNeighborhood(g, b));
			NbBp.retainAll(Bp);
			for(Integer tmpc : NbBp){
				int j = compMap.get(tmpc);
				c[j]++;
				if(c[j] == 1)
					L.add(j);
			}
			List<Integer> Ldone = new ArrayList<Integer>();
			for(Integer j : L){
				if(c[j] < C.get(j).size()){
					return false;
				}
				c[j] = 0;
				Ldone.add(j);
			}
			L.removeAll(Ldone);
		}
		return true;
	}

	/**
	 * Method to find and return an induced P5 in a given graph
	 * @param g Graph to test in
	 * @return empty list if P5-free, otherwise returns a P5.
	 */
	public static List<Integer> findP5(TestGraph g){
		List<Integer> retList = new ArrayList<Integer>();
		for(Integer v : g.vertexSet()){
			for(Integer e : g.edgesOf(v)){
				int u = Neighbors.opposite(g, v, e);
				Set<Integer> Nv = Neighbors.openNeighborhood(g, v);
				Set<Integer> B = new HashSet<Integer>(g.vertexSet());
				B.removeAll(Nv);
				Set<Integer> Nu = Neighbors.openNeighborhood(g, u);
				Set<Integer> Bp = new HashSet<Integer>(B);
				Bp.removeAll(Nu);
				List<HashSet<Integer>> C = listComponents(g, Bp);
				Map<Integer, Integer> compMap = componentMapping(g, Bp);
				Integer c[] = new Integer[C.size()];
				for(int i = 0; i<C.size(); i++){
					c[i] = 0;
				}
				List<Integer> L = new ArrayList<Integer>();

				Set<Integer> NaB = new HashSet<Integer>(Nu);
				NaB.retainAll(B);
				for(Integer b : NaB ){
					Set<Integer> NbBp = new HashSet<Integer>(Neighbors.openNeighborhood(g, b));
					NbBp.retainAll(Bp);
					for(Integer tmpc : NbBp){
						int j = compMap.get(tmpc);
						c[j]++;
						if(c[j] == 1)
							L.add(j);
					}
					List<Integer> Ldone = new ArrayList<Integer>();
					for(Integer j : L){
						if(c[j] < C.get(j).size()){
							Set<Integer> X = Neighbors.openNeighborhood(g, b);
							X.retainAll(C.get(j));
							Set<Integer> Y = new HashSet<Integer>(C.get(j));
							Y.removeAll(X);
							for(Integer x : X){
								for(Integer xEdge : g.edgesOf(x)){
									int xEdgeOpposite = Neighbors.opposite(g, x, xEdge);
									if(Y.contains(xEdgeOpposite)){
										retList.add(v);
										retList.add(u);
										retList.add(b);
										retList.add(x);
										retList.add(xEdgeOpposite);
										return retList;
									}

								}
							}
						}
						c[j] = 0;
						Ldone.add(j);
					}
					L.removeAll(Ldone);
				}
			}
		}
		return retList;
	}

	/**
	 * Find P5 of the form uvwxy given u
	 * @param g Graph to test in
	 * @return false if P5-free, otherwise true.
	 */
	public static boolean containsP5u(TestGraph g, Integer v){
		Set<Integer> Nv = Neighbors.openNeighborhood(g, v);
		Set<Integer> B = new HashSet<Integer>(g.vertexSet());
		B.removeAll(Nv);
		for(Integer u : Nv){
			Set<Integer> Nu = Neighbors.openNeighborhood(g, u);
			Set<Integer> Bp = new HashSet<Integer>(B);
			Bp.removeAll(Nu);
			List<HashSet<Integer>> C = listComponents(g, Bp);
			Map<Integer, Integer> compMap = componentMapping(g, Bp);
			Integer c[] = new Integer[C.size()];
			for(int i = 0; i<C.size(); i++){
				c[i] = 0;
			}
			List<Integer> L = new ArrayList<Integer>();

			Set<Integer> NaB = new HashSet<Integer>(Nu);
			NaB.retainAll(B);
			for(Integer b : NaB ){
				Set<Integer> NbBp = new HashSet<Integer>(Neighbors.openNeighborhood(g, b));
				NbBp.retainAll(Bp);
				for(Integer tmpc : NbBp){
					int j = compMap.get(tmpc);
					c[j]++;
					if(c[j] == 1)
						L.add(j);
				}
				List<Integer> Ldone = new ArrayList<Integer>();
				for(Integer j : L){
					if(c[j] < C.get(j).size()){
						return true;
					}
					c[j] = 0;
					Ldone.add(j);
				}
				L.removeAll(Ldone);
			}
		}
		return false;
	}

	public static Map<Integer, Integer> componentMapping(TestGraph g, Set<Integer> Bp){
		Map<Integer, Integer> comp = new HashMap<Integer,Integer>();
		int currComp = 0;
		for(Integer i : Bp){
			comp.put(i, -1);
		}
		for(Integer i : Bp){
			if(comp.get(i) != -1)
				continue;
			Queue<Integer> q = new LinkedList<Integer>();
			q.add(i);
			comp.put(i, currComp);
			while(!q.isEmpty()){
				Integer k = q.poll();

				for(int e : g.edgesOf(k)){
					int kOp = Neighbors.opposite(g, k, e);
					if(Bp.contains(kOp) && comp.get(kOp) == -1){
						comp.put(kOp, currComp);
						q.add(kOp);
					}
				}
			}
			currComp++;
		}
		return comp;

	}

	/**
	 * List components within G[Bp]
	 * @param g graph
	 * @param Bp vertex set to list components in 
	 * @return list of components
	 */
	public static List<HashSet<Integer>> listComponents(TestGraph g, Set<Integer> Bp){
		Map<Integer, Integer> comp = new HashMap<Integer,Integer>();
		int currComp = 0;
		for(Integer i : Bp){
			comp.put(i, -1);
		}
		for(Integer i : Bp){
			if(comp.get(i) != -1)
				continue;
			Queue<Integer> q = new LinkedList<Integer>();
			q.add(i);
			comp.put(i, currComp);
			while(!q.isEmpty()){
				Integer k = q.poll();
				for(int e : g.edgesOf(k)){
					int kOp = Neighbors.opposite(g, k, e);
					if(Bp.contains(kOp) && comp.get(kOp) == -1){
						comp.put(kOp, currComp);
						q.add(kOp);
					}
				}
			}
			currComp++;
		}
		List<HashSet<Integer>> C = new ArrayList<HashSet<Integer>>();
		for(int i = 0; i<currComp; i++)
			C.add(new HashSet<Integer>());
		for(Integer key : comp.keySet()){
			C.get(comp.get(key)).add(key);
		}
		return C;

	}


	/**
	 * Encodes a graph as a long, where the binary representation of the long is 
	 * the lower diagonal of the adjecency matrix.
	 * Encoded in the format 1"binary representation", where 1 is a delimiter.
	 * @param graph graph to convert
	 * @return a long that in binary represents the graph.
	 */
	public static BigInteger graphToBigInt(TestGraph graph){
		int n = graph.vertexSet().size();
		if(n == 0)
			return BigInteger.ZERO;
		if(n == 1)
			return BigInteger.ONE;
		BigInteger longGraph = new BigInteger("2");
		for(int i = 0; i<n; i++){
			Set<Integer> iNeigh = Neighbors.openNeighborhood(graph, i);
			for(int j = 0; j<i; j++){
				if(iNeigh.contains(j)){
					longGraph = BigInteger.ONE.or(longGraph); 
				}
				longGraph = longGraph.shiftLeft(1);// << 1;

			}
		}
		longGraph = longGraph.shiftRight(1);//longGraph >> 1;
		return longGraph;

	}

	/**
	 * Takes a list of graphs represented as longs and prints them to a file
	 * @param graphs list of graphs to print
	 * @param filename name of file to print to
	 */
	public static void writeBigIntGraphsToFile(Collection<BigInteger> graphs, String filename){
		try{
			PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(filename)));
			for(BigInteger l : graphs){
				out.println(l.toString());
			}
			out.close();
		} catch (Exception e){
			e.printStackTrace();
		}
	}

	public static boolean containsP5(TestGraph g){
		for(Integer v : g.vertexSet()){
			for(Integer e : g.edgesOf(v)){
				int u = Neighbors.opposite(g, v, e);
				Set<Integer> Nv = Neighbors.openNeighborhood(g, v);
				Set<Integer> B = new HashSet<Integer>(g.vertexSet());
				B.removeAll(Nv);
				Set<Integer> Nu = Neighbors.openNeighborhood(g, u);
				Set<Integer> Bp = new HashSet<Integer>(B);
				Bp.removeAll(Nu);
				List<HashSet<Integer>> C = listComponents(g, Bp);
				Map<Integer, Integer> compMap = componentMapping(g, Bp);
				Integer c[] = new Integer[C.size()];
				for(int i = 0; i<C.size(); i++){
					c[i] = 0;
				}
				List<Integer> L = new ArrayList<Integer>();

				Set<Integer> NaB = new HashSet<Integer>(Nu);
				NaB.retainAll(B);
				for(Integer b : NaB ){
					Set<Integer> NbBp = new HashSet<Integer>(Neighbors.openNeighborhood(g, b));
					NbBp.retainAll(Bp);
					for(Integer tmpc : NbBp){
						int j = compMap.get(tmpc);
						c[j]++;
						if(c[j] == 1)
							L.add(j);
					}
					List<Integer> Ldone = new ArrayList<Integer>();
					for(Integer j : L){
						if(c[j] < C.get(j).size()){
							return true;
						}
						c[j] = 0;
						Ldone.add(j);
					}
					L.removeAll(Ldone);
				}
			}
		}
		return false;
	}



	public static TestGraph disjointUnion(TestGraph g1, TestGraph g2) {
		TestGraph g = new TestGraph();
		SparseIntArray m1 = new SparseIntArray();
		SparseIntArray m2 = new SparseIntArray();
		int counter = 1;
		for (Integer v : g1.vertexSet()) {
			m1.put(v, counter);
			g.addVertex(counter);
			counter++;
		}
		for (Integer v : g2.vertexSet()) {
			m2.put(v, counter);
			g.addVertex(counter);
			counter++;
		}
		for (Integer edge : g1.edgeSet()) {
			Integer s = g1.getEdgeSource(edge);
			Integer t = g1.getEdgeTarget(edge);

			g.addEdge(m1.get(s), m1.get(t));
		}
		for (Integer edge : g2.edgeSet()) {
			Integer s = g2.getEdgeSource(edge);
			Integer t = g2.getEdgeTarget(edge);

			g.addEdge(m2.get(s), m2.get(t));
		}
		return g;
	}

	public static void genRandP5ToFile(int size, int number, String fileName){
		List<BigInteger> grps = new ArrayList<BigInteger>();
		int k = size;
		for(int i = 0; i<number; i++){
			//			System.out.println(i);
			TestGraph g = GraphGenerator.randP5Free(k);
			grps.add(graphToBigInt(g));
		}
		writeBigIntGraphsToFile(grps, fileName);
	}
	public static void main(String[] args){
		Set<BigInteger> grps = new HashSet<BigInteger>();
		int k = 12;
		while(grps.size() < 10000){
			TestGraph g = GraphGenerator.random(k, 0.5f);
//			g.DotGraph();
			if(!containsP5(g) && listComponents(g,g.vertexSet()).size() == 1){
				System.out.println(grps.size());
				grps.add(graphToBigInt(g));
			}
		}
		writeBigIntGraphsToFile(grps, "uniform12Graphs.txt");
	}

}
