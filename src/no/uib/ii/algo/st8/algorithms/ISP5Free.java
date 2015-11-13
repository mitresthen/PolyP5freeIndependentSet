package no.uib.ii.algo.st8.algorithms;

import java.io.File;
import java.io.FileNotFoundException;
import java.math.BigInteger;
import java.util.*;

import no.uib.ii.algo.st8.tests.TestGraph;
import no.uib.ii.algo.st8.tests.GraphGenerator;
import no.uib.ii.algo.st8.util.InducedSubgraph;
import no.uib.ii.algo.st8.util.Neighbors;

import org.jgrapht.EdgeFactory;
import org.jgrapht.graph.SimpleGraph;

/**
 * Class to calculate an Independent set of a P5-free graph, and all submethods necessary to achieve this.
 * Everything is based on a paper titled "Independent Set in P5-Free Graphs in Polynomial Time"
 * 
 * @author Havard Haug
 *
 * @param <V> type of vertices
 * @param <E> type of edges
 */
public class ISP5Free<V,E> {

	/**
	 * Graph that was given as input, but with types for edges and nodes converted to int
	 */
	private SimpleGraph<Integer,Integer> P5freeGraph;
	/**
	 * A list of subgraphs made from P5freeGraph by 
	 */
	private List<SimpleGraph<Integer,Integer>> graphI;
	/**
	 * Mapping that provides easy access to the neighbourhood of a vertex
	 */
	private Map<Integer, Set<Integer>> adjGraph;
	private List<V> vOrd;
	private List<Integer> vList;
	private Map<V, Integer> vMap;


	private SimpleGraph<V,E> G;
	/**
	 * number of vertices in P5freeGraph
	 */
	private int n;

	/**
	 * list Pi of all pmcs in the graph
	 */
	public Set<Set<Integer>> comboPI = new HashSet<Set<Integer>>();
	Set<Set<Integer>> firstPI = new HashSet<Set<Integer>>();
	Set<Set<Integer>> secondPI = new HashSet<Set<Integer>>();

	public Map<Integer, Map<Set<Integer>, Map<Set<Integer>, Integer>>> M;

	public Map<Integer, Map<Set<Integer>, Map<Set<Integer>, Integer>>> T1;
	public Map<Integer, Map<Set<Integer>, Map<Set<Integer>, Integer>>> T2;
	/**
	 * variables needed for fast independent set algorithm
	 */
	private SimpleGraph<Integer,Integer> piDelta;
	private Map<Set<Integer>, Integer> piMap;
	private Map<Set<Integer>, Integer> deltaMap;
	private List<Set<Integer>> bigDelta;
	private List<Set<Integer>> PiList;

	int dg0and1count = 0;

	private V lowestDegreeV(SimpleGraph<V,E> G){
		V minDg = null;
		int minDeg = Integer.MAX_VALUE;
		for(V v : G.vertexSet()){
			if(G.degreeOf(v) < minDeg){
				minDg = v;
				minDeg = G.degreeOf(v);
			}
		}
		return minDg;
	}


	//	public ISP5Free(SimpleGraph<V,E> inG, boolean something){
	//		G = (SimpleGraph<V, E>) inG.clone();
	//		while(lowestDegreeV(G) != null && G.degreeOf(lowestDegreeV(G)) < 2){
	//			V v = lowestDegreeV(G);
	//			for(V u : Neighbors.openNeighborhood(G, v)){
	//				G.removeVertex(u);
	//			}
	//			G.removeVertex(v);
	//			dg0and1count++;
	//		}
	//	}

	/**
	 * Constructor that sets up everything necessary to use the methods in this class.
	 * @param G The graph to find an independent set in.
	 */
	public ISP5Free(SimpleGraph<V,E> inG){
		G = (SimpleGraph<V, E>) inG.clone();
		//		while(lowestDegreeV(G) != null && G.degreeOf(lowestDegreeV(G)) < 2){
		//			V v = lowestDegreeV(G);
		//			for(V u : Neighbors.openNeighborhood(G, v)){
		//				G.removeVertex(u);
		//			}
		//			G.removeVertex(v);
		//			dg0and1count++;
		//		}
		//Convert the graph from SimpleGraph<V,E> to SimpleGraph<Int, Int> as the type information
		//Is not important to the algorithm, and this provides much faster lookups and other neat functionality.
		//vOrd associates the vertices with integers that represent them
		//		if(!G.vertexSet().isEmpty()){
		vOrd = new ArrayList<V>(G.vertexSet());
		vMap = new HashMap<V, Integer>();
		adjGraph = new HashMap<Integer, Set<Integer>>();
		graphI = new ArrayList<SimpleGraph<Integer,Integer>>();
		vList = new ArrayList<Integer>();

		P5freeGraph = new SimpleGraph<Integer, Integer>(new EdgeFactory<Integer, Integer>() {
			@Override
			public Integer createEdge(Integer arg0, Integer arg1) {
				//Using the cantor pairing function to create unique IDs for each pair of vertices
				//the order of the vertices shoudl be irrelevant as this is an undirected graph, therefore
				//the vertices are sorted before the calculaton
				if(arg0 > arg1){
					int tmp = arg1;
					arg1 = arg0;
					arg0 = tmp;
				}
				//As the graphs are relatively small, this function is ok to use. 
				//essentially as long as both numbers can be represented in less than 16 bits, it will fit into an int.
				return (((arg0 + arg1) * (arg0 + arg1 + 1)) /2) + arg0;
			};
		});
		for(int i = 0; i<vOrd.size(); i++){
			vMap.put(vOrd.get(i), i);
			vList.add(i);
			P5freeGraph.addVertex(i);
		}
		for(int i = 0; i< vOrd.size(); i++){
			for(V v: Neighbors.openNeighborhood(G, vOrd.get(i))){
				P5freeGraph.addEdge(i, vMap.get(v));
			}
		}
		n = G.vertexSet().size();
		for(int i = 0; i<n; i++){
			adjGraph.put(i, new HashSet<Integer>(Neighbors.openNeighborhood(P5freeGraph, i)));
		}

		//Create induced subgraphs for each size up to n
		for(int i = 0; i<n; i++){
			SimpleGraph<Integer, Integer> tmpG = InducedSubgraph.inducedSubgraphOf(P5freeGraph, vList.subList(0, i+1));
			//				System.out.println("dlt : " + i);
			//				DotGraph(tmpG);
			graphI.add(tmpG);
		}

		comboPI = new HashSet<Set<Integer>>();
		firstPI = Pi1();
		secondPI = Pi2();
		comboPI.addAll(firstPI);
		comboPI.addAll(secondPI);
		//			DotGraph(P5freeGraph);
		//		}


	}

	/**
	 * Faster algorithm to compute maximum independent set
	 * @return size of largest independent set
	 */
	public int maxISetFaster(){
		if(G.vertexSet().isEmpty())
			return dg0and1count;
		//		DotGraph(P5freeGraph);
		//		System.out.println(comboPI);
		//Create tables for DP
		T1 = new HashMap<Integer, Map<Set<Integer>, Map<Set<Integer>, Integer>>>();
		T2 = new HashMap<Integer, Map<Set<Integer>, Map<Set<Integer>, Integer>>>();
		for(int i = -1; i< P5freeGraph.vertexSet().size(); i++){
			T1.put(i, new HashMap<Set<Integer>, Map<Set<Integer>,Integer>>());
			T2.put(i, new HashMap<Set<Integer>, Map<Set<Integer>,Integer>>());
		}



		//List delta(omega) for each omega in pi, filter duplicates and create 
		//undirected graph linking omega to delta(omega)
		int max = 0;
		piDelta = newUndirectedGraph();
		List<List<Integer>> bigDeltaList = new ArrayList<List<Integer>>();
		Set<Set<Integer>> bigDeltaSet = new HashSet<Set<Integer>>();
		bigDelta = new ArrayList<Set<Integer>>();
		PiList = new ArrayList<Set<Integer>>();
		for(Set<Integer> omg : comboPI){
			bigDeltaList.addAll(minSep(omg));
			PiList.add(omg);
		}
		for(List<Integer> dlt : bigDeltaList){
			bigDeltaSet.add(new HashSet<Integer>(dlt));
		}
		bigDeltaList = new ArrayList<List<Integer>>();
		for(Set<Integer> dlt : bigDeltaSet){
			bigDelta.add(dlt);
		}
		for(int i = 0; i<(bigDelta.size() + PiList.size()) +1; i++){
			piDelta.addVertex(i);
		}

		//		System.out.println(bigDelta);
		//Create mappings to associate vertex sets with nodes in the graph piDelta
		deltaMap = new HashMap<Set<Integer>, Integer>();
		deltaMap.put(Collections.EMPTY_SET, PiList.size() + bigDelta.size());
		for(int i = 0; i<bigDelta.size(); i++){
			//			System.out.println(bigDelta.get(i));
			deltaMap.put(bigDelta.get(i), PiList.size() + i);
		}

		piMap = new HashMap<Set<Integer>, Integer>();
		for(int i = 0; i< PiList.size(); i++){
			piMap.put(PiList.get(i), i);
		}
		for(int i = 0; i< PiList.size(); i++){
			for(int j = 0; j<bigDelta.size(); j++){
				if(PiList.get(i).containsAll(bigDelta.get(j))){
					piDelta.addEdge(i, PiList.size()+ j);
				}
			}
		}

		//Initialize each position in the DP table
		for(Set<Integer> omega : comboPI){
			for(int i = -1; i< P5freeGraph.vertexSet().size(); i++)
				T1.get(i).put(omega, new HashMap<Set<Integer>,Integer>());
			List<List<Integer>> CCofComega = CCs(omega);
			for(List<Integer> listC : CCofComega){	
				Set<Integer> C = new HashSet<Integer>(listC);
				for(int i = -1; i< P5freeGraph.vertexSet().size(); i++){
					T1.get(i).get(omega).put(C,-1);
				}
			}
		}
		//Use same variable names as in the next forloop
		if(true){
			for(int i = -1; i< P5freeGraph.vertexSet().size(); i++)
				T2.get(i).put(Collections.EMPTY_SET, new HashMap<Set<Integer>,Integer>());
			List<List<Integer>> CCofComega = CCs(Collections.EMPTY_SET);
			for(List<Integer> listC : CCofComega){	
				Set<Integer> C = new HashSet<Integer>(listC);
				for(int i = -1; i< P5freeGraph.vertexSet().size(); i++){
					T2.get(i).get(Collections.EMPTY_SET).put(C,-1);
				}
			}
		}
		for(Set<Integer> omega : bigDelta){
			for(int i = -1; i< P5freeGraph.vertexSet().size(); i++)
				T2.get(i).put(omega, new HashMap<Set<Integer>,Integer>());
			List<List<Integer>> CCofComega = CCs(omega);
			for(List<Integer> listC : CCofComega){	
				Set<Integer> C = new HashSet<Integer>(listC);
				for(int i = -1; i< P5freeGraph.vertexSet().size(); i++){
					T2.get(i).get(omega).put(C,-1);
				}
			}
		}

		//		System.out.println(T2);

		//		DotGraph(piDelta);
		for(Set<Integer> omega : comboPI){

			int tmpmax = 0;
			//Let I be empty set
			List<List<Integer>> CCofComega = CCs(omega);
			for(List<Integer> listC : CCofComega){
				Set<Integer> C = new HashSet<Integer>(listC);
				int krs = T1(omega, C,-1);
				//System.out.println(krs);
				tmpmax += krs;
			}
			if(tmpmax > max){
				max = tmpmax;
			}

			//I non-empty
			for(int I : omega){
				tmpmax = 1;
				for(List<Integer> listC : CCofComega){
					Set<Integer> C = new HashSet<Integer>(listC);
					//					System.out.println("b4: " + tmpmax);
					tmpmax += T1(omega, C, I);
					//					System.out.println("aft " + tmpmax);
					tmpmax--;
				}
				if(tmpmax > max){
					max = tmpmax;
				}
			}

		}
		if(max <= 0){
			return 1 + dg0and1count;
		}

		return max + dg0and1count;
	}

	/**
	 * Method to fill in dp table T1
	 * @param Z element in table Pi
	 * @param C connected component of G minus Z
	 * @param I vertice in Z
	 * @return largest iset containing I 
	 */
	private int T1(Set<Integer> Z, Set<Integer> C, int I){
		Map<Set<Integer>, Map<Set<Integer>, Integer>> xMap = T1.get(I);
		Map<Set<Integer>, Integer> Bmap = xMap.get(Z);
		int cMap = Bmap.get(C);
		if(cMap != -1)
			return cMap;
		Set<Integer> neigh = (Set<Integer>) Neighbors.openNeighborhood(P5freeGraph, C);
		if(I == -1){
			int k = T2(neigh, C, -1);
			T1.get(I).get(Z).put(C, k);
			return k;
		} else if(!neigh.contains(I)){
			int k = T2(neigh, C, -1) +1;
			T1.get(I).get(Z).put(C, k);
			return k;
		}
		else{
			int k = T2(neigh, C, I);
			T1.get(I).get(Z).put(C, k);
			return k;
		}
	}

	/**
	 * Method to calculate entries in dp table T2
	 * @param S member of bigDelta calculated in maxIsetfaster
	 * @param C connected component of the graph
	 * @param I vertex in S
	 * @return largest independent set
	 */
	private int T2(Set<Integer> S, Set<Integer> C, int I){

		Map<Set<Integer>, Map<Set<Integer>, Integer>> xMap = T2.get(I);
		Map<Set<Integer>, Integer> Bmap = xMap.get(S);
		int cMap = Bmap.get(C);
		if(cMap != -1)
			return cMap;

		Set<Integer> X = new HashSet<Integer>();
		if(I != -1)
			X.add(I);

		int maxSize = 0;
		Set<Integer> BuC = new HashSet<Integer>(S);
		BuC.addAll(C);
		Set<Set<Integer>> potB = new HashSet<Set<Integer>>();
		//		System.out.println(S);
		int sIdx = deltaMap.get(S);
		for(Integer neighOfSIdx : Neighbors.openNeighborhood(piDelta, sIdx)){
			Set<Integer> potpotB = PiList.get(neighOfSIdx);
			if(BuC.containsAll(potpotB))
				potB.add(potpotB);
		}



		for(Set<Integer> Bp : potB){
			int tmpSol = 0;

			List<Set<Integer>> Cp =  new ArrayList<Set<Integer>>();
			for(List<Integer> potCp : CCs(Bp)){
				if(C.containsAll(potCp))
					Cp.add(new HashSet<Integer>(potCp));
			}
			//Empty Ip
			if(I == -1){
				for(Set<Integer> cp : Cp){
					tmpSol += T1(Bp, cp, -1);
				}
				if(tmpSol > maxSize)
					maxSize = tmpSol;
			}
			//nonempty
			for(Integer Ip : Bp){
				if((S.contains(Ip) && Ip != I) || (!S.contains(Ip) && I != -1))
					continue;
				tmpSol = 1;
				for(Set<Integer> cp : Cp){
					tmpSol += T1(Bp, cp, Ip);
					tmpSol--;
				}
				if(tmpSol > maxSize)
					maxSize = tmpSol;
			}
		}

		T2.get(I).get(S).put(C, maxSize);
		return maxSize;
	}


	/**
	 * Computes the maximum independent set in the graph
	 * @return the size of the maximum independent set
	 */
	public int maxISet(){
		if(G.vertexSet().isEmpty())
			return dg0and1count;
		int max = 0;
		M = new HashMap<Integer, Map<Set<Integer>, Map<Set<Integer>, Integer>>>();
		for(int i = -1; i< P5freeGraph.vertexSet().size(); i++)
			M.put(i, new HashMap<Set<Integer>, Map<Set<Integer>,Integer>>());
		for(Set<Integer> omega : comboPI){
			for(int i = -1; i< P5freeGraph.vertexSet().size(); i++)
				M.get(i).put(omega, new HashMap<Set<Integer>,Integer>());
			List<List<Integer>> CCofComega = CCs(omega);
			for(List<Integer> listC : CCofComega){	
				Set<Integer> C = new HashSet<Integer>(listC);
				for(int i = -1; i< P5freeGraph.vertexSet().size(); i++){
					M.get(i).get(omega).put(C,-1);
				}
			}

		}
		for(Set<Integer> omega : comboPI){
			List<List<Integer>> CCofComega = CCs(omega);

			int tmpmax = 0;

			//Let I be empty set

			for(List<Integer> listC : CCofComega){	
				Set<Integer> C = new HashSet<Integer>(listC);

				int krs = M(omega, -1, C);
				//System.out.println(krs);
				tmpmax += krs;
			}
			if(tmpmax > max){
				max = tmpmax;
			}

			//I non-empty
			for(int I : omega){
				tmpmax = 1;
				for(List<Integer> listC : CCofComega){
					Set<Integer> C = new HashSet<Integer>(listC);
					tmpmax += M(omega, I, C);
					tmpmax--;
				}
				if(tmpmax > max){
					max = tmpmax;
				}
			}

		}
		if(max <= 0)
			return 1+dg0and1count;
		return max +dg0and1count;
	}

	/**
	 * Algorithm to compute the maximum independent set in polynomial time
	 * @param B element of PI
	 * @param x vertex of B, -1 for empty set
	 * @param C Component of C(B)
	 * @return the size of the largest independent set I which is a subset of B union C
	 */
	public int M(Set<Integer> B, Integer x, Set<Integer> C){
		Map<Set<Integer>, Map<Set<Integer>, Integer>> xMap = M.get(x);
		Map<Set<Integer>, Integer> Bmap = xMap.get(B);
		Integer cMap = Bmap.get(C);
		if(cMap != -1)
			return cMap;
		//use set X to represent a vertex of B for simplicity, X empty if x is empty
		Set<Integer> X = new HashSet<Integer>();
		if(x != -1)
			X.add(x);

		//maxsize is return-value
		int maxSize = 0;

		//Satisfy all the necessary conditions
		Set<Integer> BuC = new HashSet<Integer>(B);
		BuC.addAll(C);
		Set<Integer> NeighOfC = new HashSet<Integer>(Neighbors.openNeighborhood(P5freeGraph, C));
		Set<Set<Integer>> filteredComboPi = new HashSet<Set<Integer>>();
		for(Set<Integer> Bp : comboPI){
			Set<Integer> BpIntC = new HashSet<Integer>(Bp);
			BpIntC.retainAll(C);
			if(BuC.containsAll(Bp) && Bp.containsAll(NeighOfC) && !BpIntC.isEmpty())
				filteredComboPi.add(Bp);
		}

		//Maximize across omegas satisfying requirements 
		for(Set<Integer> Bp : filteredComboPi){
			int tmpSol = 0;

			Set<Integer> BintBp = new HashSet<Integer>(B);
			BintBp.retainAll(Bp);

			//Get connected components satisfying the requirements
			List<List<Integer>> CCofBpUnfiltered = CCs(Bp);
			List<List<Integer>> CCofBp = new ArrayList<List<Integer>>();
			for(List<Integer> subC : CCofBpUnfiltered){
				if(C.containsAll(subC))
					CCofBp.add(subC);
			}

			//need B intersection Bp intersection X = B intersection Bp intersection X' where X' is an element in Bp
			if(!BintBp.contains(x)){
				for(List<Integer> subC : CCofBp){
					Set<Integer> setC = new HashSet<Integer>(subC);
					tmpSol += M(Bp, -1, setC);
				}
				if (tmpSol > maxSize){
					//					System.out.println(tmpSol + " empty");
					maxSize = tmpSol;
				}
			}
			for(Integer xp : Bp){
				tmpSol = 0;
				Set<Integer> Xp = new HashSet<Integer>();
				Xp.add(xp);
				Set<Integer> BintBpintX = new HashSet<Integer>(BintBp);
				BintBpintX.retainAll(X);
				Set<Integer> BintBpintXp = new HashSet<Integer>(BintBp);
				BintBpintXp.retainAll(Xp);

				if((!X.isEmpty() && P5freeGraph.containsEdge(x, xp))){
					continue;
				}

				if(!BintBpintX.equals(BintBpintXp)){
					continue;
				}

				if(xp != x)
					tmpSol += 1;

				for(List<Integer> subC : CCofBp){
					Set<Integer> setC = new HashSet<Integer>(subC);
					tmpSol += M(Bp, xp, setC);
					tmpSol--;
				}
				if (tmpSol > maxSize){
					//					System.out.println(tmpSol + " nonempty");
					maxSize = tmpSol;
				}
			}

		}

		maxSize += X.size();
		M.get(x).get(B).put(C, maxSize); 
		return maxSize;

	}

	/**
	 * Function that finds PI1, the list of maximal cliques in all possible u,v-good triangulations of G.
	 * Runs in time O(n^3*m)
	 * @return Set of Sets, where each Set is a maximal clique in some triangulation of G
	 */
	public Set<Set<Integer>> Pi1(){
		Set<Set<Integer>> Pi = new HashSet<Set<Integer>>();
		for(int i = 0; i< n; i++){
			for(int j = i+1; j < n; j++){
				if(adjGraph.get(i).contains(j) || i == j)
					continue;
				//For every pair of non-adjacent vertices do the following
				boolean[] closedNuv = new boolean[n];
				for(int k = 0; k<n; k++){
					closedNuv[k] = true;
				}
				SimpleGraph<Integer, Integer> c = completedDeltaUV(i, j);
				for(int k = 0; k< n; k++){
					if(!adjGraph.get(i).contains(k) && !adjGraph.get(j).contains(k) && !(k == i) && !(k==j)) //Remove vertexes not in N[u,v] in G.
						closedNuv[k] = false;	
				}
				MinimalTriangulation<Integer, Integer> minTri = new MinimalTriangulation<Integer, Integer>(c);
				minTri.execute();

				//Find all maximal cliques in the minimal triangulation
				List<Set<Integer>> maximalCliques = minTri.maximalCliques;
				boolean[] junk = new boolean[maximalCliques.size()];
				for(int k = 0; k<maximalCliques.size(); k++){
					junk[k] = false;
				}
				//Discard maximal cliques that contain vertices outside the closed neighbourhood of i and j
				//as per the specification in the paper
				for(int k = 0; k< maximalCliques.size(); k++){
					for(Integer vertice : maximalCliques.get(k)){
						if(!closedNuv[vertice]){
							junk[k] = true;
							break;
						}
					}
				}
				Set<Set<Integer>> NUVmaximalCliques = new HashSet<Set<Integer>>();
				for(int k = 0; k<junk.length; k++){
					if(!junk[k])
						NUVmaximalCliques.add(maximalCliques.get(k));
				}
				Pi.addAll(NUVmaximalCliques);

			}
		}
		return Pi;
	}




	/**
	 * Returns the graph Guv where delta(u) and delta(v) have been made into cliques
	 * runtime O(N^2)
	 * @param u first node
	 * @param v second node
	 * @return Graph with delta(u) and delta(v) as cliques
	 */
	private SimpleGraph<Integer,Integer> completedDeltaUV(Integer u, Integer v){
		//Get deltas (terminology specified in the description of its method) for u and v
		Set<Integer> dU = deltaV(u);
		Set<Integer> dV = deltaV(v);

		//Create a new discardable graph
		SimpleGraph<Integer,Integer> retG = new SimpleGraph<Integer, Integer>(P5freeGraph.getEdgeFactory());
		for(Integer i : P5freeGraph.vertexSet()){
			retG.addVertex(i);
		}
		for(Integer i : P5freeGraph.vertexSet()){
			Set<Integer> Ni = Neighbors.openNeighborhood(P5freeGraph, i);
			for(Integer j : Ni){
				retG.addEdge(i, j);
			}
		}

		//Make delta u and delta v into cliques
		for(Integer i : dU){
			for(Integer j : dU){
				if(i.equals(j))
					continue;
				retG.addEdge(i, j);
			}
		}
		for(Integer i : dV){
			for(Integer j : dV){ 
				if(i.equals(j))
					continue;
				retG.addEdge(i, j);
			}
		}
		return retG;
	}




	/**
	 * Finds neighbours of v that have neighbours outside the closed neighbourhood of v
	 * @param v vertice
	 * @return list of vertices in delta(v)
	 */
	private Set<Integer> deltaV(Integer v){
		Set<Integer> neighbours = adjGraph.get(v);
		neighbours.add(v); //closed neighbourhood
		Set<Integer> deltaV = new HashSet<Integer>();
		for(Integer i : neighbours){
			if(!neighbours.containsAll(adjGraph.get(i)))
				deltaV.add(i);		
		}
		return deltaV;
	}

	public static void DotGraph(SimpleGraph<Integer, Integer> g){
		System.out.println("graph myGraph{");
		for(Integer i : g.vertexSet()){
			System.out.println(i);
			for(Integer j : g.edgesOf(i))
				if(Neighbors.opposite(g, i, j) > i)
					System.out.println(i + "--" + Neighbors.opposite(g, i, j) + ";");
		}
		System.out.println("}");

	}

	/**
	 * Testing function to find how many unordered size 3 isets exist in the graph
	 * @return
	 */
	public int countSize3ISets(){
		int cnt = 0;
		for(int u = 0;u<P5freeGraph.vertexSet().size(); u++){
			for(int v = u+1; v< P5freeGraph.vertexSet().size(); v++){
				if(adjGraph.get(u).contains(v)){
					continue;
				}
				for(int w = v+1; w <P5freeGraph.vertexSet().size(); w++){
					if(adjGraph.get(u).contains(w) || adjGraph.get(v).contains(w)){
						continue;
					}
					cnt++;
				}
			}
		}
		return cnt;
	}

	/**
	 * Testing function to count number of Independent sets of size 3
	 * that exists in the graph. Each ordering of an iset is counted.
	 * @return
	 */
	public int countSeqSize3ISets(){
		int cnt = 0;
		for(Integer u : P5freeGraph.vertexSet()){
			for(Integer v : P5freeGraph.vertexSet()){
				if(u.equals(v) || adjGraph.get(u).contains(v)){
					continue;
				}
				for(Integer w : P5freeGraph.vertexSet()){
					if(u.equals(w) || v.equals(w) || adjGraph.get(u).contains(w) || adjGraph.get(v).contains(w)){
						continue;
					}
					cnt++;
				}
			}
		}
		return cnt;
	}

	/**
	 * Calculate delta2 according to the procedure described in the paper
	 * @return a set of sets of vertices which make up delta2
	 */
	public List<List<Integer>> smallDelta2(){
		List<List<Integer>> delta2 = new ArrayList<List<Integer>>();
		if(G.vertexSet().isEmpty())
			return delta2;
		Set<Set<Integer>> delta2Set = new HashSet<Set<Integer>>();
		//		Set<Set<Integer>> chatus = new HashSet<Set<Integer>>();
		//		Set<Set<Integer>> cws = new HashSet<Set<Integer>>();
		for(int u = 0; u < n; u++){
			for(int v = 0; v < n; v++){
				if(u == v || adjGraph.get(u).contains(v)){
					continue;
				}
				for(int w = 0; w < n; w++){
					if(u == w || v == w || adjGraph.get(u).contains(w) || adjGraph.get(v).contains(w)){
						continue;
					}
					Set<Integer> NgUV = new HashSet<Integer>();
					NgUV.add(u); NgUV.add(v);
					NgUV.addAll(adjGraph.get(u)); NgUV.addAll(adjGraph.get(v));

					//					List<List<Integer>> cck = CCs(NgUV);
					Set<Integer> Cw = connectedContainingU(w, NgUV);

					//					cws.add(Cw);
					Set<Integer> NgCw = new HashSet<Integer>(Cw);

					for(Integer k : Cw){
						NgCw.addAll(adjGraph.get(k));
					}

					Set<Integer> Chatu = connectedContainingU(u, NgCw);

					//					chatus.add(Chatu);
					Set<Integer> openNgChatu = new HashSet<Integer>(Neighbors.openNeighborhood(P5freeGraph, Chatu));

					if(!openNgChatu.isEmpty()){
						delta2Set.add(openNgChatu);
					}

				}
			}
		}
		for(Set<Integer> dlt2 : delta2Set){
			//				System.out.println(dlt2);
			delta2.add(new ArrayList<Integer>(dlt2));
		}
		//System.out.println(delta2.size());
		//	System.out.println("chatus : " + chatus.size() + " deltas: " + delta2.size() + " cws: " + cws.size());
		return delta2;
	}



	/**
	 * Method to generate the list Pi2
	 * @return
	 */
	private Set<Set<Integer>> Pi2(){
		List<List<Set<Integer>>> deltaI = new ArrayList<List<Set<Integer>>>();
		List<Set<Set<Integer>>> Omegas = new ArrayList<Set<Set<Integer>>>();
		List<Set<Integer>> filteredOmega = new ArrayList<Set<Integer>>();
		Set<Set<Integer>> filteredOmegaNoDup = new HashSet<Set<Integer>>();
		List<List<List<Integer>>> omegaMinSep = new ArrayList<List<List<Integer>>>();
		for(int i = 0; i<n; i++){
			deltaI.add(new ArrayList<Set<Integer>>());
			Omegas.add(new HashSet<Set<Integer>>());	
		}
		List<List<Integer>> delta = smallDelta2();
		//System.out.println("delta: " + delta.size());
		List<List<List<Integer>>> CC = new ArrayList<List<List<Integer>>>();
		for(int i = 0 ; i<n; i++){
			CC.add(new ArrayList<List<Integer>>());
			for(int j = 0; j< delta.size(); j++){
				List<Integer> S = delta.get(j);
				Set<Integer> tmpSet = new HashSet<Integer>(S);
				CC.get(i).addAll(CCsEq(tmpSet, i));
			}
		}

		//System.out.println("CC: " + CC.size());
		//Listing neighbourhood in O(m) instead of O(n) like paper says
		for(int i = 0; i<n; i++){
			for(int j = 0; j<CC.get(i).size(); j++){
				List<Integer> aC = CC.get(i).get(j);
				Set<Integer> neigh = new HashSet<Integer>();
				for(Integer v : aC){
					for(Integer e : P5freeGraph.edgesOf(v)){
						int k = Neighbors.opposite(P5freeGraph, v, e);
						if( k <= i )
							neigh.add(k);
					}
				}
				neigh.removeAll(aC);
				if(!neigh.isEmpty()){
					deltaI.get(i).add(neigh);
				}
			}
		}
		List<Set<Set<Integer>>> piAI = PiAI(deltaI);
		List<Set<Set<Integer>>> piBI = PiBI(deltaI);

		for(int i = 0; i<piAI.size(); i++){
			if(piAI.get(i) == null)
				continue;
			for(Set<Integer> omegaI : piAI.get(i)){
				if(VerifyPMC.isPMC(graphI.get(i), new ArrayList<Integer>(omegaI))){
					Omegas.get(i).add(omegaI);
				}
			}
		}
		for(int i = 0; i< piBI.size(); i++){
			if(piBI.get(i) == null)
				continue;
			for(Set<Integer> omegaI : piBI.get(i)){
				if(VerifyPMC.isPMC(graphI.get(i), new ArrayList<Integer>(omegaI))){
					Omegas.get(i).add(omegaI);
				}
			}
		}

		for(int i = 0; i< Omegas.size(); i++){
			for(Set<Integer> omegaI : Omegas.get(i)){
				filteredOmegaNoDup.add(reconstructPMC(omegaI, i));
			}
		}
		for(Set<Integer> filtOmega: filteredOmegaNoDup){
			filteredOmega.add(filtOmega);
		}


		for(int i = 0; i< filteredOmega.size(); i++){
			omegaMinSep.add(minSep(filteredOmega.get(i)));
		}

		//		System.out.println(delta);
		delta = sort2DIntList(delta);
		for(int i = 0; i< omegaMinSep.size(); i++){
			omegaMinSep.set(i,sort2DIntList(omegaMinSep.get(i)));
		}

		//		System.out.println("First: " + firstPI);
		//		DotGraph(P5freeGraph);
		//Create Trie from delta
		Trie deltaTrie = new Trie(n);
		//		List<List<Integer>> maxDeltaI = new ArrayList<List<Integer>>();
		//		for(int i = 0; i< deltaI.get(n-1).size(); i++){
		//			maxDeltaI.add(new ArrayList<Integer>(deltaI.get(n-1).get(i)));
		//		}
		deltaTrie.addSeqs(delta);
		//		System.out.println(deltaTrie.DotGraph());
		//		System.out.println("Unfiltered " + filteredOmega);
		Set<Set<Integer>> finalOmegaList = new HashSet<Set<Integer>>();
		for(int i = 0; i<omegaMinSep.size(); i++){
			//			System.out.println(omegaMinSep.get(i));
			if(deltaTrie.containsAll(omegaMinSep.get(i))){
				finalOmegaList.add(new HashSet<Integer>(filteredOmega.get(i)));
			}
		}
		//		System.out.println("filtered: " + finalOmegaList);
		return finalOmegaList;
	}

	private List<Set<Set<Integer>>> PiAI(List<List<Set<Integer>>> deltaI){
		List<Set<Set<Integer>>> piAI = new ArrayList<Set<Set<Integer>>>();
		for(int i = 0; i<deltaI.size(); i++){
			piAI.add(new HashSet<Set<Integer>>());
		}
		for(int i = 0; i<deltaI.size(); i++){
			for(Set<Integer> Si : deltaI.get(i)){
				for(int j = 0; j<= i; j++){
					Set<Integer> tmpSet = new HashSet<Integer>(Si);
					tmpSet.add(j);
					piAI.get(i).add(tmpSet);
				}
			}     
		}
		return piAI;
	}

	private List<Set<Set<Integer>>> PiBI(List<List<Set<Integer>>> deltaI){
		List<Set<Set<Integer>>> piBI = new ArrayList<Set<Set<Integer>>>();
		for(int i = 0; i<deltaI.size(); i++){
			piBI.add(new HashSet<Set<Integer>>());
		}
		for(int i = 0; i<deltaI.size(); i++){
			for(Set<Integer> Si : deltaI.get(i)){
				List<List<Integer>> CiSet = CCsEq(Si,i);
				for(List<Integer> Ci : CiSet){
					for(Integer v : Si){
						Set<Integer> tmpSet = new HashSet<Integer>(Si);
						Set<Integer> Nv = Neighbors.openNeighborhood(graphI.get(i), v);
						Nv.retainAll(Ci);
						//						Set<Integer> Nv = new HashSet<Integer>(adjGraph.get(v));
						//						Set<Integer> NvRemove = new HashSet<Integer>();
						//						for(Integer v2 : Nv){
						//							if(v2 > i){
						//								NvRemove.add(v2);
						//								continue;
						//							}
						//							if(!Ci.contains(v2))
						//								NvRemove.add(v2);
						//						}
						//						Nv.removeAll(NvRemove);
						tmpSet.addAll(Nv);
						piBI.get(i).add(tmpSet);
					}
				}
			}
		}
		return piBI;
	}
	/**
	 * Method to sort each row in a 2D array of ints simultaneously.
	 * As every number in unsorted is smaller than n(size of graph), 
	 * the algorithm runs in O(N^2). It does so by creating a new 2D array with a row for each number
	 * from 0 to n-1. The new 2D array shows in which row in unsorted one can find a specific number. 
	 * Then the algorithm looks through this new 2D array, starting from 0 and up to n-1, 
	 * and places the numbers in corresponding rows to get a final sorted version of input. 
	 * @param unsorted a 2D array of unsorted integers
	 * @return a 2D array of integers where each row is sorted in ascending order
	 */
	private List<List<Integer>> sort2DIntList(List<List<Integer>> unsorted){
		List<List<Integer>> sorting = new ArrayList<List<Integer>>();
		List<List<Integer>> sorted = new ArrayList<List<Integer>>();
		for(int i = 0; i<n; i++){
			sorting.add(new ArrayList<Integer>());
		}
		for(int i = 0; i<unsorted.size(); i++){
			for(int j = 0; j<unsorted.get(i).size(); j++){
				sorting.get(unsorted.get(i).get(j)).add(i);
			}
		}
		for(int i = 0; i<unsorted.size(); i++){
			sorted.add(new ArrayList<Integer>());
		}
		for(int i = 0; i<sorting.size(); i++){
			for(int j = 0; j<sorting.get(i).size(); j++){
				sorted.get(sorting.get(i).get(j)).add(i);
			}
		}
		return sorted;
	}




	//	private Set<Integer> reconstructPMC(Set<Integer> pmc, int start){
	//		Set<Integer> o = new HashSet<Integer>();
	//		o.add(1);
	//		o.add(2);
	//		Set<Integer> retPMC = new HashSet<Integer>(pmc);
	//		for(int i = start+1; i < n; i++){ //Starts from G{i+1}
	//			Set<Integer> tmpSet = new HashSet<Integer>(retPMC);
	//			tmpSet.add(i);
	//			if(VerifyPMC.isPMC(graphI.get(i), new ArrayList<Integer>(tmpSet)))
	//				retPMC = tmpSet;
	//		}
	//		return retPMC;
	//
	//		
	//		
	//	}


	/**
	 * Method that rebuilds a pmc based on the procedure outlined by Daniel.
	 * will filter away any set of integers that are not a pmc in the graph specified at start.
	 * 
	 * @param pmc set to expand into full pmc
	 * @param start starting graph size
	 * @return a pmc in the original graph
	 */
	private Set<Integer> reconstructPMC(Set<Integer> pmc, int start){		
		Set<Integer> retPMC = new HashSet<Integer>(pmc);
		//		System.out.println("start: " + start);
		for(int i = start+1; i < n; i++){ //Starts from G{i+1}
			//			System.out.println(retPMC);
			if(!VerifyPMC.isPMC(graphI.get(i), new ArrayList<Integer>(retPMC)))
				retPMC.add(i);
		}
		//		if(!VerifyPMC.isPMC(P5freeGraph, new ArrayList<Integer>(retPMC))){
		//			DotGraph(graphI.get(start));
		//			System.out.println(retPMC);
		//			System.out.println("failed " + n);
		//			System.exit(0);
		//		}
		return retPMC;

	}

	/**
	 * Method to list all minimal separators of the graph that are subsets of vertices.
	 * @param vertices set of vertices in which to find minimal separators
	 * @return the set of minimal separators in vertices
	 */
	private List<List<Integer>> minSep(Set<Integer> vertices){
		List<List<Integer>> CC = CCs(vertices);
		List<List<Integer>> seps = new ArrayList<List<Integer>>();
		for(List<Integer> C : CC){
			List<Integer> neighbourhood = new ArrayList<Integer>(Neighbors.openNeighborhood(P5freeGraph, C));
			if(CC.size() == 1 && neighbourhood.size() == vertices.size())
				continue;
			if(!neighbourhood.isEmpty())
				seps.add(neighbourhood);
		}
		return seps;
	}

	/**
	 * This method finds all connected components in the graph, 
	 * when the set separator is removed.
	 * @param separator is the separator to split the graph
	 * @return list of connected components
	 */
	private List<List<Integer>> CCs(Set<Integer> separator){
		return CCs(separator, n);
	}

	public SimpleGraph<Integer, Integer> newUndirectedGraph(){
		SimpleGraph<Integer, Integer> returnGraph = new SimpleGraph<Integer, Integer>(new EdgeFactory<Integer, Integer>() {
			@Override
			public Integer createEdge(Integer arg0, Integer arg1) {
				//Using the cantor pairing function to create unique IDs for each pair of vertices
				//the order of the vertices shoudl be irrelevant as this is an undirected graph, therefore
				//the vertices are sorted before the calculaton
				if(arg0 > arg1){
					int tmp = arg1;
					arg1 = arg0;
					arg0 = tmp;
				}
				//As the graphs are relatively small, this function is ok to use. 
				//essentially as long as both numbers can be represented in less than 16 bits, it will fit into an int.
				return (((arg0 + arg1) * (arg0 + arg1 + 1)) /2) + arg0;
			};
		});
		return returnGraph;
	}

	/**
	 * Method to find connected components in Graph - separator, using vertices with id < cutoff
	 * @param separator set of vertices to split graph with
	 * @param cutoff largest id of vertices in output
	 * @return list of connected components
	 */
	private List<List<Integer>> CCs(Set<Integer> separator, int cutoff){
		List<List<Integer>> comps = new ArrayList<List<Integer>>();
		int[] comp = new int[n];
		for(int i = 0; i<n; i++){
			comp[i] = -1;
			if(separator.contains(i))
				comp[i] = -2;
		}
		int currComp = 0;
		for(int i = 0; i< cutoff; i++){
			if(comp[i] != -1)
				continue;
			//			Set<Integer> tmpComp = new HashSet<Integer>();
			//			tmpComp.add(i);
			Queue<Integer> q = new LinkedList<Integer>();
			q.add(i);
			comp[i] = currComp;
			while(!q.isEmpty()){
				int k = q.poll();
				for(Integer l : adjGraph.get(k)){
					if(l < cutoff && comp[l] == -1){
						q.add(l);
						//Set which component vertex l belongs to, aka component id
						comp[l] = currComp;
					}
				}
			}
			currComp++;
		}
		for(int i = 0; i<currComp; i++){
			comps.add(new ArrayList<Integer>());
		}
		//For each vertex, get component id and add it to the relevant component list
		for(int i = 0; i<n; i++){
			if(comp[i] >= 0)
				comps.get(comp[i]).add(i);
		}
		return comps;
	}

	/**
	 * Method to find connected components in Graph - separator, using vertices with id <= cutoff
	 * @param separator set of vertices to split graph with
	 * @param cutoff largest id of vertices in output
	 * @return list of connected components
	 */
	private List<List<Integer>> CCsEq(Set<Integer> separator, int cutoff){
		if(cutoff >= n){
			System.out.println("error, cutoff too large");
			System.exit(0);
		}

		List<List<Integer>> comps = new ArrayList<List<Integer>>();
		int[] comp = new int[n];
		for(int i = 0; i<n; i++){
			comp[i] = -1;
			if(separator.contains(i))
				comp[i] = -2;
		}
		int currComp = 0;
		for(int i = 0; i<= cutoff; i++){
			if(comp[i] != -1)
				continue;
			//			Set<Integer> tmpComp = new HashSet<Integer>();
			//			tmpComp.add(i);
			Queue<Integer> q = new LinkedList<Integer>();
			q.add(i);
			comp[i] = currComp;
			while(!q.isEmpty()){
				int k = q.poll();
				for(Integer l : adjGraph.get(k)){
					if(l <= cutoff && comp[l] == -1){
						q.add(l);
						//Set which component vertex l belongs to, aka component id
						comp[l] = currComp;
					}
				}
			}
			currComp++;
		}
		for(int i = 0; i<currComp; i++){
			comps.add(new ArrayList<Integer>());
		}
		//For each vertex, get component id and add it to the relevant component list
		for(int i = 0; i<n; i++){
			if(comp[i] >= 0)
				comps.get(comp[i]).add(i);
		}
		return comps;
	}

	/**
	 * Method to find the connected component containing
	 * vertex with id u in the graph separated by avoid
	 * @param u id of the vertex to find
	 * @param avoid set of vertices to separate graph
	 * @return the connected component containing u
	 */
	public Set<Integer> connectedContainingUOLD(Integer u, Collection<Integer> avoid){
		Map<Integer, Boolean> visited = new HashMap<Integer, Boolean>();
		for(Integer v : P5freeGraph.vertexSet())
			visited.put(v, false);
		Set<Integer> comp = new HashSet<Integer>();
		Queue<Integer> q = new LinkedList<Integer>();
		q.add(u);
		visited.put(u, true);
		comp.add(u);
		while(!q.isEmpty()){
			Integer k = q.poll();
			for(Integer v : adjGraph.get(k)){
				if(!visited.get(v)){
					visited.put(v, true);
					if(!avoid.contains(v)){
						q.add(v);
						comp.add(v);
					}
				}
			}
		}
		return comp;
	}

	/**
	 * Method to find the connected component containing
	 * vertex with id u in the graph separated by avoid
	 * @param u id of the vertex to find
	 * @param avoid set of vertices to separate graph
	 * @return the connected component containing u
	 */
	public Set<Integer> connectedContainingU(Integer u, Collection<Integer> avoid){
		int[] visited = new int[n];
		for(int i = 0; i<n; i++){
			visited[i] = -1;
			if(avoid.contains(i))
				visited[i] = -2;
		}
		Set<Integer> comp = new HashSet<Integer>();
		Queue<Integer> q = new LinkedList<Integer>();
		q.add(u);
		visited[u] = 1;
		comp.add(u);
		while(!q.isEmpty()){
			Integer k = q.poll();
			for(Integer v : adjGraph.get(k)){
				if(visited[v] == -1){
					visited[v] = 1;
					q.add(v);
					comp.add(v);
				}
			}
		}
		return comp;
	}

	public static List<Long> readLongGraphsFromFile(String filename){
		List<Long> graphs = new ArrayList<Long>();
		try {
			Scanner sc = new Scanner(new File(filename));
			while(sc.hasNextLong()){
				graphs.add(sc.nextLong());
			}
			sc.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
		return graphs;
	}

	/**
	 * Reads graphs in the long format
	 * @param filename
	 * @return
	 */
	public static List<BigInteger> readBigIntGraphsFromFile(String filename){
		List<BigInteger> graphs = new ArrayList<BigInteger>();
		try {
			Scanner sc = new Scanner(new File(filename));
			while(sc.hasNext()){
				graphs.add(new BigInteger(sc.next()));
			}
			sc.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return graphs;
	}

	/**
	 * Reads graphs in the long format
	 * @param filename
	 * @return
	 */
	public static Set<BigInteger> readNonDuplicateBigIntGraphsFromFile(String filename){
		Set<BigInteger> graphs = new HashSet<BigInteger>();
		try {
			Scanner sc = new Scanner(new File(filename));
			while(sc.hasNext()){
				graphs.add(new BigInteger(sc.next()));
			}
			sc.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return graphs;
	}

	/**
	 * Function to convert a long to a graph according to the description given elsewhere in this general class.
	 * @param l long to convert
	 * @return a graph based on the long
	 */
	public static TestGraph longToGraph(Long l){
		TestGraph g = new TestGraph();
		long orig = l;
		int nBits = (63-Long.numberOfLeadingZeros(l));
		int n = (int) ((1+Math.sqrt(1+(4*nBits*2)))/2);
		for(int i = 0; i<n; i++){
			g.addVertex(i);
		}
		for(int i = n-1; i>= 0; i--){
			for(int j = i-1; j>= 0; j--){
				if((1 & l) == 1){
					g.addEdge(i, j);
				}
				l = l >> 1;
			}
		}
		return g;
	}

	public static TestGraph bigintToGraph(BigInteger l){
		TestGraph g = new TestGraph();
		BigInteger orig = l;
		//Log base 2
		int nBits = orig.bitLength();// (63-Long.numberOfLeadingZeros(l));
		int n = (int) ((1+Math.sqrt(1+(4*nBits*2)))/2);
		for(int i = 0; i<n; i++){
			g.addVertex(i);
		}
		for(int i = n-1; i>= 0; i--){
			for(int j = i-1; j>= 0; j--){
				if(BigInteger.ONE.and(orig).equals(BigInteger.ONE)){
					g.addEdge(i, j);
				}
				orig = orig.shiftRight(1);//l >> 1;
			}
		}
		return g;
	}



	public boolean isClique(List<Integer> potClique){
		for(int x : potClique){
			for(int y : potClique){
				if(x == y)
					continue;
				if(!P5freeGraph.containsEdge(x, y))
					return false;
			}
		}
		return true;
	}
	/**
	 * Trie (prefix-tree) used to detect if a sequence is found in a list of sequences.
	 * @author håvard
	 *
	 */
	public class Trie{
		TrieNode root;

		/**
		 * Constructor that creates a root node for a tree that can reference
		 * symbols many different characters.
		 * @param symbols size of the set of characters found in the tree
		 */
		public Trie(int symbols){
			root = new TrieNode(symbols);
		}

		public String DotGraph(){
			String outP = "graph myGraph{";
			outP += root.dotGraphChildren();
			outP += "\n }";
			return outP;
		}

		/**
		 * Add a new sequence to the tree
		 * @param seq is the sequence to add to the Trie
		 */
		public void addSeq(List<Integer> seq){
			root.addSeq(seq);
		}


		/**
		 * Convenient function to add a list of sequences
		 * @param seqs is the list of sequences to add to the Trie
		 */
		public void addSeqs(List<List<Integer>> seqs){
			for(int i = 0; i< seqs.size(); i++){
				this.addSeq(seqs.get(i));
			}
		}

		/**
		 * Method to detect if the Trie contains a given sequnece
		 * @param seq the sequence to look up
		 * @return true if Trie contains seq, false otherwise.
		 */
		public boolean contains(List<Integer> seq){
			return root.contains(seq);
		}

		/**
		 * Method to detect if the Trie contains a given sequnece
		 * @param seq the sequence to look up
		 * @return true if Trie contains seq, false otherwise.
		 */
		public boolean containsAll(Collection<List<Integer>> seqs){
			Boolean ret = true;
			for(List<Integer> seq : seqs){
				if(!root.contains(seq))
					ret = false;
			}
			return ret;
		}


		/**
		 * Class to represent a single node in a Trie, with all the necessary functionality
		 * to evaluate Trie properties and perform operations on the Trie.
		 * @author håvard
		 *
		 */
		private class TrieNode {
			/**
			 * id used to reference node
			 */
			int id;

			String uniqueID;
			/**
			 * List of child nodes
			 */
			List<TrieNode> children;
			/**
			 * Node which contains a reference to this node
			 */
			TrieNode parent;
			/**
			 * number of child nodes
			 */
			int nrOfChildren;
			/**
			 * This TrieNode is a leaf if it has no children
			 */
			boolean isleaf;
			/**
			 * Number of possible symbols that the children can have
			 */
			int symbols;
			/**
			 * True if a sequence that was added to the Trie ends in this node
			 */
			boolean endOfSeq;

			/**
			 * Initialize the root node
			 * @param symbols nr of possible symbols that can be as children
			 */
			public TrieNode(int symbols){
				id = -1;
				uniqueID = "0";
				this.children = new ArrayList<TrieNode>();
				for(int i = 0; i<symbols; i++){
					children.add(null);
				}
				isleaf = true;
				endOfSeq = false;
				nrOfChildren = 0;
				this.symbols= symbols;
			}

			/**
			 * General constructor for a Trie node
			 * @param id this is the id of the node and also the information which it carries
			 * @param symbols nr of possible symbols for children
			 * @param parent node that contains this as a child
			 */
			public TrieNode(int id, int symbols, TrieNode parent){
				this.id = id;
				this.children = new ArrayList<TrieNode>();
				for(int i = 0; i<symbols; i++){
					children.add(null);
				}
				isleaf = true;
				endOfSeq = false;
				nrOfChildren = 0;
				uniqueID = parent.uniqueID +"" + id;
				this.parent = parent;
				this.symbols= symbols;
			}

			public String dotGraphChildren(){
				String ret = "" + uniqueID;
				if(isleaf)
					ret += " [shape=triangle]";
				else if(endOfSeq)
					ret += " [shape=box]";
				for(TrieNode i : children){
					if(i != null){
						ret += "\n" + uniqueID + " -- " +i.uniqueID;
						ret += "\n" + i.dotGraphChildren();
					}
				}
				return ret;
			}

			/**
			 * Adds a new child node to this node
			 * @param x id of the child
			 * @return true if successfully added, false otherwise
			 */
			public boolean addChild(int x){
				if (x >= children.size() || children.get(x) != null){
					return false;
				}
				TrieNode trx = new TrieNode(x, symbols, this);
				children.set(x, trx);
				isleaf = false;
				nrOfChildren++;
				return true;
			}

			/**
			 * Add the remainder of the sequence from index dist to the end.
			 * @param seq sequence to add
			 * @param dist where to start adding the sequence from
			 */
			private void addSeq(List<Integer> seq, int dist){
				if(dist == seq.size()){
					endOfSeq = true;
					return;
				}
				int next = seq.get(dist);
				if(children.get(next) == null){
					addChild(next);
				}
				children.get(next).addSeq(seq, dist+1);

			}

			/**
			 * Add a new sequence
			 * @param seq sequence to add
			 */
			public void addSeq(List<Integer> seq){
				addSeq(seq, 0);

			}

			/**
			 * Test if the subtree of this node contains the sequence seq
			 * @param seq sequence to test
			 * @return true if contained, false otherwise
			 */
			public boolean contains(List<Integer> seq){
				return contains(seq, 0);
			}

			/**
			 * Test if subtree contains sequence from dist to end of sequence
			 * @param seq sequence to test
			 * @param dist where to start in the sequence
			 * @return true if contained, false otherwise
			 */
			private boolean contains(List<Integer> seq, int dist){
				if(dist == seq.size() && endOfSeq)
					return true;
				if(dist >= seq.size() || seq.get(dist) == null)
					return false;
				int next = seq.get(dist);
				if(children.get(next) != null){
					//System.out.println("at: "  + next);
					return children.get(next).contains(seq, dist+1);
				}
				return false;
			}
		}
	}


	public static void main(String[] args) {

		//		TestGraph gr2 = GraphGenerator.star(23);
		//		ISP5Free<Integer, Integer> ispGR2 = new ISP5Free<Integer, Integer>(gr2);
		//		ispGR2.DotGraph(ispGR2.graphI.get(22));
		//		gr2.DotGraph();
		//		Set<Integer> kfe = new HashSet<Integer>();
		////		kfe.add(0);
		//		System.out.println(ispGR2.CCsEq(kfe, 23));


		String filename = "30Graphs.txt";
		System.out.println("reading " +filename);
		Set<BigInteger> grps = readNonDuplicateBigIntGraphsFromFile(filename);
		List<TestGraph> grpsSimpUF = new ArrayList<TestGraph>();
		List<TestGraph> grpsSimp = new ArrayList<TestGraph>();
		for(BigInteger l : grps){
			grpsSimpUF.add(bigintToGraph(l));
		}
		for(TestGraph g : grpsSimpUF){
			if(GraphGenerator.listComponents(g, g.vertexSet()).size() == 1)
				grpsSimp.add(g);
		}

		System.out.println("Number of graphs: " + grpsSimp.size());
		long startTime = System.nanoTime();

		int totPi1 = 0;
		int maxPi1 = 0;

		int totPi2 = 0;
		int maxPi2 = 0;

		int totDlt2 = 0;
		int maxDlt2 = 0;

		int totDiff = 0;
		int maxDiff = 0;

		int maxPi = 0;
		int totPi = 0;

		int maxPiIdx = 0;

		for(int i = 0; i<grpsSimp.size(); i++){

			if(i % 1 == 0)
				System.out.println("At " + i);
			TestGraph gr = grpsSimp.get(i);
			//									ExactVertexCover<Integer, Integer> exV = new ExactVertexCover<Integer, Integer>(gr);
			//									Collection<Integer> inDset = exV.execute();
			//									int iSetSize = gr.vertexSet().size()-inDset.size();

			ISP5Free<Integer,Integer> ispGr = new ISP5Free<Integer,Integer>(gr);
			int kfast = ispGr.maxISetFaster();
			int k = ispGr.maxISet();

			totPi += ispGr.comboPI.size();
			if(ispGr.comboPI.size() > maxPi){
				maxPiIdx = i;
				maxPi = ispGr.comboPI.size();
			}

			List<List<Integer>> dlt = ispGr.smallDelta2();
			totDlt2 += dlt.size();
			if(dlt.size() > maxDlt2){
				maxDlt2 = dlt.size();
			}

			Set<Set<Integer>> pi1 = ispGr.firstPI;
			totPi1 += pi1.size();
			if(pi1.size() > maxPi1){
				maxPi1 = pi1.size();
			}
			Set<Set<Integer>> pi2 = ispGr.secondPI;
			totPi2 += pi2.size();
			if(pi2.size() > maxPi2)
				maxPi2 = pi2.size();
			pi2.removeAll(pi1);
			totDiff += pi2.size();
			if(pi2.size() > maxDiff)
				maxDiff = pi2.size();
			//									
			//										System.out.println(k + " " + kfast);
			//										if( kfast != k){
			//										gr.DotGraph();
			//										return;
			//									}
		}

		System.out.println("TotPi: " + totPi + " maxPi: " + maxPi );
		System.out.println("TotPi1: " + totPi1 + " maxPi1: " + maxPi1 );
		System.out.println("TotPi2: " + totPi2 + " maxPi2: " + maxPi2 );
		System.out.println("TotPiDiff: " + totDiff + " maxDiff: " + maxDiff );
		System.out.println("TotDlt2: " + totDlt2 + " maxDlt2: " + maxDlt2 );
		System.out.println("MaxPiIdx: " + maxPiIdx);

		long stopTime = System.nanoTime();
		long elapsedTime = stopTime - startTime;
		System.out.println(elapsedTime);


	}
}


