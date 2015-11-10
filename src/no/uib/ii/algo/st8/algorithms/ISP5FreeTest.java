/**
 * 
 */
package no.uib.ii.algo.st8.algorithms;

import static org.junit.Assert.*;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import no.uib.ii.algo.st8.tests.*;

/**
 * @author havard
 *
 */
public class ISP5FreeTest {

	TestGraph g;
	ISP5Free<Integer, Integer> isp;
	
	/**
	 * @throws java.lang.Exception
	 */
	@Before
	public void setUp() throws Exception {
		g = new TestGraph();
		for(int i = 0; i<5; i++)
			g.addVertex(i);
		for(int i = 0; i<5; i++){
			g.addEdge(i, (i+1) % 5);
		}
		isp = new ISP5Free<Integer, Integer>(g);
		
		
	}

	

	/**
	 * Test method for {@link no.uib.ii.algo.st8.algorithms.ISP5Free#maxISet(java.util.Set, java.util.Set, java.util.Set)}.
	 */
	@Test
	public void testMaxISet() {
		
	}

	/**
	 * Test method for {@link no.uib.ii.algo.st8.algorithms.ISP5Free#listMaxCliques()}.
	 */
	@Test
	public void testListMaxCliques() {
		
	}

	/**
	 * Test method for {@link no.uib.ii.algo.st8.algorithms.ISP5Free#smallDelta2()}.
	 */
	@Test
	public void testSmallDelta2() {
		
	}

	/**
	 * Test method for {@link no.uib.ii.algo.st8.algorithms.ISP5Free#connectedContainingU(java.lang.Integer, java.util.Collection)}.
	 */
	@Test
	public void testConnectedContainingU() {
		Set<Integer> sep = new HashSet<Integer>();
		sep.add(2);
		sep.add(4);
		Set<Integer> ret = isp.connectedContainingU(0, sep);
		Set<Integer> expect = new HashSet<Integer>();
		expect.add(0); expect.add(1);
		assertEquals(ret, expect);
	}


}
