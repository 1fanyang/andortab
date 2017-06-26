package abd.tableau.iterative;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import abd.knowledge.util.SetOps;
import net.sf.tweety.commons.BeliefBaseSampler;
import net.sf.tweety.commons.ParserException;
import net.sf.tweety.commons.Signature;
import net.sf.tweety.logics.commons.analysis.BeliefSetInconsistencyMeasure;
import net.sf.tweety.logics.commons.analysis.DHitInconsistencyMeasure;
import net.sf.tweety.logics.commons.analysis.DMaxInconsistencyMeasure;
import net.sf.tweety.logics.commons.analysis.DSumInconsistencyMeasure;
import net.sf.tweety.logics.commons.analysis.DfInconsistencyMeasure;
import net.sf.tweety.logics.commons.analysis.NaiveMusEnumerator;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.analysis.ContensionInconsistencyMeasure;
import net.sf.tweety.logics.pl.analysis.DalalDistance;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.sat.LingelingSolver;
import net.sf.tweety.logics.pl.sat.MarcoMusEnumerator;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;
import net.sf.tweety.logics.pl.semantics.PossibleWorld;
import net.sf.tweety.logics.pl.semantics.PossibleWorldIterator;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.Contradiction;
import net.sf.tweety.logics.pl.syntax.Disjunction;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import net.sf.tweety.logics.pl.syntax.PropositionalSignature;
import net.sf.tweety.logics.pl.syntax.Tautology;
import net.sf.tweety.logics.pl.util.CnfSampler;
import net.sf.tweety.math.func.FracAggrFunction;

public class Test {
public static void main(String[] args) throws ParserException, IOException{
	
	//
//	PropositionalSignature sig = new PropositionalSignature(10);
//	
//	BeliefBaseSampler<PlBeliefSet> sampler = new CnfSampler(sig, 0.3);
//	
//	for(int i = 0; i < 10; i++)
//		System.out.println(sampler.randomSample(5, 10));

	// test the correction of the hypotheses.

	PlParser parser = new PlParser();
	PropositionalFormula ob = (PropositionalFormula) parser.parseFormula("!c||c");
	PropositionalFormula oc = (PropositionalFormula) parser.parseFormula("c");

	
	// Create a pl knowledge base
//	PlParser parser = new PlParser();
//	String file="/home/yifan/logickb/test1.txt";
//	PlBeliefSet kb = parser.parseBeliefBaseFromFile(file);

	PlBeliefSet x = new PlBeliefSet();
	
	// Set SAT solver
	SatSolver.setDefaultSolver(new Sat4jSolver());
	
	// consistency
	System.out.println("knowledge base is "+ x.isConsistent()+" consistent");
	System.out.println(x.getMinimalInconsistentSubsets());
	
	PropositionalFormula oa = (PropositionalFormula) parser.parseFormula("s");
	PropositionalFormula od = (PropositionalFormula) parser.parseFormula("s&&v");
//	PropositionalFormula ob = (PropositionalFormula) parser.parseFormula("d||c");
//	PropositionalFormula oc = (PropositionalFormula) parser.parseFormula("d||! c");
//	Conjunction c =new Conjunction();
//	Conjunction d =new Conjunction();
////	d.addAll(oc.getLiterals());
//	c.add(oa);
//	d.add(oa);
//	d.add(c);
//	d.add(ob);
//	
//	System.out.println("hashcode " + d + " : " + d);
//	System.out.println("hashcode " + od + " : " + od.hashCode());
//	System.out.println("hashcode " + ob + " : " + ob.hashCode());
//	System.out.println("hashcode " + oc + " : " + oc.complement().hashCode());
//	System.out.println("signature " + oc + " : " + oc.getSignature());
//
//	
//	
//	//	PropositionalFormula od;
////	od.oc.getLiterals()
//	HashSet<PropositionalFormula> ha = new HashSet<PropositionalFormula>();
//	HashSet<PropositionalFormula> hc = new HashSet<PropositionalFormula>();
//	ha.add(oa);
//	ha.add(ob);
//	hc.add(oc);
//	System.out.println("xx" + ha.contains(oc));
//	HashSet<String> has = new HashSet<String>();
//	HashSet<String> hcs = new HashSet<String>();
//	has.add(oa.toString());
//	has.add(ob.toString());
//	hcs.add(oc.toString());
//	System.out.println(oa.toString());
//	System.out.println(oc.toString());
//	System.out.println(ob.toString().equals(oc.toString()));
//	System.out.println(ha.containsAll(hc));
//
//	System.out.println(has.contains(hcs));

//	System.out.println(c);


	if(oa.equals(ob))
		System.out.println("yes");
	

	x.add(oa);
	x.add(ob);
	
//	PropositionalFormula oc = (PropositionalFormula) parser.parseFormula("s");
	PlBeliefSet y = new PlBeliefSet();
	y.add(oc);
	if(y.contains(x))
		System.out.println("yess");
		
	// singature 
	Signature sg = x.getSignature();
	System.out.println(sg.getClass());
	System.out.println(sg.toString());
//	
//	System.out.println(file);
	
	// print every formula in the terminal
	System.out.println(x.toString());
	Iterator<PropositionalFormula> it = x.iterator();
	while(it.hasNext()){
		PropositionalFormula pf = it.next();
		
		System.out.println(pf.toString());
		System.out.println("NNF " +pf.toNnf());
		System.out.println("NNF C " +pf.toNnf().collapseAssociativeFormulas());
		System.out.println("DNF " +pf.toDnf());
		System.out.println("DNF C " +pf.toDnf().collapseAssociativeFormulas());
		
		PropositionalFormula nnf = pf.toDnf().collapseAssociativeFormulas();
		
	    // DNF( P || Q) = DNF(P) || DNF(Q)
	    if(nnf instanceof Disjunction) {
	      Disjunction d = (Disjunction) nnf;
	      d.remove(new Contradiction());
	      Disjunction dnf = new Disjunction();
	      for(PropositionalFormula f : d) {
		      System.out.println("dnf " + f.toNnf());
	      }
		}

		
		System.out.println("CNF " +pf.toCnf());
		System.out.println("CNF C" +pf.toCnf().collapseAssociativeFormulas());
		System.out.println("atoms "+ pf.getLiterals());
		
		Set<PropositionalFormula> lits = pf.getLiterals();
		Vector<PropositionalFormula> a = new Vector<PropositionalFormula>(lits);
		Vector<PropositionalFormula> b = new Vector<PropositionalFormula>(lits);
		
		outerloop:
		for(int i=0; i< a.size();i++){
			for(int j=i; j< a.size();j++){
				if(a.elementAt(i).equals(a.elementAt(j).complement())){
					System.out.println(a.elementAt(i));
					System.out.println(a.elementAt(j));
					System.out.println(false);
					break outerloop;
				}
			}
		}
	}
}
}
