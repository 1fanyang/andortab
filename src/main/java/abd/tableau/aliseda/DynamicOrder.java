package abd.tableau.aliseda;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import abd.knowledge.util.DistanceMeasure;
import net.sf.tweety.commons.ParserException;
import net.sf.tweety.commons.Signature;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

/* Ordering the formulas in the kb during the expansion process*/
public class DynamicOrder {

	public static void main(String[] args) throws FileNotFoundException, ParserException, IOException {
		PlParser parser = new PlParser();
		String file="/home/yifan/workspace_eclipse/iterativeTab/kbset/generator_5_5/generator5.txt";
		
		PlBeliefSet kb = parser.parseBeliefBaseFromFile(file);

		PropositionalFormula obs = (PropositionalFormula) parser.parseFormula("p1 && p3");


		// Set SAT solver
		SatSolver.setDefaultSolver(new Sat4jSolver());

		// consistency
		boolean consistency =kb.isConsistent();
		System.out.println("knowledge base is "+consistency+" consistent");
		if(!consistency){
			System.out.println("not a consistent kb. Stop");
			System.exit(0);
		}
		
		// order the kb formula list 
		Conjunction cnf = kb.toCnf();
		Iterator it = cnf.iterator();

		
		ArrayList<PropositionalFormula> kblist= new ArrayList<PropositionalFormula> ();
		while(it.hasNext()){
			PropositionalFormula pf = (PropositionalFormula) it.next();
			System.out.println(pf);
			kblist.add(pf);
		}
		sortFormula(kblist,obs);
		PlBeliefSet newkb= new PlBeliefSet();
		newkb.addAll(kblist);
		
		
		
		// Get current time
		long start = System.currentTimeMillis();
		
		
		// Initialization aliseda tableau
		AlisedaTableau tab = new AlisedaTableau();
		tab.addKb(newkb);
		tab.addRoot(obs);
		
		// Expansion of the tableau
		tab.expansion();
		
		// print tableau
		 //tab.printGraph();
		 System.out.println("nodes size: "+ tab.getnbNodes());
		
		Vector<AlisedaNode> leaves = tab.getLeaves();
		System.out.println("open branch size: "+leaves.size());
		for(int i=0; i<leaves.size(); i++){
			leaves.elementAt(i).removeRedundance();

		}
		
		// compute explanation
		Vector<PropositionalFormula> hyp = tab.generationHypotheses(leaves);
		for(int i=0; i<hyp.size(); i++){
			System.out.println("hyp " +i + "  "+ hyp.elementAt(i));
		}

		// get Explanation
		
		Vector<PropositionalFormula> minimal = tab.getMiniamlExplantion(hyp);
		for(int i=0; i<minimal.size(); i++){
			System.out.println("minimal " +i + "  "+ minimal.elementAt(i));
		}
		
		// Get elapsed time in milliseconds
		long elapsedTimeMillis = System.currentTimeMillis()-start;
		
		// Get elapsed time in seconds
		float elapsedTimeSec = elapsedTimeMillis/1000F;
		
		System.out.println("elapsedTimeSec " +elapsedTimeSec);
		System.out.println("Finish");
	}
	
	public static void sortFormula(ArrayList<PropositionalFormula> kblist, PropositionalFormula w){
		HashSet<PropositionalFormula> sig = new HashSet<PropositionalFormula>();
		for(int i=0; i<kblist.size(); i++){
			sig.addAll(kblist.get(i).getAtoms());
		}
		System.out.println(sig);   
		HashMap<PropositionalFormula,Double> repeattable = new HashMap<PropositionalFormula, Double>();
		Iterator<PropositionalFormula> it = sig.iterator();
		while(it.hasNext()){
			PropositionalFormula f= it.next();
			if(w.getLiterals().contains(f)){
				repeattable.put(f, (double) 1);
				repeattable.put((PropositionalFormula) f.complement(), (double) 0);
			}
			else if(w.getLiterals().contains(f.complement())){
				repeattable.put(f, (double) 0);
				repeattable.put((PropositionalFormula) f.complement(), (double) 1);
			}
			else{
				repeattable.put(f, (double) 0);
				repeattable.put((PropositionalFormula) f.complement(), (double) 0);
			}
		}
		ArrayList<PropositionalFormula> newlist = new ArrayList<PropositionalFormula>();
		while(kblist.size()>0){
			ruleSelection(kblist,newlist,repeattable);
		}
		System.out.println(newlist);
		System.out.println(repeattable);
		kblist.addAll(newlist);
	}
	
	public static void ruleSelection(ArrayList<PropositionalFormula> kblist, ArrayList<PropositionalFormula> newlist, HashMap<PropositionalFormula, Double> map){
		PropositionalFormula fmax = kblist.get(0);
		double distancemax = DistanceMeasure.distance2(fmax,map);
		int max=0;
		for(int i=0; i<kblist.size();i++){
			if(DistanceMeasure.distance2(kblist.get(i),map)>distancemax){
				max=i;
			}
		}
		newlist.add(kblist.get(max));
		System.out.println(kblist.get(max));
		HashSet<PropositionalFormula> mapnewlit= (HashSet<PropositionalFormula>) kblist.get(max).getLiterals();
		kblist.remove(max);
		Set<PropositionalFormula> pfset =  map.keySet();
		Iterator<PropositionalFormula> itpfset = pfset.iterator();
		while(itpfset.hasNext()){
			PropositionalFormula pf=itpfset.next();
			if(map.get(pf)!=0){
				map.put(pf, map.get(pf)+1);
			}
		}
		Iterator<PropositionalFormula> it =mapnewlit.iterator();
		while(it.hasNext()){
			PropositionalFormula l=it.next();
			if(map.get(l)==0){
				map.put(l, (double)1);
			}
		}
	}

}
