package abd.tableau.aliseda;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.Vector;

import net.sf.tweety.commons.ParserException;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import abd.knowledge.util.DistanceMeasure;

public class PriorOrder {

	public static void main(String[] args) throws FileNotFoundException, ParserException, IOException {
		// Create a pl knowledge base
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
	
	public static void sortFormula(ArrayList kb, PropositionalFormula w){
		for (int i= kb.size()-1; i>=0; i--)
		{
			for (int j=1;j<=i;j++)
			{
				if(DistanceMeasure.distance((PropositionalFormula) kb.get(j-1),w) < DistanceMeasure.distance((PropositionalFormula)kb.get(j),w))
				{
					PropositionalFormula temp = (PropositionalFormula) kb.get(j-1);
					kb.set(j-1, kb.get(j));
					kb.set(j, temp);
				}
			}
		}
	}

}
