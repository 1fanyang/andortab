package abd.tableau.aliseda;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import abd.datastructure.graph.TreeNode;
import abd.knowledge.util.MinHittingSet;
import abd.knowledge.util.SortedIntList;
import net.sf.tweety.commons.ParserException;
import net.sf.tweety.commons.Signature;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.Disjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import org.apache.commons.cli.*;

public class Aliseda {
	protected static PlParser plparser = new PlParser();
	public static void main(String[] args) throws ParserException, IOException{

		// command line argument parsing
		Options options = new Options();
		CommandLineParser parser = new DefaultParser();
		HelpFormatter formatter = new HelpFormatter();
		CommandLine cmd;

		Option knowledge = new Option("k", "knowledge", true, "input knowledge file path");
		knowledge.setRequired(true);
		options.addOption(knowledge);

		Option observation = new Option("o", "observation", true, "observation");
		observation.setRequired(true);
		options.addOption(observation);

		try {
			cmd = parser.parse(options, args);
		} catch (ParseException e) {
			System.out.println(e.getMessage());
			formatter.printHelp("utility-name", options);

			System.exit(1);
			return;
		}


		String knowledgePath = cmd.getOptionValue("knowledge");
		String obs = cmd.getOptionValue("observation");


		System.out.println(knowledgePath);
		System.out.println(obs);



//    		// test a single file
//		String file = "/home/yifan/plkb.txt";
//		PropositionalFormula obs = (PropositionalFormula) parser.parseFormula("w && d");
//
//		double[] rt = run(file, obs);
		PropositionalFormula obsFormula = (PropositionalFormula) plparser.parseFormula(obs);
		double[] result = run(knowledgePath,obsFormula);
	}


	public static double[] run(String name, PropositionalFormula observation) throws FileNotFoundException, ParserException, IOException{
		
		// Create a pl knowledge base

		String file= name;
		PlBeliefSet kb = plparser.parseBeliefBaseFromFile(file);
		
		PropositionalFormula obs = observation;
		
		// Set SAT solver
		SatSolver.setDefaultSolver(new Sat4jSolver());
		
		
		kb = new PlBeliefSet(kb.toCnf());
		
		// Get current time
		long start = System.nanoTime();
		
		
		// Initialization aliseda tableau
		AlisedaTableau tab = new AlisedaTableau();
		tab.addKb(kb);
		tab.addRoot(obs);
		
		// Expansion of the tableau
		tab.expansion();

		double nb_nodes = tab.getnbNodes();
		Vector<AlisedaNode> leaves = tab.getLeaves();
 
		for(int i=0; i<leaves.size(); i++){ 
			leaves.elementAt(i).removeRedundance(); 
		}
 
		
		// compute explanation using hitting set algo
		ArrayList confsets = new ArrayList();
		for(int i=0; i<leaves.size(); i++){
			SortedIntList cs = new SortedIntList();
			AlisedaNode n = leaves.elementAt(i);
			Vector<PropositionalFormula> lits = n.getLiterals();
			for(PropositionalFormula f:lits){
				cs.addSorted(f);
			}
			confsets.add(cs);
		}
        MinHittingSet hittingSets = new MinHittingSet(false, confsets);

        hittingSets.compute(100, 100);
        
        Vector<PropositionalFormula> hyp = new Vector<PropositionalFormula>();

        Iterator itHS = hittingSets.getMinHSAsIntLists().iterator();
        while(itHS.hasNext()) {
            //System.out.println();
            Conjunction h= new Conjunction();
            SortedIntList hs = (SortedIntList)itHS.next();
            
            Iterator itInt = hs.iterator();
            while(itInt.hasNext()) {
            	PropositionalFormula n = (PropositionalFormula)itInt.next();
            	h.add((PropositionalFormula) n.complement());
            }
            hyp.add(h);
        }
              
	// get Explanation
	Vector<PropositionalFormula> minimal = tab.getMiniamlExplantion(hyp);
	// Get elapsed time in milliseconds
	long elapsedTimeMillis = System.nanoTime()-start;

	PropositionalFormula negobs =(PropositionalFormula)obs.complement();
	for(int i=0; i<minimal.size(); i++){
		PropositionalFormula hypo = minimal.elementAt(i);
		System.out.println("minimal " +i + "  "+ hypo);
		// check the hypothesis 
		kb.add(hypo);
		System.out.println("hyp is "+kb.isConsistent()+" consistent wrt kb");
		kb.add(negobs);
		System.out.println("hyp is  "+ !kb.isConsistent()+" explanation");
		kb.remove(hypo);
		kb.remove(negobs);
	}
		

		
	// Get elapsed time in seconds
	// float elapsedTimeSec = elapsedTimeMillis/1000F;
	double elapsedTimeSec = elapsedTimeMillis/1000000F;

	
	System.out.println("elapsedTimeSec " +elapsedTimeSec);
	System.out.println("Finish");
	

	//return elapsedTimeSec;
	return new double[] {elapsedTimeSec, nb_nodes};
   }
}

