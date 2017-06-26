package abd.tableau.iterative;

import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Vector;

import scala.sys.Prop;
import net.sf.tweety.commons.ParserException;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

import org.apache.commons.cli.*;


public class IterativeMethod {

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
		PlParser parser = new PlParser();

		String file = name;
		PlBeliefSet kb = parser.parseBeliefBaseFromFile(file);

		PropositionalFormula obs = observation;
		// Set SAT solver
		SatSolver.setDefaultSolver(new Sat4jSolver());

		// consistency
		boolean consistency =kb.isConsistent();
		System.out.println("knowledge base is "+consistency+" consistent");
		if(!consistency){
			System.out.println("not a consistent kb. Stop");
			System.exit(0);
		}

		kb = new PlBeliefSet(kb.toCnf());

	
		HashMap<PropositionalFormula, Vector<PropositionalFormula>> dict = new HashMap<PropositionalFormula, Vector<PropositionalFormula>>();
		Iterator<PropositionalFormula> it = kb.iterator();
		while(it.hasNext()){
			PropositionalFormula f = it.next();
			Set<PropositionalFormula> s = f.getLiterals();
			for(PropositionalFormula a:s){
				Vector<PropositionalFormula> v = new Vector<PropositionalFormula>();
				v.add(f);
				if(dict.get(a)!= null){
					v.addAll(dict.get(a));
				}
				dict.put(a, v);
			}	
		}
	
		Set<PropositionalFormula> keys = dict.keySet();
	
		// Get current time
		//long start = System.currentTimeMillis();
		long start = System.nanoTime();
	
	
		IteGraph andortab = new IteGraph();
		PropositionalFormula obs_comp = (PropositionalFormula)obs.complement();
		AONode root = new AONode(obs_comp.toNnf());
		// set kb to root node
		Set<PropositionalFormula> k = kb.toCnf().getFormulas();

		//System.out.println("hello");
	
		HashSet<PropositionalFormula> kbrules = new HashSet<PropositionalFormula>();
		kbrules.addAll(k);
		root.setLeftRules(kbrules);
		root.setAndNode();
		root.distance = 0;
		andortab.setRoot(root);
	
		//System.out.println("hello resolution");
		HashSet<PropositionalFormula> resolution = andortab.getResolution();
		Iterator<PropositionalFormula> itreso =resolution.iterator();
		while(itreso.hasNext()){
			System.out.println(itreso.next());
		}
	
		andortab.setLiteralMap(dict);
		andortab.startExpansion();
	
	//	andortab.generateExplanation();
	//	

		double nb_node = andortab.getTableauSize();
		// Get elapsed time in milliseconds
		//long elapsedTimeMillis = System.currentTimeMillis()-start;
		long elapsedTimeMillis = System.nanoTime()-start;
	
	
		Collection<Conjunction> explanation =  andortab.getExplanations();

		// Get elapsed time in seconds
		//float elapsedTimeSec = elapsedTimeMillis/1000F;
		double elapsedTimeSec = elapsedTimeMillis/1000000F;
		System.out.println("elapsedTimeMillis " +elapsedTimeSec);
		PropositionalFormula negobs =(PropositionalFormula)obs.complement();
		int ind=0;
		if(explanation.isEmpty()){
			System.out.println("no explanations");
		}else{
			Iterator<Conjunction> it_exp = explanation.iterator();
		
			while(it_exp.hasNext()){
				PropositionalFormula hypo = it_exp.next();
				ind++;
				if(ind!=2)
				System.out.println("explanation is: "+ hypo);
			}
		}

		System.out.println("Finish");

		return new double[] {elapsedTimeSec,nb_node};

	}

}
