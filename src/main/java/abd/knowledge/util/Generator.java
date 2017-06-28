package abd.knowledge.util;

import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.Random;

import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;

public class Generator {
	
      protected static int nb_var = 9;
      protected static int nb_formulas = 20;
      protected static int nb_length = 4;

	  public static final void main(String... aArgs) throws IOException{
		    log("Generating 100 random formulas knowledge base with 26 variables.");
		    
//		    int nb_var = 26;
//		    int nb_formulas = 100;
//		    int nb_length = 6;

		    
			PlParser parser = new PlParser();
			SatSolver.setDefaultSolver(new Sat4jSolver());
		    int count =0;
		    for(int i =100 ; i<200;i++){
		    	String name = String.format("./generator/%1$02d/Data-%1$02d-%2$02d-%3$03d.txt", nb_var, nb_formulas,i);
		    	generator(name);
		    	PlBeliefSet kb = parser.parseBeliefBaseFromFile(name);
		    	//System.out.println(kb.size());
		    	if(!kb.isConsistent()){
		    		System.out.println("inconsistent");
		    		i=i-1;
		    	}
		    		
		    	count++;
		    }
		    
		    System.out.println("finished. count = "+ count);
	  }
	  
	  public static void generator(String name) throws IOException{
		  
		  //Writer writer = new FileWriter("/home/yifan/workspace_eclipse/iterativeTab/kbset/generator_5_5/generator9.txt");
		  
		  Writer writer = new FileWriter(name);
		    Random randomGenerator = new Random();
		    for (int idx = 1; idx <= nb_formulas; ++idx){
		      int length = randomGenerator.nextInt(nb_length);
		      //log("Generated length: " + length);
		      if(length > 2){
		    	  for(int i=0;i<length; i++){
		    		  int var = randomGenerator.nextInt(nb_var);
		    		  boolean sign= randomGenerator.nextBoolean(); 
		    		  boolean connector;
	    			  if(sign)
	    				  writer.write("p" + var + " " );
	    			  else
	    				  writer.write("!p"+ var + " ");
		    		  if(i!=length-1){
		    			  connector =  randomGenerator.nextBoolean(); 
//		    			  if(connector)
//		    				  writer.write("&& ");
//		    			  else
//		    				  writer.write("|| ");
		    			  writer.write("|| ");
		    		  }
		    			  
		    	  }
		    	  writer.write("\n");
		      }
		      else
		    	  idx--;
		    }
		    writer.close();
	
	  }

		  
		  private static void log(String aMessage){
		    System.out.println(aMessage);
		  }
}
	  
