package abd.tableau.iterative;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import javax.print.attribute.HashAttributeSet;

import com.sun.org.apache.bcel.internal.util.BCELifier;

import scala.Array;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

/* And Or connected semantic tableau */

public class IteGraph {
 
	protected AONode root = null;
    protected Vector<AONode> nodes = new Vector<AONode>();
    protected Vector<Edge> edges = new Vector<Edge>();

    protected HashMap<PropositionalFormula, Vector<PropositionalFormula>> dict;
    protected ArrayList<PropositionalFormula> hypotheses;
    protected ArrayList<Conjunction> hypotheses_bis;
    
    protected HashSet<PropositionalFormula> resolution = new HashSet<PropositionalFormula>();
    
    protected HashSet<PropositionalFormula> base_model = new HashSet<PropositionalFormula>();
	protected HashSet<PropositionalFormula> fusion_model = new HashSet<PropositionalFormula>();
    
	protected HashMap<Set<PropositionalFormula>, Conjunction> explanations = new HashMap<Set<PropositionalFormula>, Conjunction>();
	
	public void smConstrctTree(AONode rootnode){
		// BFS uses Queue data structure
		// semantic minimal explanation
		Queue queue = new LinkedList<AONode>();
		queue.add(rootnode);

		rootnode.visited = true;
		while(!queue.isEmpty()) {
			AONode node = (AONode)queue.remove();
			AONode child=null;
			
			// generate the hypotheses base.
			if(node.distance == 4){
				ArrayList<AONode> obs = getNodeatDist(1);
				//ArrayList<AONode> base = getNodeatDist(3);
				for(int i = 0; i< obs.size(); i++){
					AONode temp = obs.get(i);
					ArrayList<AONode> chs = new ArrayList<AONode>();
					if(temp.hasChildren()){
						chs = temp.getChildren();
					}else{
						chs.add(temp);
					}
					
					if(i==0){
						//initiate explanation
						for(int j=0; j< chs.size();j++){
							explanations.put(chs.get(j).model, chs.get(j).hyps);
						}
					}else{
						HashMap<Set<PropositionalFormula>, Conjunction> temp_exp = new HashMap<Set<PropositionalFormula>, Conjunction>();
						Set<Set<PropositionalFormula>> keys = explanations.keySet();
						
						List<Set<PropositionalFormula>> keysarray =new ArrayList<Set<PropositionalFormula>>(keys);
						for(int k = 0;k<chs.size();k++){
							Set<PropositionalFormula> m = chs.get(k).model;		
							Conjunction hch = chs.get(k).hyps;

							for(int ind =0;ind<keysarray.size();ind++){
								Set<PropositionalFormula> mexp = keysarray.get(ind);
								if(!contradictModel(m,mexp)){
									Conjunction th = explanations.get(mexp);
									Conjunction nth = th.combineWithAnd(hch);
									Set<PropositionalFormula> newModel = new HashSet<PropositionalFormula>(); 
									newModel.addAll(mexp);
									newModel.addAll(m);
									temp_exp.put(newModel, new Conjunction(nth.getLiterals()));
								}
							}
						}
						explanations.clear();
						explanations.putAll(temp_exp);
					}
				}
			}
			
			if(node.termination){
				node.visited = true;
			}else{
				if(node.status){
					node.visited = true;
					// and node 
	    			PropositionalFormula pf = node.getLiteral();

	    			node.setModel(pf);
	    			ArrayList<PropositionalFormula> resolits = new ArrayList<PropositionalFormula>();
    				Set<PropositionalFormula> lits = pf.getLiterals();
    				for(PropositionalFormula l : lits){
    					
    					AONode newnode = new AONode(l);
    					newnode.setOrNode();

    					if(node.getPredecessor()!= null && node.getPredecessor().getLiteral().equals(l.complement())){
    						newnode.setTermination();
    					}else{
    						resolits.add((PropositionalFormula)l.complement());
    					}
    					newnode.setPredecessor(node);
    					newnode.distance = node.distance+1;
    					
    					// new node copy the predecessor's rule list
    					newnode.setAppliedRules(node.getAppliedRules());
    					newnode.setLeftRules(node.getLeftRules());
    					newnode.setRule(node.getRule());
    					
    					// new node copy the model and hypotheses
    					newnode.copyModel(node.getModel());
    					if(!newnode.updateModel()){
    						newnode.setTermination();
    					}
    					// model is the complement of the literals that appear in  a node
    					if(!newnode.termination){
    						node.hyps.add((PropositionalFormula)l.complement());
    					}
    					node.setChildren(newnode);

    					// add the edges between the parent and children
    					Edge e = new Edge(node, newnode);
    					edges.add(e);
    				}
    				
    				node.setResolution(resolits);
    				if(node.getTermination()&& node.distance!=0){
    					node.getPredecessor().setTermination();
    					queue.removeAll(node.getPredecessor().getChildren());
    					node.getPredecessor().removeChildren();
    				}else{
        				ArrayList<AONode> children = node.getChildren();
    					for(int i=0; i<children.size(); i++){
        					AONode ch = children.get(i);
        					ch.copyResolution(node.getResolution());
        					queue.add(ch);
        					nodes.add(ch);
    					}
    					updateExplanations(node);
    				}    				
				}else{
	    			// or node, add new clause to the node 
					node.visited = true;
	    			PropositionalFormula pf = node.getLiteral();
	    			if(pf.isLiteral()){
	    				PropositionalFormula comp_pf = (PropositionalFormula)pf.complement();
	    				Vector<PropositionalFormula> values= dict.get(comp_pf);
	    				if(values!=null){
	    					for(int i=0;i<values.size();i++){
 
	    						PropositionalFormula rf = values.elementAt(i);
    						
	    						HashSet<PropositionalFormula> applied = node.getAppliedRules();

	    						if(node.getAppliedRules().contains(rf)){
	    							break;
	    						}
	    						// add every formula as a new alterantive node
	    						// set as and node
	    						AONode newnode = new AONode(values.elementAt(i));
	    						newnode.setRule(values.elementAt(i));
	        					newnode.setAndNode();

	        					newnode.setPredecessor(node);
	        					newnode.distance = node.distance+1;
	        					
	        					// new node copy the predecessor's rule list
	        					newnode.setAppliedRules(node.getAppliedRules());
	        					newnode.setLeftRules(node.getLeftRules());
	        					newnode.addAppliedRule(rf);
	        					newnode.deleteLeftRule(rf);
	        					newnode.setRule(node.getRule());
	        					
	        					// new node copy the model and hypotheses
	        					newnode.copyModel(node.getModel());
	        					
	        					newnode.copyResolution(node.getResolution());
	        					
	        					node.setChildren(newnode);
	        					// add the edges between the parent and children
	        					Edge e = new Edge(node, newnode);
	        					edges.add(e);
	        					
	        					
	        					nodes.add(newnode);
	        					queue.add(newnode);
	        					
	    					}
	    				}
	    			}
					
				}
			}

		}

	}
	
	
	private void updateExplanations(AONode node) {
		Set<Set<PropositionalFormula>> keys = explanations.keySet();
		Iterator it = keys.iterator();
		while(it.hasNext()){
			Set<PropositionalFormula> mexp = (Set<PropositionalFormula>)it.next();
			Set<PropositionalFormula> mnode = node.model;
			if(mexp.containsAll(mnode)){
				Conjunction newexp = new Conjunction(node.hyps);
				newexp.addAll(explanations.get(mexp).getLiterals());
				PropositionalFormula f = node.getPredecessor().getLiteral();
				Set<PropositionalFormula> lits = newexp.getLiterals();
				lits.remove((PropositionalFormula)f.complement());
				newexp = new Conjunction(lits);
				mnode.addAll(mexp);
				explanations.put(mnode, newexp);
			}
		}
		Iterator it1 = explanations.keySet().iterator();
		ArrayList<Set<PropositionalFormula>> toDelete = new ArrayList<Set<PropositionalFormula>>();

		while(it1.hasNext()){
			Set<PropositionalFormula> m1 = (Set<PropositionalFormula>)it1.next();
			Set<PropositionalFormula> e1 = explanations.get(m1).getLiterals();
			Iterator it2 = explanations.keySet().iterator();
			while(it2.hasNext()){
				Set<PropositionalFormula> m2 = (Set<PropositionalFormula>)it2.next();
				Set<PropositionalFormula> e2 = explanations.get(m2).getLiterals();
				if(!(e1.containsAll(e2) && e2.containsAll(e1))){
					if(e1.containsAll(e2) && !toDelete.contains(m1)){
						// delete e1
						toDelete.add(m1);
					}else if(e2.containsAll(e1) && !toDelete.contains(m2)){
						// delete e2
						toDelete.add(m2);
					}
				}
			}
		}
		for (Set<PropositionalFormula> k : toDelete){
			explanations.remove(k);
		}

	}


	private boolean contradictModel(Set<PropositionalFormula> m,
			Set<PropositionalFormula> mexp) {
		Iterator it = m.iterator();
		while(it.hasNext()){
			PropositionalFormula element = (PropositionalFormula)it.next();
			if(mexp.contains(element.complement())){
				return true;
			}
		}
		return false;
	}


	private ArrayList<AONode> getNodeatDist(int i) {
		ArrayList<AONode> res = new ArrayList<AONode>();
		for(int ind =0; ind<nodes.size(); ind++){
			if(nodes.elementAt(ind).distance==i){
				res.add(nodes.elementAt(ind));
			}
		}
		
		return res;
	}


	public void bfconstrctTree(AONode rootnode){
		// BFS uses Queue data structure
		Queue queue = new LinkedList<AONode>();
		queue.add(rootnode);
		rootnode.visited = true;
		while(!queue.isEmpty()) {
			AONode node = (AONode)queue.remove();
			AONode child=null;
			if(node.termination){
				node.visited = true;
			}else{
				if(node.status){
					node.visited = true;
					// and node 
	    			PropositionalFormula pf = node.getLiteral();

	    			node.setModel(pf);
	    			ArrayList<PropositionalFormula> resolits = new ArrayList<PropositionalFormula>();
    				Set<PropositionalFormula> lits = pf.getLiterals();
    				for(PropositionalFormula l : lits){
    					
    					AONode newnode = new AONode(l);
    					newnode.setOrNode();

    					if(node.getPredecessor()!= null && node.getPredecessor().getLiteral().equals(l.complement())){
    						System.out.println("contradiction");
    						newnode.setTermination();
    					}else{
    						resolits.add((PropositionalFormula)l.complement());
    					}
    					newnode.setPredecessor(node);
    					
    					
    					// new node copy the predecessor's rule list
    					newnode.setAppliedRules(node.getAppliedRules());
    					newnode.setLeftRules(node.getLeftRules());
    					newnode.setRule(node.getRule());
    					
    					// new node copy the model and hypotheses
    					newnode.copyModel(node.getModel());
    					if(!newnode.updateModel()){
    						newnode.setTermination();
    					}
    					// model is the complement of the literals that appear in  a node
    					// considering sibling node
    					//sib.
    					
    					node.setChildren(newnode);

    					// add the edges between the parent and children
    					Edge e = new Edge(node, newnode);
    					edges.add(e);
    				}
    				
    				node.setResolution(resolits);
    				if(node.getTermination()){
    					node.getPredecessor().setTermination();
    					queue.removeAll(node.getPredecessor().getChildren());
    					node.getPredecessor().removeChildren();
    				}else{
        				ArrayList<AONode> children = node.getChildren();
    					for(int i=0; i<children.size(); i++){
        					AONode ch = children.get(i);
        					ch.copyResolution(node.getResolution());
        					queue.add(ch);
        					nodes.add(ch);
    					}
    				}    				
				}else{
	    			// or node, add new clause to the node 
					node.visited = true;
	    			PropositionalFormula pf = node.getLiteral();
	    			if(pf.isLiteral()){
	    				PropositionalFormula comp_pf = (PropositionalFormula)pf.complement();
	    				Vector<PropositionalFormula> values= dict.get(comp_pf);
	    				if(values!=null){
	    					for(int i=0;i<values.size();i++){
	    						System.out.println("literal "+ pf +" in formula "+values.elementAt(i));
	    						PropositionalFormula rf = values.elementAt(i);
	    						System.out.println("selected formula" + rf);
	    						
	    						HashSet<PropositionalFormula> applied = node.getAppliedRules();
	    						for(PropositionalFormula ap : applied){
	    							System.out.println("applied rules " + ap);
	    						}
	    						
	    						if(node.getAppliedRules().contains(rf)){
	    							
	    							System.out.println("already applied");
	    							break;
	    							
	    						}
	    						// add every formula as a new alterantive node
	    						// set as and node
	    						AONode newnode = new AONode(values.elementAt(i));
	    						newnode.setRule(values.elementAt(i));
	        					newnode.setAndNode();

	        					newnode.setPredecessor(node);
	        					
	        					
	        					// new node copy the predecessor's rule list
	        					newnode.setAppliedRules(node.getAppliedRules());
	        					newnode.setLeftRules(node.getLeftRules());
	        					newnode.addAppliedRule(rf);
	        					newnode.deleteLeftRule(rf);
	        					newnode.setRule(node.getRule());
	        					
	        					// new node copy the model and hypotheses
	        					newnode.copyModel(node.getModel());
	        					
	        					newnode.copyResolution(node.getResolution());
	        					
	        					node.setChildren(newnode);
	        					// add the edges between the parent and children
	        					Edge e = new Edge(node, newnode);
	        					edges.add(e);
	        					
	        					
	        					nodes.add(newnode);
	        					queue.add(newnode);
	        					
	    					}
	    				}
	    			}
					
				}
			}
		}
		// Clear visited property of nodes
	}
	
	
    public void constructTree(AONode node){
    	// recursive method
    	// In this way, we prioritize the depth of a branch
    	if(!node.termination){
    		if(node.status){
    			System.out.println("and");
    			// and node, disjunct literals are separated
    			// create a  new node  for every literals 
    			PropositionalFormula pf = node.getLiteral();
    			System.out.println("root "+pf);
    			node.setModel(pf);
    			
    			ArrayList<PropositionalFormula> resolits = new ArrayList<PropositionalFormula>();
				Set<PropositionalFormula> lits = pf.getLiterals();
				for(PropositionalFormula l : lits){
					
					AONode newnode = new AONode(l);
					newnode.setOrNode();

					if(node.getPredecessor()!= null && node.getPredecessor().getLiteral().equals(l.complement())){
						System.out.println("contradiction");
						newnode.setTermination();
					}else{
						resolits.add((PropositionalFormula)l.complement());
					}
					newnode.setPredecessor(node);
					
					
					// new node copy the predecessor's rule list
					newnode.setAppliedRules(node.getAppliedRules());
					newnode.setLeftRules(node.getLeftRules());
					newnode.setRule(node.getRule());
					
					// new node copy the model and hypotheses
					newnode.copyModel(node.getModel());
					if(!newnode.updateModel()){
						newnode.setTermination();
					}
					// model is the complement of the literals that appear in  a node
					// considering sibling node
					node.setChildren(newnode);
					nodes.add(newnode);
					// add the edges between the parent and children
					Edge e = new Edge(node, newnode);
					edges.add(e);
				}
    				
				node.setResolution(resolits);
				
				ArrayList<AONode> children = node.getChildren();
				if(node.getTermination()){
					for(int i=0; i<children.size(); i++){
    					AONode ch = children.get(i);
    					ch.setTermination();
    				}
				}else{
					for(int i=0; i<children.size(); i++){
    					AONode ch = children.get(i);
    					ch.copyResolution(node.getResolution());
    					if(!ch.getTermination())
    						constructTree(ch);
    				}
				}    		    
    		}else{
    			System.out.println("or");

    			// or node, add new clause to the node 
    			PropositionalFormula pf = node.getLiteral();
    			if(pf.isLiteral()){
    				PropositionalFormula comp_pf = (PropositionalFormula)pf.complement();
    				Vector<PropositionalFormula> values= dict.get(comp_pf);
    				if(values!=null){
    					for(int i=0;i<values.size();i++){
    						System.out.println("literal "+ pf +" in formula "+values.elementAt(i));
    						PropositionalFormula rf = values.elementAt(i);
    						System.out.println("selected formula" + rf);
    						
    						HashSet<PropositionalFormula> applied = node.getAppliedRules();
    						for(PropositionalFormula ap : applied){
    							System.out.println("applied rules " + ap);
    						}
    						
    						if(node.getAppliedRules().contains(rf)){
    							
    							System.out.println("already applied");
    							break;
    							
    						}
    						// add every formula as a new alterantive node
    						// set as and node
    						AONode newnode = new AONode(values.elementAt(i));
    						newnode.setRule(values.elementAt(i));
        					newnode.setAndNode();

        					newnode.setPredecessor(node);
        					
        					
        					// new node copy the predecessor's rule list
        					newnode.setAppliedRules(node.getAppliedRules());
        					newnode.setLeftRules(node.getLeftRules());
        					newnode.addAppliedRule(rf);
        					newnode.deleteLeftRule(rf);
        					newnode.setRule(node.getRule());
        					
        					// new node copy the model and hypotheses
        					newnode.copyModel(node.getModel());
        					
        					newnode.copyResolution(node.getResolution());
        					
        					node.setChildren(newnode);
        					// add the edges between the parent and children
        					Edge e = new Edge(node, newnode);
        					edges.add(e);
        					
        					
        					nodes.add(newnode);
        					// recursive 
        					constructTree(newnode);
    					}
    				}else{
    					node.setTermination();
    				}
    			}
    		}
    	}
    }
     
    public double[][] getAdjacencyMatrix() {
        double[][] adjMatrix = new double[nodes.size()][nodes.size()];
         
        for(int i = 0; i < nodes.size(); i++)
            for(int j = 0; j < nodes.size(); j++)
                if(i == j)
                    adjMatrix[i][j] = 0;
                else
                    adjMatrix[i][j] = Double.POSITIVE_INFINITY;
                 
        for(int i = 0; i < nodes.size(); i++) {
        	AONode node = nodes.elementAt(i);
            //System.out.println("Current node: " + node);
             
            for(int j = 0; j < edges.size(); j++) {
                Edge edge = edges.elementAt(j);
                 
                if(edge.a == node) {
                    int indexOfNeighbor = nodes.indexOf(edge.b);
                     
                    adjMatrix[i][indexOfNeighbor] = edge.weight;
                }
            }
        }
         
        return adjMatrix;
    }
     
    public int indexOf(AndNode a) {
        for(int i = 0; i < nodes.size(); i++)
//            if(nodes.elementAt(i).data.equals(a.data))
                return i;
                 
        return -1;
    }
     
    public Vector<AONode> getNodes() {
        return nodes;
    }
     
    public Vector<Edge> getEdges() {
        return edges;
    }
     
    public AONode getNodeAt(int i) {
        return nodes.elementAt(i);
    }
     
    public void unvisitAllNodes() {
        for(int i = 0; i < nodes.size(); i++)
            nodes.elementAt(i).unvisit();
    }
     
    public Vector<AONode> getNeighbors(AONode a) {
        Vector<AONode> neighbors = new Vector<AONode>();
         
        for(int i = 0; i < edges.size(); i++) {
            Edge edge = edges.elementAt(i);
             
            if(edge.a == a)
                neighbors.add(edge.b);
        }       
        return neighbors;
    }
     
    public int addNode(AONode a) {
        nodes.add(a);
         
        return nodes.size() - 1;
    }
     
    public void addEdge(Edge a) {
        edges.add(a);
    }
     
    public void printNodes() {
        System.out.println(nodes);
    }
     
    public void printEdges() {
        System.out.println(edges);
    }

	public void setRoot(AONode root) {
		this.root = root;
		nodes.addElement(root);
		//root.initResolution();
		
		resolution.addAll(root.getLeftRules());
		Set<PropositionalFormula> toRemove = new HashSet<PropositionalFormula>();
		Iterator<PropositionalFormula> it = resolution.iterator();
		while(it.hasNext()){
			PropositionalFormula pf = it.next();
			for(PropositionalFormula ol : root.f.getLiterals()){
				if(pf.getLiterals().contains(ol.complement())){
					toRemove.add(pf);
					break;
				}
			}
		}
		resolution.removeAll(toRemove);
		PLResolution.plresolution(resolution,root.f);
		root.addResolution(new ArrayList<PropositionalFormula>(resolution));
	}

	public void setLiteralMap(
			HashMap<PropositionalFormula, Vector<PropositionalFormula>> dict) {
		this.dict = dict;
	}

	public void startExpansion() {
		//constructTree(root);
		//bfconstrctTree(root);
		smConstrctTree(root);
	}
	
	public void toDot(String filename){
		try {
			String content = "This is the content to write into file";

			File file = new File("./output/"+filename+".dot");

			// if file doesnt exists, then create it
			if (!file.exists()) {
				file.createNewFile();
			}

			FileWriter fw = new FileWriter(file.getAbsoluteFile());
			BufferedWriter bw = new BufferedWriter(fw);
			
			//bw.write(content);
			//print nodes information and edges information
			for(int i =0;i<nodes.size();i++){
				bw.write(Integer.toString(nodes.indexOf(nodes.elementAt(i)))+ "  " + "[label=\"" + nodes.elementAt(i).getLiteral().toString()+"\"];\n");
			}
			for(int j=0;j<edges.size();j++){
				Edge e = edges.get(j);
				int na = nodes.indexOf(e.a);
				int nb = nodes.indexOf(e.b);
				String se =e.a.getLiteral().toString();
				String ee = e.b.getLiteral().toString();
				String final_se = se.replace("||", "_or_").replace("!","n");
				String final_ee = ee.replace("||", "_or_").replace("!","n");
				//bw.write(Integer.toString(na).concat("_"+final_se)+ " -> " + Integer.toString(nb).concat("_"+final_ee));
				bw.write(Integer.toString(na)+ " -> " + Integer.toString(nb));

				// add conditions to separate dotted line and concrete line
				if(!e.a.status)
					bw.write(" [style = dotted];");
				else
					bw.write(";");
				bw.write("\n");
			}
			
			bw.close();

			System.out.println("Done");

		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public void generateExplanation(){
		hypotheses = new ArrayList<PropositionalFormula>();
		// using breadth first search to generate sub tree		
		// generate minimal semantic explanations.
		topdownHyp(root);
		// generate minimal syntatic explanations
        oneStepGeneration(root);
		
		//top down search
        tdsearch(root);

		
	}
	
	public void tdsearch(AONode node){
		ArrayList<AONode> ch = node.getChildren();
	}

	private void topdownHyp(AONode node) {
		// to do rewritten using java Queue
		// or node, list all possible hyps
		ArrayList<AONode> ch = node.getChildren();
		if(ch!=null && ch.size()>0){
			if(node.status==false){
				Iterator<AONode> it = ch.iterator();
				while(it.hasNext()){
					AONode anode = it.next();
					if(!anode.termination){
						anode.copyHyp();
						topdownHyp(anode);
					}
				}
			}else{
			// and node, combination of complement of each literals
				Iterator<AONode> it = ch.iterator();
				Conjunction h = new Conjunction();
				while(it.hasNext()){
					AONode anode = it.next();
					if(!anode.termination)
						h.add((PropositionalFormula) anode.getLiteral().complement());
					topdownHyp(anode);
				}
				//node.setHyp(h);
			}
		}
		
	}
	
	//todo rewrite the generation part using minimal hitting set algo
	public void oneStepGeneration(AONode node){
		ArrayList<AONode> ch_root = node.getChildren();
		Iterator<AONode> it_ch = ch_root.iterator();
		int nb_obs = root.getLiteral().getLiterals().size();
		Vector<List<Conjunction>> conj = new Vector<List<Conjunction>>(nb_obs);
		int i=0;
		ArrayList<AONode> children_list = new ArrayList<AONode>();
		while(it_ch.hasNext()){
			AONode ch_node = it_ch.next();
			children_list.add(ch_node);
			if(ch_node.termination == true){
				ArrayList<Conjunction> ac = new ArrayList<Conjunction>();
				Conjunction c = new Conjunction();
				c.add((PropositionalFormula) ch_node.getLiteral().complement());
				ac.add(c);
				//conj.add(i, ac);
			}
			i++;
			fusion_model.addAll(ch_node.getModel());
		}
		
		for(AONode n : children_list){
			ArrayList<AONode> grandchildren = n.getChildren();
			if( grandchildren !=null){
				Iterator<AONode> it_gc = grandchildren.iterator();
			}
		}
		ArrayList<Conjunction> result = new ArrayList<Conjunction>();
		Conjunction current = new Conjunction();
		GeneratePermutations(conj, result, 0, current);
		hypotheses_bis = result;
	}
	
	
	public void GeneratePermutations(Vector<List<Conjunction>> Lists, List<Conjunction> result, int depth, Conjunction current)
	{
	    if(depth == Lists.size())
	    {
	       result.add(current);
	       return;
	     }

	    for(int i = 0; i < Lists.get(depth).size(); ++i)
	    {
	        GeneratePermutations(Lists, result, depth + 1, current.combineWithAnd(Lists.get(depth).get(i)));
	    }
	}
	

	public Collection<Conjunction> getExplanations() {
//		return hypotheses_bis;
		return explanations.values();
	}
	
	public float getTableauSize(){
		return nodes.size();
	}


	public HashSet<PropositionalFormula> getResolution() {
		return resolution;
	}
 
}
