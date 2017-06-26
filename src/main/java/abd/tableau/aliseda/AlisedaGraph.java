package abd.tableau.aliseda;

import java.util.ArrayList;
import java.util.Set;
import java.util.Vector;

import abd.datastructure.graph.*;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.syntax.Disjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

public class AlisedaGraph extends Graph{
	
	private AlisedaNode root;
	private Vector<AlisedaNode> nodes;
	

	public AlisedaGraph() {
		root = new AlisedaNode();
		nodes = new Vector<AlisedaNode>();
	}
	
	void initilization(AlisedaNode rootnode){
		root = rootnode;
		nodes.addElement(root);
		nodes.addAll(root.getChildren());
	}

	Vector<AlisedaNode> getAllLeaves(){
		Vector<AlisedaNode> leaves = new Vector<AlisedaNode>();
		int num = nodes.size();
		for(int i=0; i<num; i++){
			if(! nodes.get(i).hasChild() && nodes.get(i).getcFlag())
				leaves.add(nodes.get(i));
		}
		return leaves;
	}

	public int getNodesize(){
		return nodes.size();
	}
	public void expansion(PropositionalFormula pf){
		// get all leave nodes
		Vector<AlisedaNode> leaves = getAllLeaves();
		
		for(int i=0; i< leaves.size(); i++){
			
			 PropositionalFormula f = pf.toDnf().collapseAssociativeFormulas();
			 
			 if(f instanceof Disjunction) {
				 Disjunction d = (Disjunction) f;
				 for(PropositionalFormula c : d) {
 
					 AlisedaNode n = leaves.elementAt(i).duplicateNode();
					 n.updateliterals(c.getLiterals());
					 n.checkConsistency();
					 n.setParent(leaves.elementAt(i));
					 leaves.elementAt(i).setChildren(n);
					 nodes.addElement(n);
				 }
			 }
		}
		
		
	}

	public void printAllNodes() {
		System.out.println("root");
		Vector<PropositionalFormula> lits = root.getLiterals();
		for(int i=0;i<lits.size();i++){
			System.out.print(lits.elementAt(i)+" ");
		}
		System.out.println();	
		root.printChildren();
	}
	
	public void printTableau(){
		for(int i=0; i<nodes.size(); i++){
			System.out.println("No:" + i);
			nodes.elementAt(i).printleaves();
			for(int j=0;j<nodes.elementAt(i).getChildren().size();j++){
				System.out.println("children: " + nodes.indexOf(nodes.elementAt(i).getChildren().elementAt(j)));
			}
			
		}
	}

}
