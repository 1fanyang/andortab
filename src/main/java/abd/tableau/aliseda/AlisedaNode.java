package abd.tableau.aliseda;

import java.io.IOException;
import java.util.*;

import abd.datastructure.graph.*;
import net.sf.tweety.logics.pl.parser.PlParser;
import net.sf.tweety.logics.pl.syntax.*;

/* Node in semantic tableau */
public class AlisedaNode extends Node implements Cloneable{

	// set of atomic propositions
	private Vector<PropositionalFormula> literals;
	// set of formulas
	private AlisedaNode ancestor;
	private Vector<AlisedaNode> successors;

	
	// inconsistent flag (closed branch)
	boolean cflag;
	
	AlisedaNode(){
		super("aliseda");
		cflag = true;
		literals = new Vector<PropositionalFormula>();
		successors = new Vector<AlisedaNode>();
	}
	
	AlisedaNode(AlisedaNode n){
		super("aliseda");
		literals=n.getLiterals();
		ancestor = n.getParent();
		successors = n.getChildren();
		cflag = true;
	}


	protected Vector<PropositionalFormula> getLiterals() {
		return literals;
	}

	AlisedaNode(String n) {
		super(n);
		cflag=true;
	}
	public boolean hasChild(){
		if(successors.isEmpty())
			return false;
		else
			return true;
	}
 
	public Vector<AlisedaNode> getChildren(){
		return successors;
	}
	
	public void setChildren(AlisedaNode n){
		successors.addElement(n);
	}
	
	public void setChildren(Vector<AlisedaNode> vn){
		for(int i=0; i<vn.size();i++)
			successors.addElement(vn.elementAt(i));
	}
	
	public AlisedaNode getParent(){
		return ancestor;
	}
	
	public void setParent(AlisedaNode p){
		ancestor = p;
	}


	public boolean getcFlag() {
		return cflag;
	}

	
	public AlisedaNode duplicateNode(){
		AlisedaNode nnode = new AlisedaNode();
		for(int i=0; i<literals.size(); i++){
			nnode.addLiterals(literals.elementAt(i));
		}
		return nnode;
	}
	
	public void addLiterals(PropositionalFormula f) {

		literals.addElement(f);
	}

        public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }
    
    
	public void init(Set<PropositionalFormula> o) {
		literals = new Vector<PropositionalFormula>();
		Iterator<PropositionalFormula> it = o.iterator();
		ancestor = null;
		successors = new Vector<AlisedaNode>();
		
		while(it.hasNext()){
			AlisedaNode n = new AlisedaNode();
			n.addLiterals((PropositionalFormula) it.next().complement());
//			literals.add((PropositionalFormula) it.next().complement());
			n.setParent(this);
			this.setChildren(n);
		}
		
		
	}
	
	public void checkConsistency(){
		outerloop:
		for(int i=0; i< literals.size();i++){
			for(int j=i; j< literals.size();j++){
				if(literals.elementAt(i).equals(literals.elementAt(j).complement())){
					cflag = false;
					break outerloop;
				}
			}
		}
	}
	
	public boolean isConsistent(){
		return cflag;
	}

	public void updateliterals(Set<PropositionalFormula> l){
		literals.addAll(l);
	}

	public void printleaves(){
		for(int i=0; i<literals.size(); i++){
			System.out.print(literals.elementAt(i));
		}
		System.out.println();
	}
	
	public void removeRedundance(){
		for(int i=literals.size()-1; i>=0; i--){
			for(int j=0; j< i ;j++){
				if(literals.elementAt(j).equals(literals.elementAt(i))){
					literals.removeElementAt(i);
					break;
				}
			}
		}
	}

	public void printChildren() {
		System.out.print("node :");
		for(int i=0;i<literals.size();i++){
			System.out.print(literals.elementAt(i)+" ");
		}
		System.out.println();	
		System.out.println(" children: ");
		for(int i=0; i<successors.size();i++){
			successors.elementAt(i).printChildren();
		}
	}
}
