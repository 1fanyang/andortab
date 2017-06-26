package abd.datastructure.graph;

import java.util.Collection;
import java.util.Vector;
/*
 * A node is an abstract class representing basic vertex
 */

// tableau node
public class Node {

	// label for Node
	String name;
	// parent node
	protected Node ancestor;
	// children nodes
	protected Vector<Node> successor;
	
	private Graph container;
	
	/**
	 * length of shortest path from source
	 */
	public int distance; 
	
	// constructor of a node
	protected Node(String n){
		name = n;
	}

	public int compareTo(Node w) {
		// TODO Auto-generated method stub
		if(this.name.equals(w.name))
			return 1;
		else
			return -1;
	}
	
	void addParent(Node p){
		ancestor = p;
	}
	
	void addChild(Node c){
		successor.add(c);
	}
	
	void addChildren(Collection<? extends Node> ch){
		successor.addAll(ch);
	}
	
	private Vector<Node> getChildren(){
		return successor;
	}
	
	public boolean hasChild() {
		if(successor.isEmpty())
			return false;
		else 
			return true;
	}
	public Vector<Node> leafnodes() {
		return successor;
	}
	
    public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }
}
