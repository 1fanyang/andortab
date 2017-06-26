package abd.tableau.iterative;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.Disjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

/* And-Or node*/

public class AONode implements Comparable<AONode> {
    
    protected HashSet<PropositionalFormula> appliedrules;
    protected HashSet<PropositionalFormula> leftrules;
    
    protected PropositionalFormula rule;
    protected PropositionalFormula f;
    
    protected boolean status = true; // true and node, false or node
    protected boolean termination = false; // terminal node
    
    
    
    // model literals list 
    protected HashSet<PropositionalFormula> model = new HashSet<PropositionalFormula>();
    // hypotheses list
    //protected HashMap<PropositionalFormula, PropositionalFormula> hyps = new HashMap<PropositionalFormula,PropositionalFormula>();
    protected Conjunction hyps = new Conjunction();
    // consistency  list
    protected HashMap<PropositionalFormula, Integer> resolution = new HashMap<PropositionalFormula, Integer>();
    
    protected boolean visited;
    public Integer index = null;
    public Integer lowlink = null;
    public double distance = Double.POSITIVE_INFINITY;
    public AONode predecessor = null;
    public ArrayList<AONode> children = null;
    public ArrayList<AONode> siblings = null;
     
    public AONode(PropositionalFormula f) {
        this.f = f;
        appliedrules = new HashSet<PropositionalFormula>();
        leftrules= new HashSet<PropositionalFormula>();
    }
     
    public AONode() {
        appliedrules = new HashSet<PropositionalFormula>();
        leftrules= new HashSet<PropositionalFormula>();
    }
     
    public boolean isVisited() {
        return visited;
    }
     
    public void visit() {
        visited = true;
    }
     
    public void unvisit() {
        visited = false;
    }
     
    public int compareTo(AONode ob) {
    	PropositionalFormula fb = ob.getLiteral();
        if(fb.isLiteral()){
        	return fb.toString().compareTo(f.toString());
        }else
        	return 0;
    }
     
    public PropositionalFormula getLiteral() {
		return f;
	}

	public String toString() {
        return f.toString();
    }

	public void setOrNode() {
		status = false;
	}
	
	public void setAndNode(){
		status = true;
	}

	public void setRule(PropositionalFormula rule) {
		this.rule = rule;
	}
	
	public void setPredecessor(AONode pred){
		this.predecessor = pred;
	}
	
	public AONode getPredecessor(){
		return predecessor;
	}
	
	public void setAppliedRules(HashSet<PropositionalFormula> applied){
		for(PropositionalFormula f : applied){
			appliedrules.add(f);
		}
	}
	
	public HashSet<PropositionalFormula> getAppliedRules(){
		return appliedrules;
	}
	
	public void setLeftRules(HashSet<PropositionalFormula> left){
		for(PropositionalFormula f : left){
			leftrules.add(f);
		}
	}
	
	public HashSet<PropositionalFormula> getLeftRules(){
		return leftrules;
	}

	public PropositionalFormula getRule() {
		return rule;
	}

	public void setTermination() {
		termination = true;
	}
	
	public boolean getTermination(){
		return termination;
	}

	public void addAppliedRule(PropositionalFormula rf) {
		appliedrules.add(rf);
	}
	
	public void deleteLeftRule(PropositionalFormula rf){
		leftrules.remove(rf);
	}

	public HashSet<PropositionalFormula> getModel() {
		return model;
	}
	
	public void copyModel(HashSet<PropositionalFormula> m){
		model.addAll(m);
	}
	
	public boolean updateModel(){
		Iterator<PropositionalFormula> it = model.iterator();
		while(it.hasNext()){
			PropositionalFormula element = it.next();
			if(f.equals(element)){
				termination = true;
				return false;
			}
		}
		model.add((PropositionalFormula)f.complement());
		return true;
	}

	public void setChildren(AONode newnode) {
		if(children == null)
			children = new ArrayList<AONode>();
		children.add(newnode);
	}
	
	public ArrayList<AONode> getChildren(){
		if(children == null || children.size()==0){
			return null;
		}else
			return children;
	}

	public void copyHyp() {
		this.hyps = predecessor.hyps;
	}
     
	public Conjunction getHyp(){
		return hyps;
	}

	public void setModel(PropositionalFormula pf) {
		Set<PropositionalFormula> lits = pf.getLiterals();
		Iterator<PropositionalFormula> it = lits.iterator();

		while(it.hasNext()){
			PropositionalFormula f = it.next();
			if(model.isEmpty()){
				model.add((PropositionalFormula)f.complement());
			}else{
				if(!model.contains(f)){					
					model.add((PropositionalFormula)f.complement());
				}
			}
		}	
	}

	// consistency test using resolution
	public void setResolution(ArrayList<PropositionalFormula> lists) {
		HashMap<PropositionalFormula, Integer> toadd = new HashMap<PropositionalFormula, Integer>();
		HashMap<PropositionalFormula, Integer> toremove = new HashMap<PropositionalFormula, Integer>();
		Iterator<Map.Entry<PropositionalFormula, Integer>> entries = resolution.entrySet().iterator(); 
		
		  
		while (entries.hasNext()) {  
		  
		    Map.Entry<PropositionalFormula, Integer> entry = entries.next();  
		    PropositionalFormula p = entry.getKey();
		    Integer i = entry.getValue();
	    	Set<PropositionalFormula> le = p.getLiterals();
		    for(int ind = 0; ind<lists.size(); ind++){
		    	le.remove((PropositionalFormula)lists.get(ind).complement());
		    }
	    	PropositionalFormula np = new Disjunction(le);

		    if(le.isEmpty()){
		    	setTermination();
		    }else{
		    	entries.remove();
		    	toadd.put(np, 2);
		    }
		}  
		
		resolution.putAll(toadd);
		
	}

	public void initResolution() {
		Iterator<PropositionalFormula> it_rule = leftrules.iterator();
		while(it_rule.hasNext()){
			resolution.put(it_rule.next(), 2);
		}
	}

	public HashMap<PropositionalFormula, Integer> getResolution() {
		return resolution;
	}

	public void copyResolution(HashMap<PropositionalFormula, Integer> resolution2) {
		resolution.putAll(resolution2);
	}

	public void removeChildren() {
		children.removeAll(children);
	}

	public boolean hasChildren() {
		if(children == null)
			return false;
		else if(children.isEmpty())
			return false;
		return true;
	}

	public void addResolution(ArrayList<PropositionalFormula> res) {
		Iterator<PropositionalFormula> it_rule = res.iterator();
		while(it_rule.hasNext()){
			resolution.put(it_rule.next(), 2);
		}
	}
}
