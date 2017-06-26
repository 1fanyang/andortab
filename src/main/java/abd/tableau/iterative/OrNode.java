package abd.tableau.iterative;

import java.util.ArrayList;
import java.util.HashSet;

import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

public class OrNode extends AndOrNode implements Comparable<OrNode> {
    
    protected HashSet<PropositionalFormula> appliedrules;
    protected HashSet<PropositionalFormula> leftrules;
    
    protected PropositionalFormula rule;
    
    protected boolean visited;
    public Integer index = null;
    public Integer lowlink = null;
    public double distance = Double.POSITIVE_INFINITY;
    public AndNode predecessor = null;
    public ArrayList<OrNode> siblings = new ArrayList<OrNode>(); 
    
    public OrNode(PropositionalFormula r) {
        this.rule = r;
    }
     
    public OrNode() {
         
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
     
    public int compareTo(OrNode ob) {
        String tempA = this.toString();
        String tempB = ob.toString();
         
        return tempA.compareTo(tempB);
    }
     
    public String toString() {
        return rule.toString();
    }
     
}
