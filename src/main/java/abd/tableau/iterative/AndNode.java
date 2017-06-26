package abd.tableau.iterative;

import java.util.ArrayList;
import java.util.HashSet;

import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

/* And node is the literal node*/

public class AndNode extends AndOrNode implements Comparable<AndNode> {
    
    protected HashSet<PropositionalFormula> appliedrules;
    protected HashSet<PropositionalFormula> leftrules;
    
    protected PropositionalFormula rule;
    protected PropositionalFormula f;
    
    protected boolean visited;
    public Integer index = null;
    public Integer lowlink = null;
    public double distance = Double.POSITIVE_INFINITY;
    public OrNode predecessor = null;
    public ArrayList<AndNode> siblings = null;
     
    public AndNode(PropositionalFormula f) {
        this.f = f;
    }
     
    public AndNode() {
         
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
     
    public int compareTo(AndNode ob) {
    	PropositionalFormula fb = ob.getLiteral();
        if(fb.isLiteral()){
        	return fb.toString().compareTo(f.toString());
        }else
        	return 0;
    }
     
    private PropositionalFormula getLiteral() {
		return f;
	}

	public String toString() {
        return f.toString();
    }
     
}
