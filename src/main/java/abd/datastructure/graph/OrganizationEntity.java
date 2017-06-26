package abd.datastructure.graph;

import java.util.ArrayList;
import java.util.Iterator;

import net.sf.tweety.logics.pl.syntax.PropositionalFormula;



public class OrganizationEntity {
	public PropositionalFormula p;
    public ArrayList<PropositionalFormula> pf;
    public boolean consistency;

     public OrganizationEntity(){
         p = null;
    	 initFormulaList();
    	 consistency= true;
     }
     
     public void initFormulaList(){
    	 pf = new ArrayList<PropositionalFormula>();
     }
     
     public void setLiteral(PropositionalFormula p){
    	 this.p = p;
    	 pf.add(p);
    	 
     }
     
     public void addLiterals(ArrayList<PropositionalFormula> l){
    	 Iterator<PropositionalFormula> it = l.iterator();
    	 while(it.hasNext()){
    		 pf.add(it.next());
    	 }
     }
     
     public PropositionalFormula getLiteral(){
    	 return p;
     }

	public boolean hasLiteral() {
		if(p==null)
			return false;
		else
			return true;
	}
   
}
