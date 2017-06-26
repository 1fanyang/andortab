package abd.tableau.aliseda;

import java.util.*;

import abd.datastructure.graph.*;
import net.sf.tweety.logics.pl.PlBeliefSet;
import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.sat.SatSolver;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.Proposition;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import abd.datastructure.graph.*;

public class AlisedaTableau{
	    
	private AlisedaNode root;
	private Vector<AlisedaNode> leafnodes;
	
	private AlisedaGraph model;
	
	private PlBeliefSet kb;
	private PropositionalFormula obs;
	
	private Vector<PropositionalFormula> usedFormula;
	private Vector<PropositionalFormula> unusedFormula;
	
	
	public AlisedaTableau() {
		model = new AlisedaGraph();
		root = new AlisedaNode();
		leafnodes = new Vector<AlisedaNode>();
		usedFormula = new Vector<PropositionalFormula>();
		unusedFormula = new Vector<PropositionalFormula>();
	}

	void initilization(AlisedaNode rootnode){
		root = rootnode;
		model.initilization(rootnode);
	}
	
	void addKb(PlBeliefSet k){
		kb = k;
		Iterator<PropositionalFormula> it = kb.iterator();
		while(it.hasNext())
			unusedFormula.add(it.next());
	}
	
    public int getnbNodes(){
    	return model.getNodesize();
    }
	
	public void expansion(){

		while(!unusedFormula.isEmpty()){			
			PropositionalFormula f = unusedFormula.firstElement();
			model.expansion(f);
			usedFormula.addElement(f);
			unusedFormula.remove(f);
		}
		leafnodes.addAll(model.getAllLeaves());

	}

	public void addRoot(PropositionalFormula obs) {
		this.obs=obs;
		Set<PropositionalFormula> o = obs.getLiterals();
		root.init(o);
		model.initilization(root);
		
	}
	
	public void printGraph(){
		model.printAllNodes();
		System.out.println("=========================================");
		model.printTableau();
	}

	public Vector<PropositionalFormula>  getMiniamlExplantion(Vector<PropositionalFormula> hyp ) {
		// test consistency
		Vector<PropositionalFormula> minimal = new Vector<PropositionalFormula>();
		SatSolver mysolver = new Sat4jSolver();
		for(int i=hyp.size()-1;i>=0;i--){
			PropositionalFormula f = hyp.elementAt(i);
			Conjunction c = new Conjunction(f.getLiterals());
			Conjunction o = new Conjunction(obs.getLiterals());
			PropositionalFormula irr = c.combineWithAnd(o.complement());
			if(c.getLiterals().containsAll(o.getLiterals())|| o.getLiterals().containsAll(c.getLiterals())){
				hyp.remove(i);
				continue;
			}
			
			if(!mysolver.isConsistent((PropositionalFormula)irr)){
				hyp.remove(i);
				continue;
			}
			PlBeliefSet test = new PlBeliefSet(kb);
			test.add(hyp.get(i));
			if(!mysolver.isConsistent(test)){
				hyp.remove(i);
				continue;
			}
		}
		
		// remove hypotheses with observation literals if not all hyp has observation literals
		boolean all_intersection = true;
		Set<PropositionalFormula> obs_lits = obs.getLiterals();
		for(int i= 0; i < hyp.size(); i++){
			PropositionalFormula f = hyp.elementAt(i);
			Iterator<PropositionalFormula> it = obs_lits.iterator();
			boolean flag = false;
			while(it.hasNext()){
				PropositionalFormula obs_part = it.next();
				if(f.getLiterals().contains(obs_part)){
					flag = true;
				}
			}
			if(!flag){
				all_intersection = false;
				break;
			}
		}

		if(!all_intersection){
			for(int i= hyp.size()-1; i >= 0; i--){
				PropositionalFormula f = hyp.elementAt(i);
				Iterator<PropositionalFormula> it = obs_lits.iterator();
				while(it.hasNext()){
					PropositionalFormula obs_part = it.next();
					if(f.getLiterals().contains(obs_part)){
						hyp.removeElementAt(i);
						break;
					}
				}
			}
		}
		
		loop1:
		for(int i =0; i<hyp.size();i++){
			PropositionalFormula f = hyp.elementAt(i);
			Conjunction c = new Conjunction(f.getLiterals());
			

			if(i==hyp.size()-1){
				minimal.add(c);
				break loop1;
			}else{
				loop2:
				for(int j=hyp.size()-1; j>i; j--){
					PropositionalFormula fc = hyp.elementAt(j);
					Conjunction fcc = new Conjunction(fc.getLiterals());
					PropositionalFormula sub1= c.combineWithAnd(fcc.complement());
					PropositionalFormula sub2= fcc.combineWithAnd(c.complement());
 
					kb.add(sub1);
					if(!mysolver.isConsistent(kb)){
						kb.remove(sub1);
						kb.add(sub2);
						if(!mysolver.isConsistent(kb)){
							kb.remove(sub2);
						}else{
							kb.remove(sub2);
							hyp.removeElementAt(i);
							i--;
							break loop2;
						}
					}else{
						kb.remove(sub1);
						kb.add(sub2);
						if(!mysolver.isConsistent(kb)){
							kb.remove(sub2);
							hyp.removeElementAt(j);
						}else{
							kb.remove(sub2);
						}
					}
					if(j==i+1){
						minimal.add(c);
					}
				}
			}
		}
		return minimal;
	}

    // hyptheses generation (minimal hitting set)
	public Vector<PropositionalFormula> generationHypotheses(Vector<AlisedaNode> leaves){
		// TODO Auto-generated method stub
		Vector<PropositionalFormula> hypotheses = new Vector<PropositionalFormula>();

		// get the minimal hitting set from the leave nodes
		// create a hitting set tree
		TreeHelper hs = new TreeHelper();
		TreeNode root = new TreeNode();
		root.initOrgEntity();
		hs.setRoot(root);
		
		for(int i=0; i< leaves.size(); i++){
			AlisedaNode n = leaves.elementAt(i);
			Vector<PropositionalFormula> candidates = n.getLiterals();
			ArrayList<TreeNode> tempNodeList = new ArrayList<TreeNode>();
			for(int j=0; j<candidates.size();j++){
				PropositionalFormula l = candidates.elementAt(j);
				TreeNode node = new TreeNode();
				OrganizationEntity entity = new OrganizationEntity();
				entity.setLiteral(l);
				node.setObj(entity);
				tempNodeList.add(node);
				node.addHyp(l);
			}
			hs.setTempNodeList(tempNodeList);
			hs.updateTree();
			ArrayList<TreeNode> ln = (ArrayList<TreeNode>) hs.getLeafNodes();
		}
		
		ArrayList<TreeNode> ln = (ArrayList<TreeNode>) hs.getLeafNodes();
		Iterator<TreeNode> itln = ln.iterator();
		while(itln.hasNext()){
			TreeNode leaf=itln.next();
			Conjunction lh= leaf.getConjunction();
			Conjunction h= new Conjunction();
			Iterator<PropositionalFormula> itlh = lh.getLiterals().iterator();
			while(itlh.hasNext()){
				h.add((PropositionalFormula) itlh.next().complement());
			}
			hypotheses.add(h);
		}

		return hypotheses;
	}
	
	public Vector<AlisedaNode> getLeaves(){
		return leafnodes;
	}
}
