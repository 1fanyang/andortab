package abd.tableau.iterative;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import net.sf.tweety.logics.pl.syntax.Disjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
import net.sf.tweety.logics.pl.syntax.Tautology;
import abd.knowledge.util.SetOps;

public class PLResolution {

	private static boolean discardTautologies = true;

	/**
	 * Default constructor, which will set the algorithm to discard tautologies
	 * by default.
	 */
	public PLResolution() {
		this(true);
	}

	public PLResolution(boolean discardTautologies) {
		setDiscardTautologies(discardTautologies);
	}
	
	public static boolean plresolution(HashSet<PropositionalFormula> clauses, PropositionalFormula alpha){
		//clauses.add(alpha);
		discardTautologies(clauses);
		Set<PropositionalFormula> newClauses= new LinkedHashSet<PropositionalFormula>();
		
		// loop do
		do {
			// for each pair of clauses C_i, C_j in clauses do
			List<PropositionalFormula> clausesAsList = new ArrayList<PropositionalFormula>(clauses);
			for (int i = 0; i < clausesAsList.size() - 1; i++) {
				PropositionalFormula ci = clausesAsList.get(i);
				for (int j = i + 1; j < clausesAsList.size(); j++) {
					PropositionalFormula cj = clausesAsList.get(j);
					// resolvents <- PL-RESOLVE(C_i, C_j)
					Set<PropositionalFormula> resolvents = plResolve(ci, cj);
					// if resolvents contains the empty clause then return true
					Iterator<PropositionalFormula> it = resolvents.iterator();
					while(it.hasNext()){
						if(it.next().getLiterals().isEmpty())
							return true;
					}
					// new <- new U resolvents
					newClauses.addAll(resolvents);
				}
			}
			// if new is subset of clauses then return false
			if (clauses.containsAll(newClauses)) {
				return false;
			}

			// clauses <- clauses U new
			clauses.addAll(newClauses);

		} while (true);
	}
	
	public static Set<PropositionalFormula> plResolve(PropositionalFormula ci, PropositionalFormula cj) {
		Set<PropositionalFormula> resolvents = new LinkedHashSet<PropositionalFormula>();

		// The complementary positive literals from C_i
		resolvePositiveWithNegative(ci, cj, resolvents);
		// The complementary negative literals from C_i
		//resolvePositiveWithNegative(cj, ci, resolvents);

		return resolvents;
	}
	
	protected static void resolvePositiveWithNegative(PropositionalFormula c1, PropositionalFormula c2,
			Set<PropositionalFormula> resolvents) {
		// Calculate the complementary positive literals from c1 with
		// the negative literals from c2
	 
		Set<PropositionalFormula> complementary = new HashSet<PropositionalFormula>();
		Set<PropositionalFormula> set1 = c1.getLiterals();
		Set<PropositionalFormula> set2 = c2.getLiterals();
		
		List<PropositionalFormula> list1 = new ArrayList<PropositionalFormula>(set1);
		List<PropositionalFormula> list2 = new ArrayList<PropositionalFormula>(set2);
		for (int i = 0; i < list1.size(); i++) {
			PropositionalFormula ci = list1.get(i);
			for (int j = 0; j < list2.size(); j++) {
				PropositionalFormula cj = list2.get(j);
				if(ci.equals(cj.complement())){
					complementary.add(ci);
					break;
				}
			}
		}
		
		for(PropositionalFormula complement:complementary){
			List<PropositionalFormula> resolventLiterals = new ArrayList<PropositionalFormula>();
			for(PropositionalFormula c1l : c1.getLiterals()){
				if (!c1l.equals(complement)) {
					resolventLiterals.add(c1l);
				}
			}
			for (PropositionalFormula c2l : c2.getLiterals()) {
				if (!c2l.equals(complement.complement())) {
					resolventLiterals.add(c2l);
				}
			}
			
			Disjunction resolvent = new Disjunction(resolventLiterals);
			// Discard tautological clauses if this optimization is turned on.
			if (resolvent.getAtoms().size()==resolvent.getLiterals().size()) {
				resolvents.add(resolvent);
			}
		}
	}
	
	protected static  void discardTautologies(Set<PropositionalFormula>  clauses) {
		if (isDiscardTautologies()) {
			Set<PropositionalFormula> toDiscard = new HashSet<PropositionalFormula>();
			for (PropositionalFormula c : clauses) {
				if (c.getAtoms().size()<c.getLiterals().size()) {
					toDiscard.add(c);
				}
			}
			clauses.removeAll(toDiscard);
		}
	}
	
	/**
	 * @return true if the algorithm will discard tautological clauses during
	 *         processing.
	 */
	public static boolean isDiscardTautologies() {
		return discardTautologies;
	}

	public void setDiscardTautologies(boolean discardTautologies) {
		this.discardTautologies = discardTautologies;
	}


}
