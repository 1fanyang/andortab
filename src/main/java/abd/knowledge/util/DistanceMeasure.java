package abd.knowledge.util;

import java.util.HashMap;
import java.util.Set;
import java.util.Iterator;

import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

//
public class DistanceMeasure {

	public static int distance(PropositionalFormula pf1, PropositionalFormula pf2){
		Set<PropositionalFormula> l1= pf1.getLiterals();
		Set<PropositionalFormula> l2= pf2.getLiterals();
		java.util.Iterator<PropositionalFormula> it2 = l2.iterator();
		int distance = 0;
		while(it2.hasNext()){
			if(l1.contains(it2.next())){
				distance++;
			}
		}
		return distance;
	}
	public static double distance2(PropositionalFormula pf1,HashMap<PropositionalFormula, Double> map){
		Set<PropositionalFormula> l1= pf1.getLiterals();
//		Set<PropositionalFormula> l2= pf2.getLiterals();
		java.util.Iterator<PropositionalFormula> it1 = l1.iterator();
		double distance = 0;
		while(it1.hasNext()){
			PropositionalFormula f =it1.next();
			distance = distance + map.get(f);
		}
		return distance;
	}
}
