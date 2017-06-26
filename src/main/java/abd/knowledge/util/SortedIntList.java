package abd.knowledge.util;

/*
 * (c) copyright 2008, Technische Universitaet Graz and Technische Universitaet Wien
 *
 * This file is part of jdiagengine.
 *
 * jdiagengine is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * jdiagengine is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * You should have received a copy of the GNU General Public License
 * along with jdiagengine. If not, see <http://www.gnu.org/licenses/>.
 *
 * Authors: Joerg Weber, Franz Wotawa
 * Contact: jweber@ist.tugraz.at (preferred), or fwotawa@ist.tugraz.at
 *
 */


/**
 *
 * @version 1, DATE: 16.03.2005
 * @author Joerg Weber
 *
 * A sorted linked list containing integers. The order is ascending.
 * A value can occur only once in the list. If one tries to add an already 
 * existing item, it is not added. 
 * Therefore, this data structure can be used for representing sets of integers.
 * Some set operations are implemented.
 *
 * For this class, an invariant (see method invariant()) is defined: it must be sorted.
 * The invariant is checked in assertions. Furthermore, assertions are used to check 
 * pre- and postconditions for methods. Some postconditions are implemented in seperate methods.
 *
 */

import java.io.*;      // IO specific classes (File, Stream,..)
import java.util.*;    

import scala.sys.Prop;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;
// Java util


public class SortedIntList extends LinkedList {


    public Object clone() {
        return super.clone();  // nothing more to do!
    }

    /*
     * Returns true iff the list is in ascending order.
     */
    protected boolean isSorted() {
        int lastItem = Integer.MIN_VALUE;

        Iterator it = iterator();
        while (it.hasNext()) {
        	PropositionalFormula newItem = (PropositionalFormula)it.next();
        	int newHash = newItem.hashCode();
            if (newHash < lastItem) return false;
            lastItem = newHash;
        }

        return true;
    }

    /*
     * Returns true iff no two consecutive elements are equal.
     */ 
    protected boolean uniqueElements() {
        Iterator it = iterator();
        
        int lastHash;

        if (it.hasNext()) {
            PropositionalFormula lastItem = (PropositionalFormula)it.next();
            lastHash = lastItem.hashCode();
        } else return true;
        
        while (it.hasNext()) {
        	PropositionalFormula nextItem = (PropositionalFormula)it.next();
            int nextHash = nextItem.hashCode();
            if (nextHash== lastHash) return false;
        }

        return true;
    }

    // The class invariant.
    protected boolean invariant() {
        return (isSorted() && uniqueElements());
    }

    /**
     * Use this method to add an integer to the sorted list (Insertion Sort algorithm).
     * Returns false if the item is already in the list.
     */
    public boolean addSorted(int item) {
        
        // precondition and class invariant
        assert(invariant());

        // method body

        ListIterator it = listIterator(0);
        while (it.hasNext()) {
            Integer currentItem = (Integer)it.next();
            int current_n = currentItem.intValue();

            if (item == current_n) return false;
            else if (item < current_n) {
                it.previous();
                it.add(new Integer(item));
                assert(invariant() && contains(new Integer(item)));
                return true;
            }
        }
        
        // this code is executed only if the item is appended at end of list,
        // i.e. all existing integers are smaller than the new item
        it.add(new Integer(item));

        // postcondition and class invariant
        assert(invariant() && contains(new Integer(item)));
        return true;
    }
    
    public boolean addSorted(PropositionalFormula f){
        // precondition and class invariant
        assert(invariant());

        // method body

        int itemHash = f.hashCode();
        ListIterator it = listIterator(0);
        while (it.hasNext()) {
        	PropositionalFormula currentItem = (PropositionalFormula)it.next();
        	int currentHash = currentItem.hashCode();
            int current_n = currentHash;

            if (itemHash == current_n) return false;
            else if (itemHash < current_n) {
                it.previous();
                it.add(f);
                assert(invariant() && contains(f));
                return true;
            }
        }
        
        // this code is executed only if the item is appended at end of list,
        // i.e. all existing integers are smaller than the new item
        it.add(f);

        // postcondition and class invariant
        assert(invariant() && contains(f));
        return true;
    }

    public int getFirstInt() {
        assert(size() > 0);

        return ((PropositionalFormula)getFirst()).hashCode();
    }
    
    public PropositionalFormula getFirstFormula(){
        assert(size() > 0);

        return (PropositionalFormula)getFirst();
    }
    
    public int getLastInt() {
        assert(size() > 0);

        return ((PropositionalFormula)getLast()).hashCode();
    }

    public PropositionalFormula getLastFormula(){
        assert(size() > 0);

        return (PropositionalFormula)getLast();
    }
    
    public boolean contains(int n) {

        if (size() == 0) return false;
        else {
            int last = ((PropositionalFormula)getLast()).hashCode();
            if (n > last) return false;
            else {
                Iterator it = iterator();
                while(it.hasNext()) {
                    int item = ((PropositionalFormula)it.next()).hashCode();
                    if (n < item) return false;
                    else if (n == item) return true;
                }
                assert(false);
                return false;
            }
        }
    }

    public boolean contains(Object o) {
        assert(o instanceof PropositionalFormula);

        int n = ((PropositionalFormula)o).hashCode();
        return contains(n);       
    }

    /**
     * Returns true iff anObject is a SortedIntList containing the same integers as this list.
     */ 
    public boolean equals(Object anObject) {
        if (anObject != null) {
            if (anObject instanceof SortedIntList) {
                SortedIntList other = (SortedIntList)anObject;
                
                if (size() == other.size()) {
                    Iterator it = iterator();
                    Iterator ot = other.iterator();

                    // compare one item after the other; we know that both lists have the same length
                    while(it.hasNext()) {
                    	PropositionalFormula n = (PropositionalFormula)it.next();
                    	PropositionalFormula o = (PropositionalFormula)ot.next();
                        if (!n.equals(o)) {
                            // postcondition
                            assert(!this.subsetOf(other) || !other.subsetOf(this));
                            return false;
                        }
                    }
                    // postcondition
                    assert(this.subsetOf(other) && other.subsetOf(this));
                    return true;

                } else return false;

            } else return false;
        } else return false;
    }


    /**
     * Creates a new list which contains all integers which are element of this list and not
     * element of the other list.
     */
    public SortedIntList subtract(SortedIntList other) {

        SortedIntList result;

        if (size() == 0) result = new SortedIntList();
        else if (other.size() == 0) result = (SortedIntList)this.clone();
        else {
            
            result = new SortedIntList();

            Iterator itThis = iterator();
            Iterator itOther = other.iterator();

            int o = ((PropositionalFormula)itOther.next()).hashCode();

            // iterate through items of this list
            while(itThis.hasNext()) {
                
                PropositionalFormula nobj = (PropositionalFormula)itThis.next();
                int n = nobj.hashCode();

                if (n < o) result.add(nobj);
                else {
                    if (itOther.hasNext()) o = ((PropositionalFormula)itOther.next()).hashCode();
                    else {
                        while(itThis.hasNext()) {
                            nobj = (PropositionalFormula)itThis.next();
                            result.add(nobj);
                        }
                    }
                }
            }             

        }

        // postcondition: let result := this - other.
        // then: result must be sorted and result must not intersect other
        //       and result joined with other must be equal to this. 
        assert(result.invariant() && !result.intersects(other) && result.join(other).equals(this));

        return result;
    }

    
    /**
     * Creates a new list which contains each integer which is in this and/or the other list.
     */
    public SortedIntList join(SortedIntList other) {
        SortedIntList result = (SortedIntList)this.clone();

        Iterator itOther = other.iterator();
        while(itOther.hasNext()) {
        	PropositionalFormula obj = (PropositionalFormula)itOther.next();
            result.addSorted(obj);
        }

        // postcondition
        assert(result.invariant() && this.subsetOf(result)  && other.subsetOf(result));

        return result;
    }

    /**
     * Returns true iff the integers in this list are a subset (proper or improper) of 
     * the integers in the other list.
     */
    public boolean subsetOf(SortedIntList other) {

        // precondition and invariant
        assert(invariant());

        int sz = size();

        // early detection: check last values
        if (sz == 0) return true;
        else if (sz > other.size()) return false;
        else {
            int nlast = ((PropositionalFormula)getLast()).hashCode();
            int olast = ((PropositionalFormula)other.getLast()).hashCode();
            if (nlast > olast) return false;
        }

        Iterator it = iterator();
        Iterator ot = other.iterator();

        // loop: iterates through this list, for each item: check if it exists in 
        // the other list.
        while (it.hasNext()) {

            int ni = ((PropositionalFormula)it.next()).hashCode();
            
            if (!ot.hasNext()) {
                assert(postcond_subsetOf(other, false));
                return false;
            }
            int no = ((PropositionalFormula)ot.next()).hashCode();            
            while (no < ni) {
                if (!ot.hasNext()) {
                    assert(postcond_subsetOf(other, false));
                    return false;
                }
                no = ((PropositionalFormula)ot.next()).hashCode();
            }
            
            if (no > ni) {
                assert(postcond_subsetOf(other, false));
                return false;
            }
            else assert(no == ni);
            
        }

        assert(postcond_subsetOf(other, true));   
        return true;

    }  // subsetOf()

    
    /**
     * Returns true iff the integers in this list form a proper subset of 
     * the integers in the other list.
     */
    public boolean properSubsetOf(SortedIntList other) {

        // precondition and invariant
        assert(invariant());

        int sz = size();

        // early detection: check last values
        if (sz == 0) return (other.size() > 0);
        else if (sz >= other.size()) return false;
        else {
            int nlast = ((PropositionalFormula)getLast()).hashCode();
            int olast = ((PropositionalFormula)other.getLast()).hashCode();
            if (nlast > olast) return false;
        }

        Iterator it = iterator();
        Iterator ot = other.iterator();

        // loop: iterates through this list, for each item: check if it exists in 
        // the other list.
        while (it.hasNext()) {

            int ni = ((PropositionalFormula)it.next()).hashCode();
            
            if (!ot.hasNext()) {
                assert(postcond_properSubsetOf(other, false));
                return false;
            }
            int no = ((PropositionalFormula)ot.next()).hashCode();            
            while (no < ni) {
                if (!ot.hasNext()) {
                    assert(postcond_properSubsetOf(other, false));
                    return false;
                }
                no = ((PropositionalFormula)ot.next()).hashCode();
             }
            
            if (no > ni) {
                assert(postcond_properSubsetOf(other, false));
                return false;
            }
            else assert(no == ni);
            
        }

        assert(postcond_properSubsetOf(other, true));   
        return true;

    }  // properSubsetOf()

    /**
     * Returns if this set intersects the other set. If false, then intersectionSet stays empty.
     * Otherwise, intersectionSet will contain all items which are in both lists. 
     */
    public boolean intersection(SortedIntList other, SortedIntList intersectionSet) {

        // precondition and invariant
        assert((intersectionSet != null) && (intersectionSet.size() == 0));
        assert(invariant());
        
        if ((size() == 0) || (other.size() == 0)) return false;

        int nfirst = ((PropositionalFormula)getFirst()).hashCode();
        int nlast = ((PropositionalFormula)getLast()).hashCode();
        int ofirst = ((PropositionalFormula)other.getFirst()).hashCode();
        int olast = ((PropositionalFormula)other.getLast()).hashCode();
        
        // "early detection": compare if the intervals [first, last] of the two lists intersect.
        // if no: return false
        if ((nlast < ofirst) || (olast < nfirst)) {
            assert(postcond_intersection(other, false, intersectionSet));
            return false;
        }
        else {

            boolean result = false;
            Iterator itThis = iterator();
            Iterator itOther = other.iterator();
            
            PropositionalFormula nf = (PropositionalFormula)itThis.next();
            int n = (nf).hashCode();
            int o = ((PropositionalFormula)itOther.next()).hashCode();
            int index = 0;

            while(true) {
                
                if (n == o) {
  
                    result = true;
                    intersectionSet.addSorted(nf);                    

                    if (!itThis.hasNext() || !itOther.hasNext()) break;
                    n = ((PropositionalFormula)itThis.next()).hashCode();
                    ++index;
                    o = ((PropositionalFormula)itOther.next()).hashCode();

                } else if (n < o) {
                    if (!itThis.hasNext()) break;

                    n = ((PropositionalFormula)itThis.next()).hashCode();
                    ++index;
                }
                else {  // n > o
                    if (!itOther.hasNext()) break;
                    o = ((PropositionalFormula)itOther.next()).hashCode();
                }
            }

            assert(postcond_intersection(other, result, intersectionSet));
            return result;

        }

    }  // intersection()


    /**
     * Returns true iff the set of integers of this list "hits" the set of integers of
     * the other list, i.e. if the intersection of this and the other list is not empty.
     */
    public boolean intersects(SortedIntList other) {
        // precondition and invariant
        assert((size() > 0) || (other.size() > 0));
        assert(invariant());

        if ((size() == 0) || (other.size() == 0)) return false;

        int nfirst = ((PropositionalFormula)getFirst()).hashCode();
        int nlast = ((PropositionalFormula)getLast()).hashCode();
        int ofirst = ((PropositionalFormula)other.getFirst()).hashCode();
        int olast = ((PropositionalFormula)other.getLast()).hashCode();
        
        // "early detection": compare if the intervals [first, last] of the two lists intersect.
        // if no: return false
        if ((nlast < ofirst) || (olast < nfirst)) {
            assert(postcond_intersects(other, false));
            return false;
        }
        else {
            
            Iterator itThis = iterator();
            Iterator itOther = other.iterator();

            int n = ((PropositionalFormula)itThis.next()).hashCode();
            int o = ((PropositionalFormula)itOther.next()).hashCode();

            // iterate through lists; return true as soon as one common integer is found.
            // Return false when the end of a list is reached before a common item is found.
            // Otherwise, exactly one of the iterators is incremented in each cycle.
            while(true) {
                
                if (n == o) {
                    assert(postcond_intersects(other, true));
                    return true;
                } else if (n < o) {
                    if (!itThis.hasNext()) {
                        assert(postcond_intersects(other, false));
                        return false;
                    }
                    n = ((PropositionalFormula)itThis.next()).hashCode();
                }
                else {  // n > o
                    if (!itOther.hasNext()) {
                        assert(postcond_intersects(other, false));
                        return false;
                    }
                    o = ((PropositionalFormula)itOther.next()).hashCode();
                }
            }

        }
        
    }  // intersects()

    // The postcondition of the intersects() method.
    protected boolean postcond_intersects(SortedIntList other, boolean result) {
        boolean proper_res = false;

        Iterator it = iterator();
        while (it.hasNext()) {
            if (other.contains(it.next())) {
                proper_res = true;
                break;
            }
        }

        return (result == proper_res);
    }

    // The postcondition of the intersection() method.
    protected boolean postcond_intersection(SortedIntList other, boolean result, 
                                            SortedIntList intersectionSet) {

        assert(intersectionSet.invariant());

        boolean proper_res = false;

        Iterator it = iterator();
        while (it.hasNext()) {
            if (other.contains(it.next())) {
                proper_res = true;
                break;
            }
        }

        if (result != proper_res) return false;
        else {
            if (!result) return (intersectionSet.size() == 0);
            else {
                Iterator itIS = intersectionSet.iterator();
                while (itIS.hasNext()) {
                	PropositionalFormula no = (PropositionalFormula)itIS.next();
                    if (!contains(no) || !other.contains(no)) return false;
                }
                return true;
            }
        }
    }

    // The postcondition of the subsetOf() method.
    protected boolean postcond_subsetOf(SortedIntList other, boolean result) {
        boolean proper_res = true;

        Iterator it = iterator();
        while (it.hasNext()) {
            if (!other.contains(it.next())) {
                proper_res = false;
                break;
            }
        }

        return (result == proper_res);
    }

    // The postcondition of the properSubsetOf() method.
    protected boolean postcond_properSubsetOf(SortedIntList other, boolean result) {
        boolean trueRes = true;

        Iterator it = iterator();
        while (it.hasNext()) {
            if (!other.contains(it.next())) {
                trueRes = false;
                break;
            }
        }

        trueRes = (trueRes && (size() < other.size()));

        return (result == trueRes);
    }

    public String toString() {
        String result = "";

        Iterator it = iterator();
        while(it.hasNext()) {
        	PropositionalFormula n = ((PropositionalFormula)it.next());
            result = result + n.toString();
            if (it.hasNext()) result = result + ",";
        }

        return result;
    }

}
