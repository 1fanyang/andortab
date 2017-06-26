package abd.tableau.iterative;

public class Edge {
	 
    protected AONode a, b;
    protected double weight;
     
    public Edge(AONode a, AONode b) {
        this(a, b, Double.POSITIVE_INFINITY);
    }
     
    public Edge(AONode a, AONode b, double weight) {
        this.a = a;
        this.b = b;
        this.weight = weight;
    }
     
    public double getWeight() {
        return weight;
    }
     
    public String toString() {
        return a + " ==> " + b;
    }
 
}
