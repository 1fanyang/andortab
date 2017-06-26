package abd.datastructure.graph;

import java.util.HashSet;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.HashMap;

import net.sf.tweety.logics.pl.sat.Sat4jSolver;
import net.sf.tweety.logics.pl.syntax.Conjunction;
import net.sf.tweety.logics.pl.syntax.PropositionalFormula;

public class TreeHelper {

	private TreeNode root;
	private List<TreeNode> tempNodeList;
	private List<TreeNode>	leafNodeList;
	
	
	private boolean isValidTree = true;

	public TreeHelper() {
		initLeafNodeList();
	}

	public TreeHelper(List<TreeNode> treeNodeList) {
		tempNodeList = treeNodeList;
		generateTree();
	}

	public static TreeNode getTreeNodeById(TreeNode tree, int id) {
		if (tree == null)
			return null;
		TreeNode treeNode = tree.findTreeNodeById(id);
		return treeNode;
	}

	/** generate a tree from the given treeNode or entity list */
	public void generateTree() {
		HashMap nodeMap = putNodesIntoMap();
		putChildIntoParent(nodeMap);
	}
	
	public void generateLeafNodes(){
		leafNodeList = root.getLeaves();
	}

	/**
	 * put all the treeNodes into a hash table by its id as the key
	 * 
	 * @return hashmap that contains the treenodes
	 */
	protected HashMap putNodesIntoMap() {
		int maxId = Integer.MAX_VALUE;
		HashMap nodeMap = new HashMap<String, TreeNode>();
		Iterator it = tempNodeList.iterator();
		while (it.hasNext()) {
			TreeNode treeNode = (TreeNode) it.next();
			int id = treeNode.getSelfId();
			if (id < maxId) {
				maxId = id;
				this.root = treeNode;
			}
			String keyId = String.valueOf(id);

			nodeMap.put(keyId, treeNode);
			// System.out.println("keyId: " +keyId);
		}
		return nodeMap;
	}

	/**
	 * set the parent nodes point to the child nodes
	 * 
	 * @param nodeMap
	 *            a hashmap that contains all the treenodes by its id as the key
	 */
	protected void putChildIntoParent(HashMap nodeMap) {
		Iterator it = nodeMap.values().iterator();
		while (it.hasNext()) {
			TreeNode treeNode = (TreeNode) it.next();
			int parentId = treeNode.getParentId();
			String parentKeyId = String.valueOf(parentId);
			if (nodeMap.containsKey(parentKeyId)) {
				TreeNode parentNode = (TreeNode) nodeMap.get(parentKeyId);
				if (parentNode == null) {
					this.isValidTree = false;
					return;
				} else {
					parentNode.addChildNode(treeNode);
					// System.out.println("childId: " +treeNode.getSelfId()+" parentId: "+parentNode.getSelfId());
				}
			}
		}
	}

	/** initialize the tempNodeList property */
	protected void initTempNodeList() {
		if (this.tempNodeList == null) {
			this.tempNodeList = new ArrayList<TreeNode>();
		}
	}
	
	/** initialize the tempNodeList property */
	protected void initLeafNodeList() {
		if (this.leafNodeList == null) {
			this.leafNodeList = new ArrayList<TreeNode>();
		}
	}

	/** add a tree node to the tempNodeList */
	public void addTreeNode(TreeNode treeNode) {
		initTempNodeList();
		this.tempNodeList.add(treeNode);
	}

	/**
	 * insert a tree node to the tree generated already
	 * 
	 * @return show the insert operation is ok or not
	 */
	public boolean insertTreeNode(TreeNode treeNode) {
		boolean insertFlag = root.insertJuniorNode(treeNode);
		return insertFlag;
	}

	/**
	 * adapt the entities to the corresponding treeNode
	 * 
	 * @param entityList
	 *            list that contains the entities
	 *@return the list containg the corresponding treeNodes of the entities
	 */
	public static List<TreeNode> changeEnititiesToTreeNodes(List entityList) {
		OrganizationEntity orgEntity = new OrganizationEntity();
		List<TreeNode> tempNodeList = new ArrayList<TreeNode>();
		TreeNode treeNode;

		Iterator it = entityList.iterator();
		while (it.hasNext()) {
			orgEntity = (OrganizationEntity) it.next();
			treeNode = new TreeNode();
			treeNode.setObj(orgEntity);
//			treeNode.setParentId(orgEntity.getParentId());
//			treeNode.setSelfId(orgEntity.getOrgId());
//			treeNode.setNodeName(orgEntity.getOrgName());
			tempNodeList.add(treeNode);
		}
		return tempNodeList;
	}
	
	public ArrayList<PropositionalFormula> getAllSatBranches(){
		
		ArrayList<PropositionalFormula> hyps = new ArrayList<PropositionalFormula>();
		
		return hyps;
	}

	public boolean isValidTree() {
		return this.isValidTree;
	}

	public TreeNode getRoot() {
		return root;
	}

	public void setRoot(TreeNode root) {
		this.root = root;
		leafNodeList.add(root);
	}

	public List<TreeNode> getTempNodeList() {
		return tempNodeList;
	}

	public void setTempNodeList(List<TreeNode> tempNodeList) {
		this.tempNodeList = tempNodeList;
	}

	public void updateTree() {
		
		// update children list for leaf nodes
		ArrayList<TreeNode> newLeafNodeList = new ArrayList<TreeNode>();
		Iterator<TreeNode> it = leafNodeList.iterator();
		while(it.hasNext()){
			ArrayList<TreeNode> newList = new ArrayList<TreeNode>();
			Iterator<TreeNode> itTemp = tempNodeList.iterator();
			TreeNode parent=it.next();
			while(itTemp.hasNext()){
				TreeNode child= itTemp.next().clone();
				child.setParentNode(parent);
				newList.add(child);
			}
			parent.setChildList(newList);
			newLeafNodeList.addAll(newList);
		}
		leafNodeList.clear();
//		leafNodeList.addAll(newLeafNodeList);
		
		Sat4jSolver solver = new Sat4jSolver();
		for(int i=newLeafNodeList.size()-1;i>=0;i--){
			TreeNode tn =newLeafNodeList.get(i);
			if(tn.getParentNode().getHyp()!= null)
				tn.addAllHyp(tn.getParentNode().getHyp());
			newLeafNodeList.get(i).reduceConjunction();
			if(!solver.isConsistent((PropositionalFormula)newLeafNodeList.get(i).getConjunction())){
				newLeafNodeList.remove(i);
			}
		}
		
		ArrayList<TreeNode> hypotheses = new ArrayList<TreeNode>();
		// each nodes contains a set of literals.
		Iterator<TreeNode> itln = newLeafNodeList.iterator();
		while(itln.hasNext()){
			TreeNode leaf=itln.next();
			Conjunction lh= leaf.getConjunction();
			HashSet<String> litset = new HashSet<String>();
			Iterator<PropositionalFormula> itlh = lh.getLiterals().iterator();
			while(itlh.hasNext()){
				litset.add(itlh.next().complement().toString());
				//h.add((PropositionalFormula) itlh.next().complement());
			}
			if(hypotheses.size()>0){
				for(int i=0;i<hypotheses.size();i++){
					HashSet<String> refset = new HashSet<String>();
					Iterator<PropositionalFormula> itref = hypotheses.get(i).getConjunction().getLiterals().iterator();
					while(itref.hasNext()){
						refset.add(itref.next().complement().toString());
					}
					if(litset.containsAll(refset)){
						break;
					}else if (refset.containsAll(litset)) {
						hypotheses.remove(i);
						hypotheses.add(leaf);
						break;
					}else{
						if(i==hypotheses.size()-1){
							hypotheses.add(leaf);
						}
					}
				}
			}else
				hypotheses.add(leaf);
		
		}
		
		leafNodeList.addAll(hypotheses);

	}

	public List<TreeNode> getLeafNodes() {

		return leafNodeList;
	}


}
