sig Tree { root : lone Node }
sig Node {
	left, right : lone Node,
	value: one Int,
	
}

//a)
sig Parent {
	rel: Node  -> one Node 
}

fact {
	all s, p:Node | s -> p in Parent.rel iff (s in p.left or s in p.right)
}

pred wellFormedTree {

	//b)
	all n:Node | ( n.left != none or n.right != none) implies n.left != n.right
	//c)
	all n0, n1:Node | n0 -> n1 in Parent.rel implies n1 -> n0 not in Parent.rel
	//d)
	all n:Node, t:Tree | n != t.root and one Parent.rel[n]
	//e)
	all n:Node | (one n.left implies n.value > n.left.value) and  (one n.right implies n.value < n.right.value) 
	//f)
	all disj n0, n1:Node | n0.value != n1.value
	//g)
	all n:Node | #(n.^(left)) - #(n.^(right)) <= 1
}




run wellFormedTree


