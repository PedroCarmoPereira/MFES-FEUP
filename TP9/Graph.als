/* 
Each node as a set of outgoing edges, representing a directed graph without multiple edged.
*/
sig Node {
	adj : set Node
}

/*
The graph is undirected, ie, edges are symmetric.
http://mathworld.wolfram.com/UndirectedGraph.html
*/
pred undirected {
	all n0, n1:Node | n0 -> n1 in adj implies n1 -> n0 in adj
}

/*
The graph is oriented, ie, contains no symmetric edges.
http://mathworld.wolfram.com/OrientedGraph.html
*/
pred oriented {
	all n0, n1:Node | n0 -> n1 in adj implies n1 -> n0 not in adj
}

/*
The graph is acyclic, ie, contains no directed cycles.
http://mathworld.wolfram.com/AcyclicDigraph.html
*/
pred acyclic {
  all n:Node | n not in n.^(adj)
}

/*
The graph is complete, ie, every node is connected to every other node.
http://mathworld.wolfram.com/CompleteDigraph.html
*/
pred complete {
  all n:Node | Node in n.adj
}

/*
The graph contains no loops, ie, nodes have no transitions to themselves.
http://mathworld.wolfram.com/GraphLoop.html
*/
pred noLoops {
	all n:Node | n not in n.adj
}

/*
The graph is weakly connected, ie, it is possible to reach every node from every node ignoring edge direction.
http://mathworld.wolfram.com/WeaklyConnectedDigraph.html
*/
pred weaklyConnected {
  all disj n1, n2: Node | n2 in n1.^(adj + ~adj)  
}

/*
The graph is strongly connected, ie, it is possible to reach every node from every node considering edge direction.
http://mathworld.wolfram.com/StronglyConnectedDigraph.html
*/
pred stonglyConnected {
  all disj n1, n2: Node | n2 in n1.^(adj) and n1 in n2.^(adj)

}

/*
The graph is transitive, ie, if two nodes are connected through a third node, they also are connected directly.
http://mathworld.wolfram.com/TransitiveDigraph.html
*/
pred transitive {
	all n0, n1, n2:Node | n0 -> n1 in adj and n1 -> n2 in adj implies n0 -> n2 in adj
}

