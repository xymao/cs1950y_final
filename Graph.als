//open util
// basic structures and elements 
sig Vertex {
	outgoing: set Vertex,
} {
	Vertex in DirectedGraph.vertices
	all v : outgoing | this->v in Edge.relation

}
sig Edge {
	weight: Int, // can be negative. 
   	v1: one Vertex,
	v2: one Vertex,
	relation: v1->v2
} {
	Edge in DirectedGraph.edges
	one relation
	relation = v1 -> v2
	v2 in v1.outgoing
}


sig DirectedGraph {
	edges: set Edge,
	vertices: set Vertex
} {
	some edges
	some vertices

	// edges only connects vertices in the graph
	all e: edges | e.v1 in vertices and e.v2 in vertices and e.v1 != e.v2
	// no duplicated edges
	all disj e1, e2: edges |
		e1.relation != e2.relation
	// no cycle
	//no iden & ^(edges.relation)
  	//let edges = {a, b: vertices| b in a.outgoing} | all a, b: vertices | a->b not in ^edges

	// all vertices and edges are connected
	all n : vertices | vertices in n.*(outgoing+~outgoing)

}


run {} for exactly 4 Vertex, exactly 3 Edge, 1 DirectedGraph
