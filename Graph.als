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
	v2 in v1.outgoing// iff (v1->v2 in relation)
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
		e1.relation != e2.relation //and e1.relation != ~(e2.relation)
	// no cycle
	//no iden & edges.relation
	// all vertices and edges are connected
//	all disj v1, v2: vertices | v1 in v2.^(edges.relation) or v2 in v1.^(edges.relation)
	all n : vertices | vertices in n.*(outgoing+~outgoing)

}


run {} for exactly 3 Vertex, exactly 3 Edge, 1 DirectedGraph
