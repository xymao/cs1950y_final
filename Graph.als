//open util
// basic structures and elements 
sig Vertex {
	outgoing: set Vertex,
	//cost: one Cost
//	value: Int,
//	isInfinite:  Int
} {
	Vertex in DirectedGraph.vertices
	all v : outgoing | this->v in Edge.relation
//	isInfinite in {1 + 0}
	//s are only vertices that have an edge in the graph with the current vertex
	//all v: neighbors | v in DirectedGraph.edges.relation.Vertex
	//all v: neighbors | v == Edge
	//	all v: neighbors | v in Edge.relation.Vertex || v in Vertex.(Edge.relation)
}
sig Edge {
	weight: Int, // can be negative. 
   	v1: one Vertex,
	v2: one Vertex,
	relation: v1->v2
	//	relation: Vertex -> Vertex,
} {
	Edge in DirectedGraph.edges
	//relation.Vertex in Vertex.relation.neighbors
	//Vertex.relation in relation.Vertex.neighbors
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
	//all v: Vertex | v in  
	// all vertices and edges are connected
//	all disj v1, v2: vertices | v1 in v2.^(edges.relation) or v2 in v1.^(edges.relation)
//	all e, b: univ | e in b.^(r+~r)
//	all v1, v2: vertices | v1 in v2.(edges.relation + ~(edges.relation))
//	all disj v1, v2: vertices | v1 in (v2.^outgoing) or v2 in (v1.^outgoing)

	// all vertices should be connected to another by an edge
	//all e: Edge | e in edges iff e.relation.Vertex in vertices and Vertex.(e.relation) in vertices
	// edges only connects vertices in the graph
	all e: edges | e.v1 in vertices and e.v2 in vertices and e.v1 != e.v2
	// no duplicated edges
	all disj e1, e2: edges |
		e1.relation != e2.relation //and e1.relation != ~(e2.relation)
//	all v: vertices | #v.outgoing > 0
	all v: vertices | some v2: vertices-v | v->v2 in edges.relation or v2->v in edges.relation

}


run {} for exactly 4 Vertex, exactly 4 Edge, 1 DirectedGraph
