open Graph
open util/ordering[State]
open util/boolean
open util
// Bellman Ford Algorithm to find shortest path

sig State {
	graph: one DirectedGraph,
	dist: set Vertex -> Cost, //  Int // update 
	//remainingEdges: set Edge
	loopCounter: Int,
	src: one Vertex
} {
	#dist = #graph.vertices
	dist.Cost = graph.vertices
}

fact initialState {
	//remainingEdges = first.graph.edges
	// all vertex -> to infinity (very large number
	all d: Vertex.(first.dist) | d.isInfinite = True
	//all v: first.graph.vertices
	first.src in first.graph.vertices
	first.src.(first.dist).isInfinite = False and first.src.(first.dist).value = 0
	first.loopCounter = #first.graph.vertices
	
}

fact endState {
	//no last.remainingEdges
	last.loopCounter = 1
}	


abstract sig Event {
	pre, post: State
}

sig relaxEdge extends Event { } {
	// make sure they are the same graph
	post.graph = pre.graph
	post.loopCounter = pre.loopCounter - 1
	// relax one edge at a time
	all e: pre.graph.edges | {
		let curcost = (e.v1.(pre.dist).value + e.weight) | { //(e.relation.Vertex).(pre.dist).value + e.weight | {
			(curcost < (e.v2).(pre.dist).value) || (e.v2).(pre.dist).isInfinite = True => {//Vertex.(e.relation).(pre.dist) or  Vertex.(e.relation).(pre.dist).isInfinite = True => {
				//Vertex.(e.relation).(post.dist).value = curcost
				e.v2.(post.dist).value = curcost
				e.v2.(post.dist).isInfinite = False
			}
		}
	}
}


run {} for 4 but exactly 1 DirectedGraph,  5 Vertex, exactly 4 Edge,  4 relaxEdge


// Detect negative cycles
// get the path 125% deliverable 
