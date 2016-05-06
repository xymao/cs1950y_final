open Graph
open util/ordering[State]
open util/boolean
open util
// Bellman Ford Algorithm to find shortest path

sig State {
	graph: one DirectedGraph,
	dist: set Vertex -> Cost, //  Int // update 
	//remainingEdges: set Edge
	loopCounter: Int,// for 4 Int
	src: one Vertex,

} {
	#dist = #graph.vertices
	dist.Cost = graph.vertices

}

fact initialState {
	//remainingEdges = first.graph.edges
	// all vertex -> to infinity (very large number
	all d: (first.graph.vertices-first.src).(first.dist) | d.isInfinite = 1
	//all v: first.graph.vertices
	first.src in first.graph.vertices
	first.src.(first.dist).isInfinite = 0 and first.src.(first.dist).value = 0
	first.loopCounter = #first.graph.edges

}

fact constrains {
	all s: State | {
		s.loopCounter > 0 //and s.loopCounter <= #(graph.edges)
	}
	all s: State - last | let s' = s.next | one e: Event | e.pre = s and e.post = s'
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
	post.loopCounter = minus[pre.loopCounter, 1]
	// relax one edge at a time
	all e: pre.graph.edges & post.graph.edges | {
		let curcost = plus[e.v1.(pre.dist).value, e.weight] | {
 				e.v2.(post.dist).value = curcost
				e.v2.(post.dist).isInfinite = 0
			((e.v2).(pre.dist).isInfinite = 1) => {
				//post.dist[e.v2].value = curcost
				//post.dist[e.v2].isInfinite = 0
				//post.src = e.v2
			}
		}
	}
}


run {} for 4 but exactly 1 DirectedGraph,  5 Vertex, exactly 4 Edge, 5 Int


// Detect negative cycles
// get the path 125% deliverable 
