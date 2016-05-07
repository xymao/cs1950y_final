open Graph
open util/ordering[State]
open util/integer
open util/boolean
//open util
// Bellman Ford Algorithm to find shortest path

sig State {
	graph: one DirectedGraph,
	dist: set Vertex -> Int,
	inf: set Vertex -> Int,
	loopCounter: Int,
	src: one Vertex,

} {
	#dist = #graph.vertices
	#inf = #graph.vertices
	dist.Int = graph.vertices
	inf.Int = graph.vertices
	Vertex.inf in {1 + 0}

}

fact initialState {
	first.src.(first.inf) = 0 and first.src.(first.dist) = 0
	all d: (first.graph.vertices-first.src).(first.inf) | d = 1 
	first.src in first.graph.vertices
	first.loopCounter = #first.graph.vertices
	first.src not in first.graph.vertices.outgoing
	#(first.src.outgoing) = 1
}

fact constrains {
	all s: State | {
		s.loopCounter > 0 and s.loopCounter <= #(s.graph.vertices) 
	}
	all s: State - last | let s' = s.next | one e: Event | e.pre = s and e.post = s'
//	all s: State | #(s.graph.vertices-s.src).outgoing = 1
}

fact endState {
	last.loopCounter = 1
}	


abstract sig Event {
	pre, post: State
}

sig relaxEdge extends Event { } {
	// make sure they are the same graph
	post.graph = pre.graph
	post.loopCounter = minus[pre.loopCounter, 1]
	post.src = pre.src
	post.src.(post.dist) = 0
	//all v: post.graph.vertices | v.(post.inf) = 0
//	all v: post.v.
	// relax one edge at a time
//	all v: pre.graph.vertices | v.(pre.dist).isInfinite = 0 => v.(post.dist).isInfinite = 0
	all e: pre.graph.edges | 
		e.v1.(pre.inf) = 0 => {
		let curcost = plus[e.v1.(pre.dist), e.weight] | {
			((e.v2).(pre.inf) = 1) => {
				e.v2.(post.dist) = curcost
				e.v2.(post.inf) = 0
			} else {
				curcost < (e.v2).(pre.dist) => {
					e.v2.(post.dist) = curcost
					e.v2.(post.inf) = 0
				} else {
					e.v2.(post.dist) = e.v2.(pre.dist)
					e.v2.(post.inf) = e.v2.(pre.inf)
				}
			}
		}
		} else {
			e.v1.(post.inf) = e.v1.(pre.inf)
			e.v2.(post.inf) = e.v2.(pre.inf)
		}
}


run { } for exactly 4 State, 3 Event, exactly 1 DirectedGraph, exactly 4 Vertex,  exactly 3 Edge, 5 Int


// Detect negative cycles
// get the path 125% deliverable 
