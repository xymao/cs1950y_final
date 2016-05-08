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

	// modifying 
	remainingEdges: set Edge,
	currentEdge: one Edge

} {
	#dist = #graph.vertices
	#inf = #graph.vertices
	dist.Int = graph.vertices
	inf.Int = graph.vertices
	Vertex.inf in {1 + 0}
	//all e: graph.edges | e.weight != 0
  	//let e = {a, b: graph.vertices| b in a.outgoing} | all a, b: graph.vertices | a->b in ^e

	// modifying 
	all e: remainingEdges | e in graph.edges
	currentEdge in remainingEdges
}

fact initialState {
	first.src.(first.inf) = 0 //and first.src.(first.dist) = 0
	all d: (first.graph.vertices).(first.dist) | d = 0
	all i: (first.graph.vertices-first.src).(first.inf) | i = 1 
	first.src in first.graph.vertices
	first.loopCounter = minus[#first.graph.vertices, 1]
	first.src not in first.graph.vertices.outgoing
	//#(first.src.outgoing) = 1

	// modifying 
	first.remainingEdges = first.graph.edges
}

fact constrains {
	all s: State | {
		s.loopCounter >= 0 and s.loopCounter < #(s.graph.vertices)
		s.currentEdge in s.remainingEdges
	}
	all s: State - last | let s' = s.next | one e: Event | e.pre = s and e.post = s'
//	all s: State | #(s.graph.vertices-s.src).outgoing = 1
}

fact endState {
	last.loopCounter = 0
	#last.remainingEdges = 1
}	


abstract sig Event {
	pre, post: State
}

sig relaxEdge extends Event { } {
	// make sure they are the same graph
	post.graph = pre.graph
	post.src = pre.src
	// check if all edges have been relaxed once in this outer loop
	
	
	#(pre.remainingEdges) = 1 => {
		post.loopCounter = minus[pre.loopCounter, 1]
		post.remainingEdges = pre.graph.edges
		post.currentEdge in post.remainingEdges
	} else {
		pre.remainingEdges = post.remainingEdges + pre.currentEdge
		(pre.currentEdge.v1).(pre.dist) = (pre.currentEdge.v1).(post.dist) 
		(pre.currentEdge.v1).(pre.inf) = (pre.currentEdge.v1).(post.inf) 
		// relax edge
		pre.currentEdge.v1.(pre.inf) = 0 => {
			let curcost = plus[pre.currentEdge.v1.(pre.dist), pre.currentEdge.weight] | {
				(pre.currentEdge.v2).(pre.inf) = 1 => {
					(pre.currentEdge.v2).(post.dist) = curcost
					(pre.currentEdge.v2).(post.inf) = 0
					//(post.currentEdge.v1).(post.dist) = (post.currentEdge.v1).(post.dist)
				} else {
					curcost < (pre.currentEdge.v2).(pre.dist) => {
						(pre.currentEdge.v2).(post.dist) = curcost
						(pre.currentEdge.v2).(post.inf) = 0
					} else {
						(pre.currentEdge.v2).(pre.dist) = (pre.currentEdge.v2).(post.dist) 
						(pre.currentEdge.v2).(pre.inf) = (pre.currentEdge.v2).(post.inf) 
					}
				}	
			}
		} else {
			(pre.currentEdge.v2).(pre.inf) = (pre.currentEdge.v2).(post.inf) 
		}
	}
	

	/*relax one edge at a time
	all e: pre.currentEdge | 
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
		}*/
}
run { } for 7 State, 6 Event, exactly 1 DirectedGraph, exactly 3 Vertex, 3 Edge, 5 Int
// if there is no negative cycle, this should hold, even there is positive cycle
assert correctness {
	all e: last.graph.edges | 
		e.v1.(last.inf) = 0 => plus[e.v1.(last.dist), e.weight] >= e.v2.(last.dist)
}
check correctness for 10 State, 9 Event, exactly 1 DirectedGraph, exactly 3 Vertex,  3 Edge, 5 Int

assert detectNegCycle {
	all e: last.graph.edges | 
		e.v1.(last.inf) = 0 => plus[e.v1.(last.dist), e.weight] < e.v2.(last.dist)
}




// Detect negative cycles
// get the path 125% deliverable 
