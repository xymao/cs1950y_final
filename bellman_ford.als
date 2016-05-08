open Graph
open util/ordering[State]
open util/integer
open util/boolean
//open util
// Bellman Ford Algorithm to find shortest path

sig State {
	graph: one DirectedGraph,
	dist: set Vertex -> Int,
	inf: set Vertex ->  Int,
	loopCounter: Int,
	src: one Vertex,

	// modifying 
	remainingEdges: set Edge,
	//	currentEdge: one Edge
} {
	#dist = #graph.vertices
	#inf = #graph.vertices
	dist.Int = graph.vertices
	inf.Int = graph.vertices
	src in graph.vertices
	Vertex.inf in {1 + 0}
	#remainingEdges >= 0
	#remainingEdges <= #(graph.edges)
	//all e: graph.edges | e.weight != 0
  	//let e = {a, b: graph.vertices| b in a.outgoing} | all a, b: graph.vertices | a->b in ^e

	// modifying 
	all e: remainingEdges | e in graph.edges
}

fact initialState {
	first.src.(first.inf) = 0 //and first.src.(first.dist) = 0
	all d: (first.graph.vertices).(first.dist) | d = 0
	all i: (first.graph.vertices-first.src).(first.inf) | i = 1 
	first.loopCounter = minus[#first.graph.vertices, 1]
	//first.src not in first.graph.vertices.outgoing
	//#(first.src.outgoing) = 1

	// modifying 
	first.remainingEdges = first.graph.edges
}

fact constraint {
	all s: State | {
		s.loopCounter >= 0 and s.loopCounter < #(s.graph.vertices)
	}
	all s: State - last | let s' = s.next | one e: Event | e.pre = s and e.post = s'
//	all s: State | #(s.graph.vertices-s.src).outgoing = 1
}

fact endState {
	last.loopCounter = 0
	//#last.remainingEdges = #last.graph.edges
}	


abstract sig Event {
	pre, post: State,
	currentEdge: one Edge
}

sig relaxEdge extends Event { } {
	// make sure they are the same graph
	post.graph = pre.graph
	post.src = pre.src
	all v : pre.graph.vertices - currentEdge.v2 | {
		v.(post.dist) = v.(pre.dist)
		v.(post.inf) = v.(pre.inf)
	}
	
	currentEdge in pre.remainingEdges
	#(pre.remainingEdges) > 1 => {
		currentEdge not in post.remainingEdges
		post.remainingEdges = pre.remainingEdges - currentEdge
		post.loopCounter = pre.loopCounter
	} else {
		post.loopCounter = minus[pre.loopCounter, 1]
		post.remainingEdges = pre.graph.edges
	}
	
	//(currentEdge.v1).(pre.dist) = (currentEdge.v1).(post.dist) 
	//(currentEdge.v1).(pre.inf) = (currentEdge.v1).(post.inf) 
	// relax edge
	currentEdge.v1.(pre.inf) < 1 => {
		let curcost = plus[currentEdge.v1.(pre.dist), currentEdge.weight] | {
			(currentEdge.v2).(pre.inf) > 0 => {
				(currentEdge.v2).(post.dist) = curcost
				(currentEdge.v2).(post.inf) = 0
				//(post.currentEdge.v1).(post.dist) = (post.currentEdge.v1).(post.dist)
			} else {
				curcost < (currentEdge.v2).(pre.dist) => {
					(currentEdge.v2).(post.dist) = curcost
					(currentEdge.v2).(post.inf) = 0
				} else {
					(currentEdge.v2).(pre.dist) = (currentEdge.v2).(post.dist) 
					(currentEdge.v2).(pre.inf) = (currentEdge.v2).(post.inf) 
				}
			}	
		}
	} else {
		(currentEdge.v2).(pre.inf) = (currentEdge.v2).(post.inf)
		(currentEdge.v2).(pre.dist) = (currentEdge.v2).(post.dist)  
	}
}
run { } for 10 State, 9 Event, exactly 1 DirectedGraph, exactly 3 Vertex, 3 Edge, 5 Int

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
