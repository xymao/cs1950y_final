open Graph
open util/ordering[State]
open util/integer
open util/boolean
//open util
// Bellman Ford Algorithm to find shortest path

sig State {
	graph: one DirectedGraph,
	dist: set Vertex -> Int,
	inf: set Vertex,
	loopCounter: Int,
	src: one Vertex,
	remainingEdges: set Edge,
	previous: set Vertex -> Vertex,
} {
	#dist = #graph.vertices
	dist.Int = graph.vertices
	all v: inf | v in graph.vertices
	src in graph.vertices
	#remainingEdges >= 0
	#remainingEdges <= #(graph.edges)
	all e: graph.edges | e.weight > 0
	all e: remainingEdges | e in graph.edges
	all v2: graph.vertices | #(previous.v2) <= 1 //only one pre
}

fact initialState {
	first.inf = first.graph.vertices - first.src
	all d: (first.graph.vertices).(first.dist) | d = 0
	first.loopCounter = minus[#first.graph.vertices, 1]
	first.remainingEdges = first.graph.edges
	#first.src.outgoing >0
	no first.previous 
}

fact constraint {
	all s: State | {
		s.loopCounter >= 0 and s.loopCounter < #(s.graph.vertices)
	}
	all s: State - last | let s' = s.next | one e: Event | e.pre = s and e.post = s'
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
		//(post.inf) = (pre.inf)
	}
		
	currentEdge in pre.remainingEdges
	currentEdge = (pre.remainingEdges)  => {
		post.loopCounter = minus[pre.loopCounter, 1]
		post.remainingEdges = pre.graph.edges
	} else {
		currentEdge not in post.remainingEdges
		post.remainingEdges = pre.remainingEdges - currentEdge
		post.loopCounter = pre.loopCounter
	}
	(post.previous).(currentEdge.v1) = (pre.previous).(currentEdge.v1)	

// relax edge
	currentEdge.v1 not in pre.inf => {
		let curcost = plus[currentEdge.v1.(pre.dist), currentEdge.weight] | {
			currentEdge.v2 in pre.inf => {
				(currentEdge.v2).(post.dist) = curcost
				post.inf = pre.inf - currentEdge.v2
				(post.previous).(currentEdge.v2) = currentEdge.v1
				currentEdge.v1 -> currentEdge.v2 in post.previous
			} else {
				curcost < (currentEdge.v2).(pre.dist) => {
					(currentEdge.v2).(post.dist) = curcost
					post.inf = pre.inf - currentEdge.v2
					(post.previous).(currentEdge.v2) = currentEdge.v1
					currentEdge.v1 -> currentEdge.v2 in post.previous
				} else {
					(currentEdge.v2).(pre.dist) = (currentEdge.v2).(post.dist) 
					pre.inf = post.inf
					post.previous = pre.previous
				}
			}	
		}
	} else {
		pre.inf = post.inf
		(currentEdge.v2).(pre.dist) = (currentEdge.v2).(post.dist)
		post.previous = pre.previous
	}
}
run { } for 7 State, 6 Event, exactly 1 DirectedGraph, exactly 3 Vertex, 3 Edge, 6 Int

// if there is no negative cycle, this should hold, even there is positive cycle
assert detectNegCycle {
	all e: last.graph.edges | 
		e.v1 not in last.inf => plus[e.v1.(last.dist), e.weight] >= e.v2.(last.dist)
}
check detectNegCycle for exactly 7 State, 6 Event, exactly 1 DirectedGraph, exactly 3 Vertex,  3 Edge, 5 Int

