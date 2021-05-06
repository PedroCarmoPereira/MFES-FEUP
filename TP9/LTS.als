/*
A labeled transition system (LTS) is comprised by States, a sub-set
of which are Initial, connected by transitions, here represented by 
Events.
*/
sig State {
        trans : Event -> State
}
sig Init in State {}
sig Event {}

/*
The LTS does not contain deadlocks, ie, each state has at least a 
transition.
*/
pred inv1 {
	all s:State | some s.trans
}

/*
There is a single initial state.
*/
pred inv2 {
	one Init
}

/*
The LTS is deterministic, ie, each state has at most a transition for each event.
*/
pred inv3 {
  all s:State, e:Event | lone e.(s.trans)
}

/*
All states are reachable from an initial state.
*/
pred inv4 {
  	//ts is the set of all transitions possible, but why is it != than i.^trans?
  	let ts = {s1,s2:State | some e:Event | s1->e->s2 in trans} |
		all s:State | some i:Init | s in i.^ts
}

/*
All the states have the same events available.
*/
pred inv5 {
	all disj s1, s2:State, e:Event | some e.(s1.trans) implies some e.(s2.trans)
}

/*
Each event is available in at least a state.
*/
pred inv6 {
  all e:Event | some s:State | some e.(s.trans)

}

/*
The LTS is reversible, ie, from a reacheable state it is always possible 
to return to an initial state.
*/
pred inv7 {
 	let ts = {s1,s2:State | some e:Event | s1->e->s2 in trans} |
		all s:Init.^ts | some i:Init | i in s.^ts
}

