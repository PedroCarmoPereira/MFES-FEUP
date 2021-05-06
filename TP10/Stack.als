open util/ordering[StackState]

sig Element {}

sig StackState {
    elements: seq Element
}{
    //
   elements.isEmpty
}

abstract sig Event {
    pre, post: StackState
}{
    // constraints that should hold for each Event
}

pred init [s: StackState] {
	s.elements.isEmpty
}

//run {}

fact trace {
    init [first]
    no p:Pop | init [p.pre]
    // relate all `StackState`s and `Event`s 
}

sig Push extends Event {
    value: Element
}{
    // -- model pushing by relating `pre`, `post`, and `value`
    value = post.elements.first
    // same as below: post.elements = pre.elements.insert [0, value]
    post.elements.rest = pre.elements  
}

sig Pop extends Event {
    //
}{
    // -- model popping
   post.elements = pre.elements.butlast
}

assert popThenPush {
    // ...
   all pop:Pop | one push:Push | push.value = pop.pre.elements.first implies StackState.elements.last = push.value
}
check popThenPush


assert sameNumberPushesPops {
    // ...
	 #Pop = #Push implies StackState.elements.isEmpty
}
check sameNumberPushesPops


assert noPopFromEmpty {
    // ...
   StackState.elements.isEmpty implies no Pop
}
check noPopFromEmpty
