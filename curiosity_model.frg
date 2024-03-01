#lang forge/bsl

---- SIGS ----

abstract sig Boolean {}
one sig True, False extends Boolean {}

one sig Circle {
	firstState: one State,
	next: pfunc State -> State,
	personSkipped: one Int
}

sig Person {  
    successor: one Person
}

sig State {
    id: one Int,
    person: one Person,
	count: one Int,
    isDead : func Person -> Boolean
}

---- STATE CONSTRAINTS ----

-- Defines well-formedness
pred wellformed {
    -- All people should be reachable. People should form a circle.
    all p1, p2 : Person | {
        reachable[p1, p2, successor]
    }
}

-- Defines the initial state
-- Every person should be alive in the initial state, and 
-- someone is selected as the person to start counting from.
pred init [t: State] {
    t.id = 1
    t.count = 0
    some t.person
    -- All people are alive
    all p: Person | {
        t.isDead[p] = False
    }
}

-- Defines the state where the model has ended
pred endState[t: State] {
    #{p: Person | t.isDead[p] = False} = 1
}

---- TRANSITION HELPERS ----

-- The life status of all people remains unchanged
pred lifeStatusUnchanged[t1, t2 : State] {
    all p : Person | {
        t1.isDead[p] = t2.isDead[p]
    }
}

-- The life status of all people, except the given person, remains unchanged
pred lifeStatusUnchangedExcept[t1, t2 : State, p: Person] {
    all other_p : Person | other_p != p implies {
        t1.isDead[other_p] = t2.isDead[other_p]
    }
}

---- TRANSITION PREDICATES ---- 

-- Do nothing between states
pred doNothing[t1, t2: State] {
    -- GUARD
    -- Only run when the next person is already dead
    (t1.isDead[t2.person] = True) or (endState[t1])

    -- ACTION/FRAME
    t2.count = t1.count
    lifeStatusUnchanged[t1,t2]
}

-- Remove the t1.person
pred removePerson[t1, t2: State] {
    -- GUARD 
    // t2.id = add[t1.id, 1]
    // t2.person = t1.person.successor
    -- Next person is alive AND the count will increment to 2
    t1.isDead[t2.person] = False
    add[t1.count, 1] = Circle.personSkipped
    not endState[t1]

    -- ACTION
    t2.count = 0
    all t : State | {
        t.id >= t2.id implies t.isDead[t2.person] = True
    }

    -- FRAME
    lifeStatusUnchangedExcept[t1, t2, t2.person]
}

-- Increment the count and do nothing else
pred incrementCount[t1, t2: State] {
    -- GUARD
    -- Next person is alive AND the count will NOT increment to 2
    t1.isDead[t2.person] = False
    add[t1.count, 1] != Circle.personSkipped
    not endState[t1]

    -- ACTION
    t2.count = add[t1.count, 1]

    -- FRAME
    lifeStatusUnchanged[t1,t2]
}

-- A valid transition is taken between two states; t2.person is updated
pred validTransition[t1, t2 : State] {
    -- GUARD
    t2.id = add[t1.id, 1]
    t2.person = t1.person.successor

    -- ACTION
    doNothing[t1, t2] or removePerson[t1, t2] or incrementCount[t1, t2]
}

---- MODEL HELPERS ----

-- Model reaches an end state
pred eventuallyEnds {
    some t: State | endState[t]
}

---- MODEL ----

-- Core of the model
pred traces {
    Circle.personSkipped > 0
    wellformed
    init[Circle.firstState] 
    no prev : State | Circle.next[prev] = Circle.firstState -- first state doesn't have a predecessor
    -- all state transitions should satisfy step
    all t: State | {
        some Circle.next[t] implies validTransition[t, Circle.next[t]]
    }
}

---- RUN STATEMENTS ----

-- Checking valid initial states
// run {some t: State | init[t]} for 5 Person, 1 State

-- 2 people skipped, 3 people, 6 states
-- starting person (Person2) wins
run {
    traces
    eventuallyEnds
    Circle.personSkipped = 2
} for exactly 3 Person, 6 State for {next is linear}

-- 2 people skipped, 5 people, 11 states
-- Person1 is the winner; two predecessor's before Person4 (starting person)
// run {
//     traces
//     eventuallyEnds
//     Circle.personSkipped = 2
// } for exactly 5 Person, 11 State, 5 Int for {next is linear}

-- 3 people skipped, 5 people, 18 states
-- Person0 is the winner; Person4's (starting person) predecessor 
// run {
//     traces
//     eventuallyEnds
//     Circle.personSkipped = 3
// } for exactly 5 Person, 18 State, 6 Int for {next is linear}
