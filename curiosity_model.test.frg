#lang forge/bsl

open "curiosity_model.frg"
//// Do not edit anything above this line ////

----------------------------------------------------------------------

------- TESTING PREDICATES -------

------- TEST SUITES -------

test suite for wellformed {
    test expect {
        isCyclic: {
            wellformed implies {all p: Person | reachable[p, p, successor]}
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is theorem 
        noNonCyclicInstances: {
            wellformed
            some p: Person | not reachable[p, p, successor]
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is unsat
        fullyConnected: {
            wellformed implies {all p1, p2: Person | reachable[p1, p2, successor]}
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is theorem 
        noNotFullyConnected: {
            wellformed
            some p1, p2: Person | not reachable[p1, p2, successor]
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is unsat 
    }
}

test suite for init {
    test expect {
        allPeopleAreAlive: {
            some t: State | init[t] implies {all p: Person | t.isDead[p] = False}
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is theorem
        somePersonIsDead: {
            some t: State | init[t] and (some p: Person | t.isDead[p] = True)
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is unsat
        startsAtAPersonInTheCircle: {
            some t: State | init[t] implies {
                some t.person
            }
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is theorem
        countStartsAtZero: {
            some t: State | init[t] implies {
                t.count = 0
            }
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is theorem
    }
}

test suite for doNothing {
    test expect {
        countStaysSame: {
            some t1, t2: State | doNothing[t1, t2] implies {t1.count = t2.count}
        } for exactly 5 Person, 2 State for {next is linear} is theorem
        lifeStatusStaysSame: {
            some t1, t2: State | doNothing[t1, t2] implies {
                lifeStatusUnchanged[t1, t2]
            }
        } for exactly 5 Person, 2 State for {next is linear} is theorem
    } 
}

test suite for removePerson {
    test expect {
        countResets: {
            some t1, t2: State | removePerson[t1, t2] implies {t2.count = 0}
        } for exactly 5 Person, 2 State for {next is linear} is theorem
        lifeStatusStaysSameExceptPerson: {
            some t1, t2: State | removePerson[t1, t2] implies {
                lifeStatusUnchangedExcept[t1, t2, t2.person]
            }
        } for exactly 5 Person, 2 State for {next is linear} is theorem
        personRemoved: {
            some t1, t2: State | removePerson[t1, t2] implies {t2.isDead[t2.person] = True}
        } for exactly 5 Person, 2 State for {next is linear} is theorem
    }
}

test suite for incrementCount {
    test expect {
        countIncrements: {
            some t1, t2: State | incrementCount[t1, t2] implies {add[t1.count, 1] = t2.count}
        } for exactly 5 Person, 2 State for {next is linear} is theorem
        lifeStatusStaysSameWhenIncrementCount: {
            some t1, t2: State | incrementCount[t1, t2] implies {
                lifeStatusUnchanged[t1, t2]
            }
        } for exactly 5 Person, 2 State for {next is linear} is theorem
        countIsNotPersonSkipped: {
            some t1, t2: State | incrementCount[t1, t2] implies {t2.count != Circle.personSkipped}
        } for exactly 5 Person, 2 State for {next is linear} is theorem
    }
}

test suite for lifeStatusUnchanged {
    test expect {
        noPersonLifeStatusChanged: {
            some t1, t2: State | lifeStatusUnchanged[t1, t2] implies {
                all p: Person | t1.isDead[p] = t2.isDead[p]
            }
        } for exactly 5 Person, 2 State for {next is linear} is theorem
        somePersonLifeStatusChanged: {
            some t1, t2: State | lifeStatusUnchanged[t1, t2] and (
                some p: Person | t1.isDead[p] != t2.isDead[p]
            )
        } for exactly 5 Person, 2 State for {next is linear} is unsat
    }
}

test suite for traces {
    -- Underconstraints
    test expect {
        canDoNothing: {
            traces
            some t1, t2: State | doNothing[t1, t2]
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is sat
        canRemovePerson: {
            traces
            some t1, t2: State | removePerson[t1, t2]
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is sat
        canIncrementCount: {
            traces
            some t1, t2: State | incrementCount[t1, t2]
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is sat
        negative_person_skipped: {
            traces
            Circle.personSkipped = -1
        } for exactly 3 Person, 6 State for {next is linear} is unsat
        initStateIsFirstState: {
            traces implies init[Circle.firstState]
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is theorem
        endStateDoesNothing: { -- which means that an end state stays ending
            traces
            all t1, t2: State | endState[t1] and validTransition[t1, t2] implies {
                doNothing[t1, t2]
            }
        } for exactly 5 Person, 20 State, 6 Int for {next is linear} is sat
    }

    -- Overconstraints
    test expect {
        noPersonGoesFromDeadToAlive: {
            traces
            some t1, t2: State, p: Person | t2.id > t1.id and (
                (t1.isDead[p] = True) and (t2.isDead[p] = False)
            )
        } for exactly 5 Person, 11 State, 5 Int for {next is linear} is unsat
        endStateStopsEnding: {
            traces
            eventuallyEnds
            some t1, t2: State | endState[t1] and validTransition[t1, t2] and not(doNothing[t1, t2])
        } for exactly 5 Person, 20 State, 6 Int for {next is linear} is unsat
    }

    -- Examples
    test expect {
        successful_3_people_2_skipped: {
            traces
            eventuallyEnds
            Circle.personSkipped = 2
        } for exactly 3 Person, 6 State for {next is linear} is sat
        failed_3_people_2_skipped: {
            traces
            eventuallyEnds
            Circle.personSkipped = 2
        } for exactly 3 Person, 3 State for {next is linear} is unsat
        successful_5_people_3_skipped: {
            traces
            eventuallyEnds
            Circle.personSkipped = 3
        } for exactly 5 Person, 18 State, 6 Int for {next is linear} is sat
        failed_5_people_3_skipped: {
            traces
            eventuallyEnds
            Circle.personSkipped = 3
        } for exactly 5 Person, 17 State, 6 Int for {next is linear} is unsat
    }
}