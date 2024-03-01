# Project Description

This project implements a model of the Josephus Circle problem

## Background story

The Josephus Circle problem is a famous theoretical problem in mathematics and computer science. The problem is named after Flavius Josephus, a Jewish historian who lived in the 1st century. According to Josephus's own account, during the Jewish-Roman War, he and his 40 soldiers were trapped in a cave, surrounded by Roman soldiers. They chose suicide over capture and decided to form a circle and, proceeding around it, to kill every third person remaining until no one was left. Josephus, preferring capture to death, figured out where he needed to sit to be the last survivor. Using this strategy, he was able to survive and later surrendered to the Romans.

The Josephus problem is a classic example of a survival problem and has various applications in computer science, particularly in the fields of algorithms and data structures. It is often used to illustrate algorithmic thinking and problem-solving techniques. There are recursive algorithms to solve the Josephus problem for any given number of people `n` and step size `m`.<br>
Here is the recursive function $J(n, m)$, where $n$ is the number of people in the circle, $m$ is the step count at which individuals are eliminated, and $J(n, m)$ is the position of the last remaining person. The formula is defined as:

$$
J(n, m) = \begin{cases}
0 & \text{if } n = 1, \\
(J(n-1, m) + m) \mod n & \text{if } n > 1.
\end{cases}
$$

## Forge model

Just click run to run this model.

### 1. Project Objective

We were trying to model the Josephus Circle Problem described above. We hoped to use Forge to calculate who survives to the end.

### 2. Model Design and Visualization

We didn't create a custom visualization. Because the number of parameters is so large, we recommended to observe by time projecting to each STATE. By constantly clicking the next state, we can observe the whole process.

We ran `traces` on different values for `Circle.personSkipped`, which is the number of people that are skipped before someone is removed. Run `State0.person` in the Sterling Evaluator to see the starting person. We stepped through each `State` to confirm that the model ran correctly. To boost our confidence even more, we tested each predicate in `test expect` blocks, with some tests in the `traces` test suite that mirrors our `run` statements for different inputs for this problem.

### 3. Signatures and Predicates

- `Circle` is a trace of the entire model trace, similar to the trace in the ring election lab.
- `Person` refers to each person, they are connected to form a ring at the beginning and the end.
- `State` refers to the state of each second, assuming that every second is counted. Unlike in reality, dead people also count in his moment.
- `wellformed`, `init`, and `endState` are helper predicates to constrain certain states in our model.
- `validTransitions` contains `doNothing`, `incrementCount`, and `removePerson`. These are the valid transitions between states in our model.
- `traces` is the predicate that outputs consecutive states of our model.
- The remaining predicates are helpers for the predicates listed above.

### 4. Testing

For the model itself (`traces`), we wrote some tests that mirrored our `run` statements (i.e. examples of the Josephus Circle Problem).

For the other predicates, we wrote tests that asserted theorems that each predicate should require.

### 5. Documentation

See code for comments.
