# Label Structural Conditions

Required child-box composition per concrete label (see labels.md for the tree).
A child "counts as X" if its is-a path's head is X or an is-a subtype of X.
`commentary` children are optional (0+) and never counted toward conditions.
Checks are SOFT: a box violating these is flagged as a loose end, not blocked.

Labels not listed here impose no condition (any/empty children), except leaves
(has-a bases) which must have no children other than commentary.

## Declared argument count
These labels have a meaningful, easily-miscounted arity, so the user MUST declare
the intended number of arguments (box.count); the actual child count of that slot
must equal it. A missing count is itself a loose end (so you can't forget to
separate arguments).

| label | counted slot |
|---|---|
| inputs | term |
| conditions | formula |
| relation | term |
| function-application | term |

| label | required children |
|---|---|
| definition | exactly 1 name, exactly 1 body (inputs/conditions 0+) |
| theorem | exactly 1 formula, exactly 1 proof |
| relation | exactly 1 relation-symbol, 1+ term |
| equality | exactly 1 equality-symbol, exactly 2 term |
| universal | exactly 1 quantifier, 1 variable-symbol, 1 formula |
| existential | exactly 1 quantifier, 1 variable-symbol, 1 formula |
| negation | exactly 1 connective-symbol, exactly 1 formula |
| implication | exactly 1 connective-symbol, exactly 2 formula |
| conjunction | exactly 1 connective-symbol, exactly 2 formula |
| disjunction | exactly 1 connective-symbol, exactly 2 formula |
| function-application | exactly 1 function-symbol, 1+ term |

Notes:
- definition HAS-A: name (definiendum), inputs (bound objects, each a term),
  conditions (typing/constraints, each a formula), body (the `:=` meaning, is-a
  term/formula). name + body required; inputs/conditions optional (0+).
- the symbol child's identity (∧ for conjunction, = for equality, …) is implied
  by the parent label and not separately checked.
- a composite label with missing/incomplete required children = loose end.
- unlabelled box = loose end.
