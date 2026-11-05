# Label Structural Conditions

Required child-box composition per concrete label (see labels.md for the tree).
A child "counts as X" if its is-a path's head is X or an is-a subtype of X.
`commentary` children are optional (0+) and never counted toward conditions.
Checks are SOFT: a box violating these is flagged as a loose end, not blocked.

Labels not listed here impose no condition (any/empty children), except leaves
(has-a bases) which must have no children other than commentary.

| label | required children |
|---|---|
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
| variable | exactly 1 variable-symbol |
| constant | exactly 1 constant-symbol |

Notes:
- definition: no structural condition (it IS-A a term/formula; its content box is
  that term/formula; may carry optional commentary).
- the symbol child's identity (∧ for conjunction, = for equality, …) is implied
  by the parent label and not separately checked.
- a composite label with missing/incomplete required children = loose end.
- unlabelled box = loose end.
