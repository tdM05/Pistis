# Label Structural Conditions (auto-generated from schema.json)

Required child composition per label. A child counts as a slot if its concrete label IS-A the slot. commentary never counts.

| label | required children |
|---|---|
| definition | 1 name, 1 body |
| theorem | 1 formula, 1 proof |
| relation | 1 relation-symbol, 1+ term |
| equality | 1 equality-symbol, 2 term |
| universal | 1 quantifier, 1 variable-symbol, 1 formula |
| existential | 1 quantifier, 1 variable-symbol, 1 formula |
| negation | 1 connective-symbol, 1 formula |
| implication | 1 connective-symbol, 2 formula |
| conjunction | 1 connective-symbol, 2 formula |
| disjunction | 1 connective-symbol, 2 formula |
| function-application | 1 function-symbol, 1+ term |

## Declared argument count (user must set box.count = number of)

| label | counted slot |
|---|---|
| inputs | term |
| conditions | formula |
| relation | term |
| function-application | term |

## Auto-derived symbols (identity fixed by parent)

| symbol label | parent → symbol |
|---|---|
| connective-symbol | conjunction→∧, implication→→, disjunction→∨, negation→¬ |
| quantifier | universal→∀, existential→∃ |
| equality-symbol | equality→= |
