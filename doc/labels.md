# Box Labels

- **is-a**: a label is a more specific kind of its parent (a `relation` IS-A `formula`).
  Only concrete (is-a base) labels can be assigned; abstract ones can't.
- **has-a**: a box decomposes into child boxes with these labels. A has-a slot
  accepts the label OR any is-a subtype of it (a `formula` slot accepts `relation`,
  `universal`, …).

Markers: indented = child. `[isa]`/`[hasa]` = relation to its children.
`(base)` = leaf (has-a base; judged ok/not-ok). `→X` = subtype expands per X above.

- root [hasa]
  - commentary (base)
  - definition
  - theorem
  - organizer-section
- organizer-section [hasa]
  - →commentary
  - →definition
  - →theorem
  - →organizer-section
- definition
  - [isa]
    - →term
    - →formula
  - [hasa]
    - →commentary
- theorem [hasa]
  - →formula
  - →proof
  - →commentary
- proof [hasa]
  - →formula
  - →theorem
  - →commentary
  - tactic (base)
- formula [isa]
  - external-citation (base)
  - atomic-formula [isa]
    - relation [hasa]
      - relation-symbol (base)
      - →term
    - equality [hasa]
      - equality-symbol (base)
      - →term
  - compound-formula [isa]
    - quantified [isa]
      - universal [hasa]
        - quantifier (base)
        - variable-symbol (base)
        - →formula
      - existential [hasa]
        - quantifier (base)
        - variable-symbol (base)
        - →formula
    - connective [isa]
      - negation [hasa]
        - connective-symbol (base)
        - →formula
      - implication [hasa]
        - connective-symbol (base)
        - →formula
      - conjunction [hasa]
        - connective-symbol (base)
        - →formula
      - disjunction [hasa]
        - connective-symbol (base)
        - →formula
- term [isa]
  - external-citation (base)
  - implicit-external-reference (base)
  - atomic-term [isa]
    - variable [hasa]
      - variable-symbol (base)
    - constant [hasa]
      - constant-symbol (base)
  - composite-term [isa]
    - function-application [hasa]
      - function-symbol (base)
      - →term
