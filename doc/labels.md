# Box Labels

- **is-a**: a label is a more specific kind of its parent (a `relation` IS-A `formula`).
  Only concrete (is-a base) labels can be assigned; abstract ones can't.
- **has-a**: a box decomposes into child boxes with these labels. A has-a slot
  accepts the label OR any is-a subtype of it (a `formula` slot accepts `relation`,
  `universal`, …).

Markers: indented = child. `[isa]`/`[hasa]` = relation to its children.
`(base)` = leaf (has-a base; judged ok/not-ok). `→X` = subtype expands per X above.

A box may be IMPLICIT (no text span, `pieces:[]`, `implicit:true`) — for symbols
with no glyph, e.g. the ∧ hidden in "sets I, J". Implicit boxes are labelled like
any box, draw no highlight, and are excluded from coverage.

`commentary` is auto-allowed as a child of EVERY composite (non-leaf) box — any
span with no formal role (whitespace, glue punctuation, meta-prose) is commentary
— so it is NOT listed under each node below.

- root [hasa]
  - definition
  - theorem
  - organizer-section
- organizer-section [hasa]
  - →definition
  - →theorem
  - →organizer-section
- definition [hasa]
  - name (base)              (the definiendum — symbol being defined)
  - inputs [hasa]
    - →term                  (the bound objects: G, D, T, …)
  - conditions [hasa]
    - →formula               (typing/constraints: finite graph, ⊆ I×J, …)
  - →body
- body [isa]                 (the `:=` meaning)
  - →term
  - →formula
- theorem [hasa]
  - →formula
  - →proof
- proof [hasa]
  - →formula
  - →theorem
  - tactic (base)
- formula [isa]
  - external-citation (base)
  - atomic-formula [isa]
    - relation [hasa]
      - →relation-symbol
      - →term
    - equality [hasa]
      - →equality-symbol
      - →term
  - compound-formula [isa]
    - quantified [isa]
      - universal [hasa]
        - →quantifier
        - →variable-symbol
        - →formula
      - existential [hasa]
        - →quantifier
        - →variable-symbol
        - →formula
    - connective [isa]
      - negation [hasa]
        - →connective-symbol
        - →formula
      - implication [hasa]
        - →connective-symbol
        - →formula
      - conjunction [hasa]
        - →connective-symbol
        - →formula
      - disjunction [hasa]
        - →connective-symbol
        - →formula
- term [isa]
  - external-citation (base)
  - implicit-external-reference (base)
  - atomic-term [isa]
    - variable (base)        (the term IS the variable — no child)
    - constant (base)
  - composite-term [isa]
    - function-application [hasa]
      - →function-symbol
      - →term
- symbol [isa]              (Def 5.1 — the symbols of a first-order language)
  - logical [isa]          (shared by every first-order language)
    - parenthesis (base)
    - connective-symbol (base)
    - quantifier (base)
    - variable-symbol (base)
    - equality-symbol (base)
  - non-logical [isa]      (depend on the language)
    - constant-symbol (base)
    - function-symbol (base)
    - relation-symbol (base)
