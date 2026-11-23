You are given a SEGMENT of the natural-language text of a mathematics paper, and
the Lean 4 formalization (or the relevant part of it). Decide whether THIS segment
is FAITHFULLY formalized by the Lean: does the Lean assert exactly what the segment
asserts — same statement, same hypotheses, same quantifiers, same direction of
inequalities, nothing dropped, weakened, strengthened, or altered?

Output ONLY a JSON object, nothing else (no prose before or after, first char `{`,
last char `}`):

{"verdict": "faithful" | "unfaithful", "reason": "<your explanation. If unfaithful, state exactly what the Lean says vs. what the NL says and how they differ. If faithful, briefly say why.>"}

Notes:
- Judge ONLY the content of this segment against the Lean. If the segment is pure
  commentary / motivation with no formal claim to check, answer "faithful" with a
  reason that says it states no formal claim.

=== NATURAL-LANGUAGE SEGMENT ===
{{NL}}

=== LEAN FORMALIZATION ===
{{LEAN}}
