for all these they are equivlaent. so if we check the compiled thing,k can we tell? like compile al 4, underthe hood it looks the same and we could check it

Yes—for those four forms, exactly. Once placed in the same parameter context, they elaborate to the same core proposition:
Π(x:A), P(x).
Π(x:A),P(x).

You would inspect the elaborated statement—the type of the theorem constant—not its proof or compiled executable code.

Then you can mechanically:

    Ignore bound-variable names and irrelevant metadata.
    Compare the resulting expression trees.

For these examples, they match. That structural comparison is deterministic and takes linear time in the size of the explicit trees.

This handles different Lean spellings of the same underlying statement. Logically equivalent statements with different underlying structures, such as P ∧ Q versus Q ∧ P, would still differ.
how would you do that? where in the lean? compile and then where

The object you want is ConstantInfo.type : Lean.Expr in Lean’s environment. It contains the theorem’s elaborated statement as a syntax tree.

Add import Lean at the top of your file, then place this after the completed theorem:
open Lean

run_elab do
  let info ← getConstInfo ``OAI.kernel_support

  -- Human-readable statement:
  logInfo m!"{info.type}"

  -- Underlying expression constructors:
  logInfo m!"{reprStr info.type}"

Run it from your Lean project:

lake env lean YourFile.lean

You can also view the messages in the editor’s Lean Infoview. run_elab executes during elaboration; you do not need to produce an executable.

For an actual comparison, here is a small standalone example:
import Lean
open Lean

theorem form1 (n : Nat) : n = n := rfl

theorem form2 : ∀ k : Nat, k = k :=
  fun k => rfl

run_elab do
  let a ← getConstInfo ``form1
  let b ← getConstInfo ``form2

  logInfo m!"Same structure: {a.type.eqv b.type}"

The expected result is:
Same structure: true

Expr.eqv performs the structural comparison up to bound-variable renaming, ignoring binder annotations. Here it recognizes that n and k play the same role.

After a project build, the elaborated declarations are stored in .olean files, normally under .lake/build/. To inspect an already-built theorem, create another Lean file that imports its module and use the same getConstInfo call. Importing loads the declaration into the environment; you access its .type rather than parsing the .olean binary yourself. 