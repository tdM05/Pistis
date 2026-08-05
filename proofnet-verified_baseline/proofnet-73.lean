import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators



/-Informal Statement

Let $G$ be a group in which $(a b)^{3}=a^{3} b^{3}$ and $(a b)^{5}=a^{5} b^{5}$ for all $a, b \in G$. Show that $G$ is abelian.
-/

/-Informal Proof

We have
$$
\begin{aligned}
& (a b)^3=a^3 b^3, \text { for all } a, b \in G \\
\Longrightarrow & (a b)(a b)(a b)=a\left(a^2 b^2\right) b \\
\Longrightarrow & a(b a)(b a) b=a\left(a^2 b^2\right) b \\
\Longrightarrow & (b a)^2=a^2 b^2, \text { by cancellation law. }
\end{aligned}
$$
Again,
$$
\begin{aligned}
& (a b)^5=a^5 b^5, \text { for all } a, b \in G \\
\Longrightarrow & (a b)(a b)(a b)(a b)(a b)=a\left(a^4 b^4\right) b \\
\Longrightarrow & a(b a)(b a)(b a)(b a) b=a\left(a^4 b^4\right) b \\
\Longrightarrow & (b a)^4=a^4 b^4, \text { by cancellation law. }
\end{aligned}
$$
Now by combining two cases we have
$$
\begin{aligned}
& (b a)^4=a^4 b^4 \\
\Longrightarrow & \left((b a)^2\right)^2=a^2\left(a^2 b^2\right) b^2 \\
\Longrightarrow & \left(a^2 b^2\right)^2=a^2\left(a^2 b^2\right) b^2 \\
\Longrightarrow & \left(a^2 b^2\right)\left(a^2 b^2\right)=a^2\left(a^2 b^2\right) b^2 \\
\Longrightarrow & a^2\left(b^2 a^2\right) b^2=a^2\left(a^2 b^2\right) b^2 \\
\Longrightarrow & b^2 a^2=a^2 b^2, \text { by cancellation law. } \\
\Longrightarrow & b^2 a^2=(b a)^2, \text { since }(b a)^2=a^2 b^2 \\
\Longrightarrow & b(b a) a=(b a)(b a) \\
\Longrightarrow & b(b a) a=b(a b) a \\
\Longrightarrow & b a=a b, \text { by cancellation law. }
\end{aligned}
$$
It follows that, $a b=b a$ for all $a, b \in G$. Hence $G$ is abelian
-/

theorem Herstein_exercise_2_2_5 {G : Type*} [Group G]
  (h : ∀ (a b : G), (a * b) ^ 3 = a ^ 3 * b ^ 3 ∧ (a * b) ^ 5 = a ^ 5 * b ^ 5) :
  ∀ a b : G, a*b = b*a := by
  intro a b
  -- Step 1: Extract the cubic and quintic identities supplied by the hypothesis.
  -- Step 1.1: Record the cubic identity in the original order (a, b) for downstream cancellations.
  have ha3 : (a * b) ^ 3 = a ^ 3 * b ^ 3 := (h a b).1
  -- Step 1.2: Record the cubic identity with swapped arguments to control the complementary squared term.
  have hb3 : (b * a) ^ 3 = b ^ 3 * a ^ 3 := (h b a).1
  -- Step 1.3: Record the fifth-power identity in the order (a, b) to promote the square relation to a fourth power.
  have ha5 : (a * b) ^ 5 = a ^ 5 * b ^ 5 := (h a b).2
  -- Step 2: Cancel a single leading and trailing factor in the cubic identities to obtain square relations.
  -- Step 2.1: Peel off the outer a and b from ha3, leaving a relation for (b * a)².
  have ba_sq : (b * a) ^ 2 = a ^ 2 * b ^ 2 := by
    -- Step 2.1.1: Multiply ha3 on the left by a⁻¹ and on the right by b⁻¹ to remove the exterior factors.
    have aux := congrArg (fun x => a⁻¹ * x * b⁻¹) ha3
    -- Step 2.1.2: Simplify the resulting product to expose the clean square equality.
    simpa [pow_succ, pow_two, mul_assoc] using aux
  -- Step 2.2: Perform the analogous cancellation on hb3 to describe (a * b)².
  have ab_sq : (a * b) ^ 2 = b ^ 2 * a ^ 2 := by
    -- Step 2.2.1: Multiply hb3 on the left by b⁻¹ and on the right by a⁻¹ to strip away the exterior factors.
    have aux := congrArg (fun x => b⁻¹ * x * a⁻¹) hb3
    -- Step 2.2.2: Clean up the resulting word to obtain the alternate square identity.
    simpa [pow_succ, pow_two, mul_assoc] using aux
  -- Step 3: Upgrade the squared relation by one power to compare iterated products of a² and b².
  -- Step 3.1: Reduce ha5 to an identity concerning (b * a)⁴.
  have ba_four : (b * a) ^ 4 = a ^ 4 * b ^ 4 := by
    -- Step 3.1.1: Multiply ha5 on the left by a⁻¹ and on the right by b⁻¹ to shave off a single copy of each factor.
    have aux := congrArg (fun x => a⁻¹ * x * b⁻¹) ha5
    -- Step 3.1.2: Simplify the expression to reach the desired fourth-power equality.
    simpa [pow_succ, pow_two, mul_assoc] using aux
  -- Step 4: Convert the fourth-power identity into a statement saying that the squares of a and b commute.
  -- Step 4.1: Substitute the square identity into the fourth-power equality so that only a² and b² remain.
  have key : (a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2) = a ^ 4 * b ^ 4 := by
    -- Step 4.1.1: Rewrite each occurrence of (b * a)² via ba_sq, and then fold the product back into a fourth power.
    calc
      (a ^ 2 * b ^ 2) * (a ^ 2 * b ^ 2)
          = (b * a) ^ 2 * (b * a) ^ 2 := by simp [ba_sq, mul_assoc]
      _ = (b * a) ^ 4 := by rw [← pow_add]
      _ = a ^ 4 * b ^ 4 := ba_four
  -- Step 4.2: Cancel the remaining exterior squares to deduce that a² and b² commute outright.
  have sq_comm : a ^ 2 * b ^ 2 = b ^ 2 * a ^ 2 := by
    -- Step 4.2.1: Multiply key on the left by (a²)⁻¹ to eliminate the leading a².
    have aux₂ := congrArg (fun x => (a ^ 2)⁻¹ * x) key
    -- Step 4.2.2: Multiply on the right by (b²)⁻¹.
    have aux₃ := congrArg (fun x => x * (b ^ 2)⁻¹) (by simpa [mul_assoc] using aux₂)
    -- Step 4.2.3: Simplify both sides explicitly to isolate b² a² and a² b².
    have rhs_simple :
        (a ^ 2)⁻¹ * (a ^ 4 * (b ^ 4 * (b ^ 2)⁻¹)) = a ^ 2 * b ^ 2 := by
      group
    have aux₄ : b ^ 2 * a ^ 2 = a ^ 2 * b ^ 2 := by
      simpa [rhs_simple, mul_assoc] using aux₃
    exact aux₄.symm
  -- Step 5: Express a · b using the squared relation and then swap the squares with sq_comm.
  -- Step 5.1: Rewrite (b * a)² = a² b² into an explicit formula for a · b.
  have ab_via_squares : a * b = b⁻¹ * (a ^ 2 * b ^ 2 * a⁻¹) := by
    -- Step 5.1.1: Remove the trailing a by multiplying (b * a)² = a² b² on the right with a⁻¹.
    have aux := congrArg (fun x => x * a⁻¹) ba_sq
    -- Step 5.1.2: Simplify to identify the left-hand side as (b * a) * b.
    have aux₁ : (b * a) * b = a ^ 2 * b ^ 2 * a⁻¹ := by
      simpa [pow_two, mul_assoc] using aux
    -- Step 5.1.3: Remove the leading b by multiplying on the left with b⁻¹ and clean up the expression.
    have aux₂ := congrArg (fun x => b⁻¹ * x) aux₁
    simpa [mul_assoc] using aux₂
  -- Step 5.2: Use the commutation of a² and b² to collapse the expression from Step 5.1 to b · a.
  have final_comm : a * b = b * a := by
    -- Step 5.2.1: Substitute the commuted square into the expression and simplify twice.
    calc
      a * b = b⁻¹ * (a ^ 2 * b ^ 2 * a⁻¹) := ab_via_squares
      _ = b⁻¹ * (b ^ 2 * a ^ 2 * a⁻¹) := by
        -- Step 5.2.1.1: Swap a² b² using sq_comm so that b-factors gather together.
        simp [mul_assoc, sq_comm]
      _ = b * a := by
        -- Step 5.2.1.2: Cancel the inverse pairs explicitly to land on b · a.
        simp [mul_assoc, pow_two]
  -- Step 6: Output the required commutativity statement, matching the goal’s orientation.
  exact final_comm
