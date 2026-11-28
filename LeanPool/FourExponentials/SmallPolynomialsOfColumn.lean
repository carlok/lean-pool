/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.AuxiliaryConstructionColumn
public import LeanPool.FourExponentials.NonvanishingDerivative
public import Mathlib.Tactic.Choose

/-!
# Small integer polynomials at `ω`, in the column case

As in `small_polynomials_of_counterexample`: `auxiliary_construction_column`
supplies, for each large `N`, an exponential polynomial whose zero count is exceeded on a grid of
points `a y₁ + b y₂`, and turns any non-zero derivative there into a small integer polynomial.
`nonvanishing_derivative` supplies that non-zero derivative, since `x` and `y` are
`ℚ`-linearly independent. A choice for each `N` gives the sequence `P_N`.

From `Diaz/Mirror/small_polynomials_of_column.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.small_polynomials_of_column`.
-/

@[expose] public section

namespace FourExponentials

open Filter Topology

/-- **One algebraic column gives small polynomials.** Let $x_1,x_2,y_1,y_2$ satisfy the column
hypotheses. Then there are a transcendental $\omega\in\mathbb{C}$, functions $\sigma_1,\sigma_2$ and
constants $a_1,a_2\ge1$ satisfying the hypotheses of Theorem , such that for every $C\in\mathbb{R}$
there is $N_0$ and for every $N>N_0$ a polynomial $P_N\in\mathbb{Z}[X]$ that is small at $\omega$
for $(N,C)$ with respect to $\sigma_1,\sigma_2$. -/
theorem small_polynomials_of_column :
    ∀ x₁ x₂ y₁ y₂ : ℂ, LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
      IsAlgebraic ℚ (Complex.exp (x₁ * y₂)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂)) →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
          Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1 →
      ∃ ω : ℂ, Transcendental ℚ ω ∧
        ∃ σ₁ σ₂ : ℝ → ℝ, StrictMono σ₁ ∧ StrictMono σ₂ ∧
          Tendsto σ₁ atTop atTop ∧ Tendsto σ₂ atTop atTop ∧
          ∃ a₁ a₂ : ℝ, 1 ≤ a₁ ∧ 1 ≤ a₂ ∧
            (∀ x : ℝ, 0 < x → σ₂ x ≤ σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₁ (x + 1) ≤ a₁ * σ₁ x) ∧
            (∀ x : ℝ, 0 < x → σ₂ (x + 1) ≤ a₂ * σ₂ x) ∧
            ∀ C : ℝ, ∃ N₀ : ℕ, ∃ P : ℕ → Polynomial ℤ, ∀ N : ℕ, N₀ < N →
              P N ≠ 0 ∧
              (∀ i : ℕ, |((P N).coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
              ((P N).natDegree : ℝ) ≤ σ₂ N ∧
              ‖Polynomial.aeval ω (P N)‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
  intro x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂ htr
  obtain ⟨ω, hω, σ₁, σ₂, hm₁, hm₂, ht₁, ht₂, a₁, a₂, ha₁, ha₂, h₂₁, hg₁, hg₂, hC⟩ :=
    auxiliary_construction_column x₁ x₂ y₁ y₂ hx hy h₁₂ h₂₂ htr
  refine ⟨ω, hω, σ₁, σ₂, hm₁, hm₂, ht₁, ht₂, a₁, a₂, ha₁, ha₂, h₂₁, hg₁, hg₂, fun C => ?_⟩
  obtain ⟨N₀, hN⟩ := hC C
  -- for each large `N`, a small polynomial
  have key : ∀ N : ℕ, N₀ < N → ∃ P : Polynomial ℤ, P ≠ 0 ∧
      (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (σ₁ N)) ∧
      (P.natDegree : ℝ) ≤ σ₂ N ∧
      ‖Polynomial.aeval ω P‖ < Real.exp (-(C * σ₁ N * σ₂ N)) := by
    intro N hN'
    obtain ⟨S, T, R₁, R₂, S', c, hc, ⟨lam, hlam, hcount⟩, himp⟩ := hN N hN'
    obtain ⟨a, b, s, ha, hb, hs, hne⟩ :=
      nonvanishing_derivative x₁ x₂ y₁ y₂ hx hy S T R₁ R₂ S' c hc lam hlam hcount
    exact himp a b s ha hb hs hne
  -- one choice for each `N`
  classical
  refine ⟨N₀, fun N => if h : N₀ < N then Classical.choose (key N h) else 0, fun N hN' => ?_⟩
  simp only [dite_eq_left hN']
  exact Classical.choose_spec (key N hN')

end FourExponentials
