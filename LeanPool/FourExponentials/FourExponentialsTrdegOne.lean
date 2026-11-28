/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.SmallPolynomialsOfCounterexample
public import LeanPool.FourExponentials.TranscendenceCriterion

/-!
# Four exponentials in transcendence degree one

Let $l_{11},l_{12},l_{21},l_{22}$ be non-zero logarithms of algebraic numbers with
$$ l_{11}l_{22} =l_{12}l_{21},
\qquad\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(l_{11},l_{12},l_{21},l_{22}) \le1. $$
Then the two rows, or the two columns, of $\begin{pmatrix}l_{11}&l_{12}\\
l_{21}&l_{22}\end{pmatrix}$ are linearly dependent over $\mathbb{Q}$. Equivalently, if $x_1,x_2$ and
$y_1,y_2$ are pairs of complex numbers linearly independent over $\mathbb{Q}$ and the four products
$x_iy_j$ are logarithms of algebraic numbers, then
$\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(x_1,x_2,y_1,y_2)\ge2$.

Source: Waldschmidt [Wal73, Cor. 4] and Brownawell [Bro74, Cor. 7]; stated in this form as [RW95,
Theorem 1].

## References

* [Bro74] W. D. Brownawell, *The algebraic independence of certain numbers related by the
  exponential function*, J. Number Theory 6 (1974), 22–31.
* [RW95] D. Roy and M. Waldschmidt, *Quadratic relations between logarithms of algebraic numbers*,
  Proc. Japan Acad. Ser. A 71 (1995), 151–153.
* [Wal73] M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory 5 (1973),
  191–202.

From `Diaz/Mirror/four_exponentials_trdeg_one.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `DiazModulus.four_exponentials_trdeg_one`.
-/

@[expose] public section

namespace FourExponentials

open Complex ComplexConjugate

-- Proof by contradiction. If neither the rows nor the columns are ℚ-dependent, the analytic
-- construction `small_polynomials_of_counterexample` produces a transcendental `ω` and
-- integer polynomials that are too small at `ω`; the transcendence criterion
-- `transcendence_criterion` then makes `ω` algebraic.
/-- **Four exponentials in transcendence degree one.** Let $l_{11},l_{12},l_{21},l_{22}$ be non-zero
logarithms of algebraic numbers with
$$ l_{11}l_{22} =l_{12}l_{21},
\qquad\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(l_{11},l_{12},l_{21},l_{22}) \le1. $$
Then the two rows, or the two columns, of $\begin{pmatrix}l_{11}&l_{12}\\
l_{21}&l_{22}\end{pmatrix}$ are linearly dependent over $\mathbb{Q}$. Equivalently, if $x_1,x_2$ and
$y_1,y_2$ are pairs of complex numbers linearly independent over $\mathbb{Q}$ and the four products
$x_iy_j$ are logarithms of algebraic numbers, then
$\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}(x_1,x_2,y_1,y_2)\ge2$. -/
theorem four_exponentials_trdeg_one :
    ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
      IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
      IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
      l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
      l₁₁ * l₂₂ = l₁₂ * l₂₁ →
      Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
      (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
      ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
          (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0) := by
  intro l₁₁ l₁₂ l₂₁ l₂₂ e₁₁ e₁₂ e₂₁ e₂₂ n₁₁ n₁₂ n₂₁ n₂₂ hdet htr
  by_contra hcon
  obtain ⟨hrows, hcols⟩ := not_or.mp hcon
  obtain ⟨ω, hω, σ₁, σ₂, hm₁, hm₂, ht₁, ht₂, a₁, a₂, ha₁, ha₂, h₂₁, hg₁, hg₂, hC⟩ :=
    small_polynomials_of_counterexample l₁₁ l₁₂ l₂₁ l₂₂ e₁₁ e₁₂ e₂₁ e₂₂
      n₁₁ n₁₂ n₂₁ n₂₂ hdet htr hrows hcols
  obtain ⟨N₀, P, hP⟩ := hC (max (10 + 1) ((4 + 1) * (a₁ * a₂)))
  exact hω (transcendence_criterion ω 1 one_pos σ₁ σ₂ hm₁ hm₂ ht₁ ht₂ a₁ a₂ ha₁ ha₂
    h₂₁ hg₁ hg₂ N₀ P (fun N hN => (hP N hN).1) (fun N hN => (hP N hN).2.1)
    (fun N hN => (hP N hN).2.2.1) (fun N hN => (hP N hN).2.2.2))

end FourExponentials
