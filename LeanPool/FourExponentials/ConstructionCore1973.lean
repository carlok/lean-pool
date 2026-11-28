/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.AuxiliaryFunctionAlg
public import LeanPool.FourExponentials.Extrapolation
public import LeanPool.FourExponentials.NormToPolynomialAlg
public import LeanPool.FourExponentials.TrdegOnePresentation

/-!
# The core of the construction

Let $x_1,x_2$ be linearly independent over $\mathbb{Q}$, and likewise $y_1,y_2$. Suppose every
$e^{x_iy_j}$ is algebraic and $\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}[x_1,x_2,y_1,y_2] \le1$.
Then there are a transcendental $\omega\in\mathbb{C}$ and $k>0$ such that for every $C$ and every
large $N$ there are coefficients $c(i,j,h)$, not all zero, with the following property: whenever
$a<R_1$, $b<R_2$, $s<S'$ and $F^{(s)}(ay_1+by_2)\neq0$, some $P\in\mathbb{Z}[X]$ is small at
$\omega$ for $(N,C)$ with respect to the growth functions of constant $k$.

Source: [Wal73, § III, (4) and Lemmes 4, 5, 7].

## References

* [Wal73] M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory 5 (1973),
  191–202.

From `Diaz/Mirror/construction_core_1973.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.construction_core_1973`.
-/

@[expose] public section

namespace FourExponentials

/-- **The core of the construction.** Let $x_1,x_2$ be linearly independent over $\mathbb{Q}$, and
likewise $y_1,y_2$. Suppose every $e^{x_iy_j}$ is algebraic and
$\operatorname{trdeg}_{\mathbb{Q}}\mathbb{Q}[x_1,x_2,y_1,y_2] \le1$. Then there are a transcendental
$\omega\in\mathbb{C}$ and $k>0$ such that for every $C$ and every large $N$ there are coefficients
$c(i,j,h)$, not all zero, with the following property: whenever $a<R_1$, $b<R_2$, $s<S'$ and
$F^{(s)}(ay_1+by_2)\neq0$, some $P\in\mathbb{Z}[X]$ is small at $\omega$ for $(N,C)$ with respect to
the growth functions of constant $k$. -/
theorem construction_core_1973
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ)) ≤ 1) :
    ∃ ω : ℂ, Transcendental ℚ ω ∧ ∃ k : ℝ, 0 < k ∧
      ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
        ∃ c : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → ℂ,
            (∃ i j k', c i j k' ≠ 0) ∧
          ∀ a b s : ℕ, a < (14 * ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊) → b < (14 * ⌊(N : ℝ) *
              Real.sqrt (Real.log (N : ℝ))⌋₊) → s < (⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ /
                  2) →
            iteratedDeriv s (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊,
                ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              c i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) * x₁ + ((k' : ℕ) : ℂ) * x₂) * z))
              ((a : ℂ) * y₁ + (b : ℂ) * y₂) ≠ 0 →
            ∃ P : Polynomial ℤ, P ≠ 0 ∧
              (∀ i : ℕ, |(P.coeff i : ℝ)| ≤ Real.exp (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 *
                  Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ))))) ∧
              (P.natDegree : ℝ) ≤ k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 /
                  Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))) ∧
              ‖Polynomial.aeval ω P‖ < Real.exp (-(C * (k * (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 *
                  Real.sqrt (Real.log 3) else (N : ℝ) ^ 2 * Real.sqrt (Real.log (N : ℝ)))) * (k *
                      (if (N : ℝ) ≤ 3 then (N : ℝ) - 3 + 9 / Real.sqrt (Real.log 3) else (N : ℝ) ^ 2
                          / Real.sqrt (Real.log (N : ℝ)))))) := by
  obtain ⟨ω, ω₁, hω, Q, hQm, hQd, hQroot, hQmin, D, E, G, H, hD, hE, hG, hH⟩ :=
    trdeg_one_presentation x₁ x₂ y₁ y₂ hx hy hexp htr
  obtain ⟨κ, hκ, N₃, h3⟩ := auxiliary_function_alg x₁ x₂ y₁ y₂ hexp ω ω₁ hω Q hQm hQd hQroot hQmin
    D E G H hD hE hG hH
  obtain ⟨κ', hκ', N₄, h4⟩ := extrapolation x₁ x₂ y₁ y₂ hy κ hκ
  obtain ⟨k, hk, h5⟩ := norm_to_polynomial_alg x₁ x₂ y₁ y₂ hexp ω ω₁ hω Q hQm hQd hQroot hQmin
    D E G H hD hE hG hH κ κ' hκ hκ'
  refine ⟨ω, hω, k, hk, fun C => ?_⟩
  obtain ⟨N₅, h5C⟩ := h5 C
  refine ⟨max N₃ (max N₄ N₅), fun N hN => ?_⟩
  obtain ⟨M, hM, q, hq, hc0, hcb, hvan⟩ := h3 N (lt_of_le_of_lt (le_max_left _ _) hN)
  refine ⟨_, hc0, fun a b s ha hb hs hne => ?_⟩
  exact h5C N (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hN) M hM q hq
    a b s ha hb hs hne
    (h4 N (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hN) _ hcb hvan s hs a b ha
        hb)

end FourExponentials
