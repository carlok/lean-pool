/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.ExpPolyIteratedDerivLe
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set

/-!
# The value of an exponential polynomial from its first derivatives at `0`

Write `N = ∑ⱼ qⱼ` and `f(z) = ∑ⱼ Pⱼ(z) e^{wⱼ z}`. If `N = 0`, every `Pⱼ` is zero and so is `f`.
Otherwise `0 ≤ D` (from `s = 0`), and `Transcendence.expPoly_iteratedDeriv_le` at `c = 0` gives
`‖f⁽ⁿ⁾(0)‖ ≤ D (W + 1)^{n + N}` for every `n`. The Taylor series of the entire function `f` at `0`
then gives `‖f(u)‖ ≤ ∑ₙ Rⁿ/n! · D (W + 1)^{n + N} ≤ D (W + 1)^N e^{(W + 1) R}`, which is at most
`N (W + 1)^{N + 1} e^{R (W + 1)} D`. The injectivity of `w` is not needed.

From `Diaz/Mirror/expPoly_value_le_derivs.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.expPoly_value_le_derivs`.
-/

@[expose] public section

namespace FourExponentials

open Finset in
/-- **Values from low-order derivatives.** Let $w_1,\dots,w_l\in\mathbb{C}$ be pairwise distinct
with $|w_j|\le W$ for some $W\ge0$. For each $j$ let $P_j\in\mathbb{C}[z]$ be zero or of degree less
than $q_j$, and put $g(z)=\sum_jP_j(z)e^{w_jz}$ and $n=\sum_jq_j$. Let $R\ge0$. If $|g^{(s)}(0)|\le
D$ for every $s<n$, then
$$ |g(u)|\le n\,(W+1)^{n+1}e^{R(W+1)}D\qquad\text{whenever }|u|\le R. $$ -/
theorem expPoly_value_le_derivs
    {l : ℕ} (q : Fin l → ℕ) (w : Fin l → ℂ) (hw : Function.Injective w)
    (P : Fin l → Polynomial ℂ) (hP : ∀ j, P j = 0 ∨ (P j).natDegree < q j)
    (W R D : ℝ) (hW0 : 0 ≤ W) (hW : ∀ j, ‖w j‖ ≤ W) (hR : 0 ≤ R)
    (hD : ∀ s : ℕ, s < ∑ j, q j →
      ‖iteratedDeriv s (fun z : ℂ => ∑ j, (P j).eval z * Complex.exp (w j * z)) 0‖ ≤ D)
    (u : ℂ) (hu : ‖u‖ ≤ R) :
    ‖∑ j, (P j).eval u * Complex.exp (w j * u)‖
      ≤ ((∑ j, q j : ℕ) : ℝ) * (W + 1) ^ ((∑ j, q j) + 1) * Real.exp (R * (W + 1)) * D := by
  have _ := hw  -- the injectivity of `w` is not needed
  set N := ∑ j, q j with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hs0 : ∑ j, q j = 0 := hN0
    have hP0 : ∀ j, P j = 0 := fun j => (hP j).resolve_right (by
      rw [Finset.sum_eq_zero_iff.1 hs0 j (Finset.mem_univ j)]; exact Nat.not_lt_zero _)
    simp [hP0, hN0]
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 hNpos)
  have hbd := Transcendence.expPoly_iteratedDeriv_le w W hW0 hW 0 N q P hP hN.symm D hD0 hD
  -- Taylor at `0`: `‖f(u)‖ ≤ ∑ₙ ‖u‖ⁿ/n! · D (W + 1)^(n + N) ≤ D (W + 1)^N e^{(W + 1) R}`
  have hT := Complex.hasSum_taylorSeries_of_entire (c := 0) (z := u)
    (show Differentiable ℂ (fun z : ℂ => ∑ j, (P j).eval z * Complex.exp (w j * z)) by fun_prop)
  have hle : ‖∑ j, (P j).eval u * Complex.exp (w j * u)‖
      ≤ D * (W + 1) ^ N * Real.exp ((W + 1) * R) := by
    refine le_of_tendsto' hT.tendsto_sum_nat.norm fun K => (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ n ∈ range K, D * (W + 1) ^ N * (((W + 1) * R) ^ n / (n.factorial : ℝ)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [sub_zero, norm_smul, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
          calc _ ≤ (n.factorial : ℝ)⁻¹ * (R ^ n * (D * (W + 1) ^ (n + N))) := by
                gcongr; exact hbd n
            _ = _ := by rw [mul_pow, pow_add]; ring
      _ = D * (W + 1) ^ N * ∑ n ∈ range K, ((W + 1) * R) ^ n / (n.factorial : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by gcongr; exact Real.sum_le_exp_of_nonneg (by positivity) K
  calc _ ≤ D * (W + 1) ^ N * Real.exp ((W + 1) * R) := hle
    _ ≤ D * ((N : ℝ) * (W + 1) ^ (N + 1)) * Real.exp (R * (W + 1)) := by
        rw [mul_comm (W + 1) R]
        gcongr
        calc (W + 1) ^ N ≤ (W + 1) ^ (N + 1) := pow_le_pow_right₀ (by linarith) (by omega)
          _ ≤ _ := le_mul_of_one_le_left (by positivity) (by exact_mod_cast hNpos)
    _ = _ := by ring

end FourExponentials
