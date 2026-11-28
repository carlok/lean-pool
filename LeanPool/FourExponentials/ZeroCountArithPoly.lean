/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set

/-!
# Few zeros beat the bound

For every integer $n\ge1$, real $x\ge0$ and $\lambda>0$, and every integer $0\le\sigma\le n-1$,
$$ \sigma<\frac{n}{\lambda}+2\,\frac{1+n^{\lambda}}{\lambda\log n}\,(1+x), $$
where for $n=1$ the second term is read as $0$.

Source: Elementary.

From `Diaz/Mirror/zero_count_arith_poly.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.zero_count_arith_poly`.
-/

@[expose] public section

namespace FourExponentials

/-- **Few zeros beat the bound.** For every integer $n\ge1$, real $x\ge0$ and $\lambda>0$, and every
integer $0\le\sigma\le n-1$,
$$ \sigma<\frac{n}{\lambda}+2\,\frac{1+n^{\lambda}}{\lambda\log n}\,(1+x), $$
where for $n=1$ the second term is read as $0$. -/
theorem zero_count_arith_poly
    (n : ℕ) (x lam : ℝ) (hx : 0 ≤ x) (hlam : 0 < lam) (σ : ℕ) (h : σ + 1 ≤ n) :
    (σ : ℝ) < (n : ℝ) / lam + 2 * (1 + (n : ℝ) ^ lam) / (lam * Real.log (n : ℝ)) * (1 + x) := by
  have hn1 : 1 ≤ n := by omega
  have hσn : (σ : ℝ) + 1 ≤ n := by exact_mod_cast h
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hsecond : 0 ≤ 2 * (1 + (n : ℝ) ^ lam) / (lam * Real.log (n : ℝ)) * (1 + x) := by
    have : 0 ≤ (n : ℝ) ^ lam := Real.rpow_nonneg hnpos.le _
    positivity
  by_cases hl : lam ≤ 1
  · have h1 : (n : ℝ) ≤ (n : ℝ) / lam := by
      rw [le_div_iff₀ hlam]
      nlinarith
    linarith
  · push Not at hl
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn : n = 1 := by omega
      have hσ : σ = 0 := by omega
      subst hn; subst hσ
      simp only [Nat.cast_one, Nat.cast_zero, Real.log_one, mul_zero, div_zero, zero_mul, add_zero]
      positivity
    · set L := Real.log (n : ℝ) with hL
      have hLpos : 0 < L := Real.log_pos (by exact_mod_cast hn2)
      set t := lam * L with ht
      have htpos : 0 < t := by positivity
      have htL : L < t := by rw [ht]; nlinarith
      have hrpow : (n : ℝ) ^ lam = Real.exp t := by
        rw [Real.rpow_def_of_pos hnpos, ht, hL, mul_comm]
      have hexp : (n : ℝ) * (1 + (t - L)) ≤ Real.exp t := by
        have h1 := Real.add_one_le_exp (t - L)
        have h2 : Real.exp t = (n : ℝ) * Real.exp (t - L) := by
          rw [Real.exp_sub, hL, Real.exp_log hnpos]; field_simp
        rw [h2]
        nlinarith
      have hlamL : lam * L = t := rfl
      have e1 : (n : ℝ) / lam = (n : ℝ) * L / t := by
        rw [ht]; field_simp
      have hA : 2 * ((n : ℝ) * (1 + (t - L))) / t ≤ 2 * (1 + Real.exp t) / t := by
        apply div_le_div_of_nonneg_right _ htpos.le
        linarith
      have hB : 2 * (1 + Real.exp t) / t ≤ 2 * (1 + Real.exp t) / t * (1 + x) := by
        have : 0 ≤ 2 * (1 + Real.exp t) / t := by positivity
        nlinarith
      have hkey : (n : ℝ) - 1 < (n : ℝ) * L / t + 2 * ((n : ℝ) * (1 + (t - L))) / t := by
        rw [← add_div, lt_div_iff₀ htpos]
        nlinarith
      rw [e1, hrpow]
      linarith

end FourExponentials
