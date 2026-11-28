/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Monotone.Union
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-!
# Growth of the construction's scales

Let `A x = x - 3 + 9 √(log 3)` for `x ≤ 3` and `A x = x² √(log x)` beyond, and let `B` be the
same with `9 / √(log 3)` and `x² / √(log x)`. The statement is about `k A` and `k B`, with
`k > 0`. For `x ≥ 3`, `1 ≤ log x ≤ x - 1` and `1 ≤ √(log x)`.

* **Monotonicity.** Each is a line of slope one on `(-∞, 3]`, glued at `3` to a function strictly
  increasing on `[3, ∞)` that takes the same value there (`StrictMonoOn.Iic_union_Ici`). For
  `x² / √(log x)`, compare squares: `log t / t` is antitone past `e`, so `x log y ≤ y log x` and
  `x⁴ log y < y⁴ log x` for `3 ≤ x < y`.
* **Limits.** Past `3`, both are at least `x`.
* **`B ≤ A`**, since `√(log x) ≥ 1`.
* **One step multiplies by at most `3`.** Up to `x + 1 ≤ 3`, a step adds `1` to a value above `3`.
  Across `3`, `(x + 1)² √(log (x + 1)) ≤ 16 · 1.5` and `(x + 1)² / √(log (x + 1)) ≤ 16 / √(log 3)`.
  Past `3`, for `A` compare squares, with `log (x + 1) ≤ 2 log x` and `x + 1 ≤ 4x/3`; for `B`, use
  `(x + 1)² ≤ 3 x²` and that `√(log x)` increases.

From `Diaz/Mirror/construction_growth.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.construction_growth`.
-/

@[expose] public section

namespace FourExponentials

open Filter Topology

namespace ConstructionGrowth

/-- The growing majorant of the construction. -/
noncomputable def A (x : ℝ) : ℝ :=
  if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x)

/-- Its companion with the reciprocal root. -/
noncomputable def B (x : ℝ) : ℝ :=
  if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x)

/-- For `x ≥ 3`: `1 ≤ log x ≤ x - 1`, and `1 ≤ √(log x)`, whose square is `log x`. -/
lemma log_facts {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x ∧ Real.log x ≤ x - 1 ∧
    1 ≤ Real.sqrt (Real.log x) ∧ Real.sqrt (Real.log x) ^ 2 = Real.log x := by
  have h1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_three]
  exact ⟨h1, Real.log_le_sub_one_of_pos (by linarith), Real.one_le_sqrt.2 h1,
    Real.sq_sqrt (by linarith)⟩

/-- A line of slope one below `a`, glued to a function increasing on `[a, ∞)`. -/
lemma strictMono_glue {f : ℝ → ℝ} {a c : ℝ} (hf : StrictMonoOn f (Set.Ici a)) (hc : c = f a) :
    StrictMono fun x => if x ≤ a then x - a + c else f x := by
  refine StrictMonoOn.Iic_union_Ici (fun x (hx : x ≤ a) y (hy : y ≤ a) hxy => ?_)
    (hf.congr fun x (hx : a ≤ x) => ?_)
  · simp only [ite_eq_left hx, ite_eq_left hy]; linarith
  · rcases hx.eq_or_lt with rfl | h
    · simp [hc]
    · simp [not_le.2 h]

lemma strictMono_A : StrictMono A := by
  refine strictMono_glue (f := fun x => x ^ 2 * Real.sqrt (Real.log x))
    (fun x (hx : 3 ≤ x) y (hy : 3 ≤ y) hxy => ?_) (by norm_num)
  exact mul_lt_mul (by nlinarith) (Real.sqrt_le_sqrt (Real.log_le_log (by linarith) hxy.le))
    (by linarith [(log_facts hx).2.2.1]) (by positivity)

lemma strictMono_B : StrictMono B := by
  refine strictMono_glue (f := fun x => x ^ 2 / Real.sqrt (Real.log x))
    (fun x (hx : 3 ≤ x) y (hy : 3 ≤ y) hxy => ?_) (by norm_num)
  obtain ⟨hlx, -, hsx, hqx⟩ := log_facts hx
  obtain ⟨hly, -, hsy, hqy⟩ := log_facts hy
  -- `log t / t` is antitone past `e`, so `x log y ≤ y log x`
  have he : Real.exp 1 ≤ x := by linarith [Real.exp_one_lt_three]
  have hant := Real.log_div_self_antitoneOn he (he.trans hxy.le) hxy.le
  simp only at hant
  rw [div_le_div_iff₀ (by linarith) (by linarith)] at hant
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  have h3 : x ^ 3 < y ^ 3 := pow_lt_pow_left₀ hxy (by linarith) (by norm_num)
  refine (pow_lt_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, mul_pow, hqx, hqy]
  nlinarith [mul_le_mul_of_nonneg_left hant (by positivity : (0 : ℝ) ≤ x ^ 3),
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right h3 (by linarith : (0 : ℝ) < y))
      (by linarith : (0 : ℝ) < Real.log x)]

lemma tendsto_A : Tendsto A atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
  simp only [A, ite_eq_right (not_le.2 hx), id]
  nlinarith [mul_le_mul_of_nonneg_left (log_facts hx.le).2.2.1 (by positivity : (0 : ℝ) ≤ x ^ 2)]

lemma tendsto_B : Tendsto B atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
  obtain ⟨-, hlx, hsx, hqx⟩ := log_facts hx.le
  simp only [B, ite_eq_right (not_le.2 hx), id]
  rw [le_div_iff₀ (by linarith)]
  have hs : Real.sqrt (Real.log x) ≤ x := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ x)]

lemma B_le_A (x : ℝ) : B x ≤ A x := by
  unfold A B
  split_ifs with hx
  · have h3 := (log_facts le_rfl).2.2.1
    have : 9 / Real.sqrt (Real.log 3) ≤ 9 * Real.sqrt (Real.log 3) := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · obtain ⟨hl, -, hs, hq⟩ := log_facts (not_le.1 hx).le
    rw [div_le_iff₀ (by linarith), mul_assoc, ← sq, hq]
    exact le_mul_of_one_le_right (sq_nonneg x) hl

lemma A_step (x : ℝ) (hx : 0 < x) : A (x + 1) ≤ 3 * A x := by
  have h3 := (log_facts (le_refl (3 : ℝ))).2.2.1
  unfold A
  by_cases h1 : x + 1 ≤ 3
  · rw [ite_eq_left h1, ite_eq_left (by linarith : x ≤ 3)]; linarith
  obtain ⟨-, -, hs1, hq1⟩ := log_facts (not_le.1 h1).le
  by_cases h2 : x ≤ 3
  · -- `3 < x + 1 ≤ 4`, so `(x + 1)² √(log (x + 1)) ≤ 16 · 1.5`
    rw [ite_eq_right h1, ite_eq_left h2]
    have hl : Real.log (x + 1) ≤ 2 * Real.log 2 := by
      have := Real.log_le_log (by linarith) (show x + 1 ≤ 2 ^ 2 by linarith)
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have ht : Real.sqrt (Real.log (x + 1)) ≤ 1.5 := by
      nlinarith [Real.sqrt_nonneg (Real.log (x + 1)), Real.log_two_lt_d9]
    nlinarith [mul_le_mul (by nlinarith : (x + 1) ^ 2 ≤ 16) ht (Real.sqrt_nonneg _) (by norm_num)]
  · -- `x > 3`: compare squares, with `log (x + 1) ≤ 2 log x` and `x + 1 ≤ 4x/3`
    rw [ite_eq_right h1, ite_eq_right h2]
    obtain ⟨hl0, -, hs0, hq0⟩ := log_facts (not_le.1 h2).le
    have hl : Real.log (x + 1) ≤ 2 * Real.log x := by
      have := Real.log_le_log (by linarith) (show x + 1 ≤ x ^ 2 by nlinarith)
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have h4 : (x + 1) ^ 4 ≤ (4 / 3 * x) ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, mul_pow, mul_pow, hq1, hq0]
    nlinarith [mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ ((x + 1) ^ 2) ^ 2),
      mul_le_mul_of_nonneg_right h4 (by linarith : (0 : ℝ) ≤ Real.log x),
      mul_nonneg (pow_nonneg hx.le 4) (by linarith : (0 : ℝ) ≤ Real.log x)]

lemma B_step (x : ℝ) (hx : 0 < x) : B (x + 1) ≤ 3 * B x := by
  obtain ⟨-, hl3, h3, hq3⟩ := log_facts (le_refl (3 : ℝ))
  have hc : 6 ≤ 9 / Real.sqrt (Real.log 3) := by rw [le_div_iff₀ (by linarith)]; nlinarith
  unfold B
  by_cases h1 : x + 1 ≤ 3
  · rw [ite_eq_left h1, ite_eq_left (by linarith : x ≤ 3)]; linarith
  by_cases h2 : x ≤ 3
  · -- `3 < x + 1 ≤ 4`
    rw [ite_eq_right h1, ite_eq_left h2]
    have hle : (x + 1) ^ 2 / Real.sqrt (Real.log (x + 1)) ≤ 16 / Real.sqrt (Real.log 3) :=
      div_le_div₀ (by norm_num) (by nlinarith) (by linarith)
        (Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by linarith)))
    have h16 : 16 / Real.sqrt (Real.log 3) = 16 / 9 * (9 / Real.sqrt (Real.log 3)) := by ring
    linarith
  · rw [ite_eq_right h1, ite_eq_right h2]
    have hs0 : 0 < Real.sqrt (Real.log x) := by linarith [(log_facts (not_le.1 h2).le).2.2.1]
    have hlog : Real.sqrt (Real.log x) ≤ Real.sqrt (Real.log (x + 1)) :=
      Real.sqrt_le_sqrt (Real.log_le_log (by linarith) (by linarith))
    have hsq : (x + 1) ^ 2 ≤ 3 * x ^ 2 := by nlinarith
    calc (x + 1) ^ 2 / Real.sqrt (Real.log (x + 1)) ≤ (x + 1) ^ 2 / Real.sqrt (Real.log x) := by
          gcongr
      _ ≤ 3 * x ^ 2 / Real.sqrt (Real.log x) := by gcongr
      _ = 3 * (x ^ 2 / Real.sqrt (Real.log x)) := by ring

end ConstructionGrowth

open ConstructionGrowth in
/-- **The growth functions.** For every $k>0$ the growth functions $\sigma_1,\sigma_2$ are strictly
increasing and tend to $+\infty$, and for every $x>0$
$$ \sigma_2(x) \le\sigma_1(x), \qquad\sigma_i(x+1) \le3\,\sigma_i(x)\quad(i =1,2). $$ -/
theorem construction_growth (k : ℝ) (hk : 0 < k) :
    StrictMono (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 *
        Real.sqrt (Real.log x))) ∧
    StrictMono (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 /
        Real.sqrt (Real.log x))) ∧
    Tendsto (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 *
        Real.sqrt (Real.log x))) atTop atTop ∧
    Tendsto (fun x : ℝ => k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 /
        Real.sqrt (Real.log x))) atTop atTop ∧
    (∀ x : ℝ, 0 < x → k * (if x ≤ 3 then x - 3 + 9 / Real.sqrt (Real.log 3) else x ^ 2 /
        Real.sqrt (Real.log x)) ≤ k * (if x ≤ 3 then x - 3 + 9 * Real.sqrt (Real.log 3) else x ^ 2 *
            Real.sqrt (Real.log x))) ∧
    (∀ x : ℝ, 0 < x → k * (if (x + 1) ≤ 3 then (x + 1) - 3 + 9 * Real.sqrt (Real.log 3) else (x +
        1) ^ 2 * Real.sqrt (Real.log (x + 1))) ≤ 3 * (k * (if x ≤ 3 then x - 3 + 9 *
            Real.sqrt (Real.log 3) else x ^ 2 * Real.sqrt (Real.log x)))) ∧
    (∀ x : ℝ, 0 < x → k * (if (x + 1) ≤ 3 then (x + 1) - 3 + 9 / Real.sqrt (Real.log 3) else (x +
        1) ^ 2 / Real.sqrt (Real.log (x + 1))) ≤ 3 * (k * (if x ≤ 3 then x - 3 + 9 /
            Real.sqrt (Real.log 3) else x ^ 2 / Real.sqrt (Real.log x)))) := by
  refine ⟨fun x y h => mul_lt_mul_of_pos_left (strictMono_A h) hk,
    fun x y h => mul_lt_mul_of_pos_left (strictMono_B h) hk,
    Filter.Tendsto.const_mul_atTop hk tendsto_A,
    Filter.Tendsto.const_mul_atTop hk tendsto_B,
    fun x _ => mul_le_mul_of_nonneg_left (B_le_A x) hk.le,
    fun x hx => ?_, fun x hx => ?_⟩
  · have h := mul_le_mul_of_nonneg_left (A_step x hx) hk.le
    calc k * A (x + 1) ≤ k * (3 * A x) := h
      _ = 3 * (k * A x) := by ring
  · have h := mul_le_mul_of_nonneg_left (B_step x hx) hk.le
    calc k * B (x + 1) ≤ k * (3 * B x) := h
      _ = 3 * (k * B x) := by ring

end FourExponentials
