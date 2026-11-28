/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import TauCeti.Analysis.Complex.Schwarz

/-!
# Cauchy's estimate with zeros

Let $F$ be an entire function, $c\in\mathbb{C}$, $\rho\ge0$ and $R>\rho+1$. Let $S$ be a finite set
of points $z$ with $|z-c|\le\rho$, and put $\sigma=\sum_{z\in S}\operatorname{ord}_zF$. If
$|F(z)|\le M$ whenever $|z-c|=R$, then for every $s\in\mathbb{N}$
$$ |F^{(s)}(c)|\le s!\,\frac{R}{R-1}\Bigl(\frac{\rho+1}{R-\rho}\Bigr)^{\sigma}M. $$

Source: [Wal71, §4, (4.3)].

## References

* [Wal71] M. Waldschmidt, *Indépendance algébrique des valeurs de la fonction exponentielle*, Bull.
  Soc. Math. France 99 (1971), 285–304.

The proof divides out the zeros and applies the maximum modulus principle through Tau
Ceti's Schwarz lemma with prescribed zeros, `TauCeti.norm_le_mul_prod_div_pow`.

From `Diaz/Mirror/cauchy_estimate_with_zeros.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.cauchy_estimate_with_zeros`.
-/

@[expose] public section

namespace FourExponentials

open Finset Metric

/-- **Cauchy's estimate with zeros.** Let $F$ be an entire function, $c\in\mathbb{C}$, $\rho\ge0$
and $R>\rho+1$. Let $S$ be a finite set of points $z$ with $|z-c|\le\rho$, and put
$\sigma=\sum_{z\in S}\operatorname{ord}_zF$. If $|F(z)|\le M$ whenever $|z-c|=R$, then for every
$s\in\mathbb{N}$
$$ |F^{(s)}(c)|\le s!\,\frac{R}{R-1}\Bigl(\frac{\rho+1}{R-\rho}\Bigr)^{\sigma}M. $$ -/
theorem cauchy_estimate_with_zeros
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ) (ρ R M : ℝ) (hρ : 0 ≤ ρ) (hR : ρ + 1 < R)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - c‖ ≤ ρ)
    (hM : ∀ z : ℂ, ‖z - c‖ = R → ‖F z‖ ≤ M) (s : ℕ) :
    ‖iteratedDeriv s F c‖
      ≤ (s.factorial : ℝ) * (R / (R - 1)) *
          ((ρ + 1) / (R - ρ)) ^ (∑ z ∈ S, analyticOrderNatAt F z) * M := by
  set N := ∑ z ∈ S, analyticOrderNatAt F z with hN
  have hR0 : 0 < R := by linarith
  have hRρ : 0 < R - ρ := by linarith
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (c + R) (by simp [abs_of_pos hR0]))
  -- Schwarz's lemma with the zeros of `F` in `S`, read on the unit circle around `c`: every
  -- factor `‖z - a‖ / (R - ‖a - c‖)` is at most `(ρ + 1) / (R - ρ)`.
  have hFsmall : ∀ z ∈ sphere c 1, ‖F z‖ ≤ ((ρ + 1) / (R - ρ)) ^ N * M := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    have hSchwarz := TauCeti.norm_le_mul_prod_div_pow (c := c) (T := R) (M := M) (s := S)
      (k := analyticOrderNatAt F)
      (fun w _ => hF.analyticAt w)
      (fun a _ => by
        unfold analyticOrderNatAt
        generalize analyticOrderAt F a = x
        induction x using ENat.recTopCoe <;> simp)
      (fun a ha => by
        rw [Finset.mem_coe] at ha
        rw [mem_ball_iff_norm]
        linarith [hS a ha])
      (fun w hw => hM w (by rwa [mem_sphere_iff_norm] at hw))
      (z := z) (by rw [mem_closedBall_iff_norm, hz]; linarith)
    refine hSchwarz.trans ?_
    rw [hN, ← prod_pow_eq_pow_sum, mul_comm M]
    refine mul_le_mul_of_nonneg_right (prod_le_prod₀ (fun a ha => ?_) fun a ha => ?_) hM0
    · exact pow_nonneg (div_nonneg (norm_nonneg _) (by linarith [hS a ha])) _
    · have h1 := norm_sub_le (z - c) (a - c)
      rw [show z - c - (a - c) = z - a by ring] at h1
      exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (by linarith [hS a ha]))
        (div_le_div₀ (by linarith) (by linarith [hS a ha]) hRρ (by linarith [hS a ha])) _
  -- Cauchy's estimate on the unit circle; the factor `R / (R - 1) ≥ 1` is slack.
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le s one_pos
    hF.diffContOnCl hFsmall
  simp only [one_pow, div_one] at hC
  have hRR : 1 ≤ R / (R - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have hK : 0 ≤ ((ρ + 1) / (R - ρ)) ^ N * M :=
    mul_nonneg (pow_nonneg (div_nonneg (by linarith) hRρ.le) _) hM0
  have hf : (0 : ℝ) ≤ s.factorial := by positivity
  calc ‖iteratedDeriv s F c‖ ≤ s.factorial * (((ρ + 1) / (R - ρ)) ^ N * M) := hC
    _ = s.factorial * 1 * (((ρ + 1) / (R - ρ)) ^ N * M) := by ring
    _ ≤ s.factorial * (R / (R - 1)) * (((ρ + 1) / (R - ρ)) ^ N * M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRR hf) hK
    _ = s.factorial * (R / (R - 1)) * ((ρ + 1) / (R - ρ)) ^ N * M := by ring

end FourExponentials
