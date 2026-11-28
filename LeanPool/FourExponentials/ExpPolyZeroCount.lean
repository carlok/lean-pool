/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.ExpPolyZeroCountScaled
public import LeanPool.FourExponentials.ZeroCountArith
public import LeanPool.FourExponentials.ZeroCountArithPoly
public import LeanPool.FourExponentials.ZeroCountDegenerate
public import Mathlib.Tactic.Push

/-!
# Zeros of an exponential polynomial in a disc

Let $\omega_1,\dots,\omega_l\in\mathbb{C}$ be pairwise distinct, let $q_1,\dots,q_l\in\mathbb{N}$,
and let $b_{j,i}\in\mathbb{C}$ ($1\le j\le l$, $0\le i<q_j$) be not all zero. Put
$$ f(z) =\sum_{j =1}^{l}\sum_{i =0}^{q_j-1}b_{j,i}\,z^{i}e^{\omega_jz}, \qquad
n=\sum_jq_j,\qquad\Omega=\max_j|\omega_j|. $$
Let $z_0\in\mathbb{C}$, $\rho\ge0$ and $\lambda>0$. Then for every finite set $S$ of points of the
disc $|z-z_0|\le\rho$
$$ \sum_{z\in S}\operatorname{ord}_zf<\frac{n}{\lambda}+2\,\frac{1+n^{\lambda}}{\lambda\log
n}\,(1+\rho\Omega), $$
where for $n=1$ the second term is read as $0$. No separation between the $\omega_j$ is assumed.

Source: [Wal71, §4, Lemme 3, (4.2)]; compare [Tij71].

## References

* [Tij71] R. Tijdeman, Proc. Kon. Nederl. Akad. Wetensch. Ser. A 74 (= Indag. Math. 33) (1971), 1–7.
* [Wal71] M. Waldschmidt, *Indépendance algébrique des valeurs de la fonction exponentielle*, Bull.
  Soc. Math. France 99 (1971), 285–304.

From `Diaz/Mirror/expPoly_zero_count.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.expPoly_zero_count`.
-/

@[expose] public section

namespace FourExponentials

open Finset

/-- **Zeros of an exponential polynomial in a disc.** Let $\omega_1,\dots,\omega_l\in\mathbb{C}$ be
pairwise distinct, let $q_1,\dots,q_l\in\mathbb{N}$, and let $b_{j,i}\in\mathbb{C}$ ($1\le j\le l$,
$0\le i<q_j$) be not all zero. Put
$$ f(z) =\sum_{j =1}^{l}\sum_{i =0}^{q_j-1}b_{j,i}\,z^{i}e^{\omega_jz}, \qquad
n=\sum_jq_j,\qquad\Omega=\max_j|\omega_j|. $$
Let $z_0\in\mathbb{C}$, $\rho\ge0$ and $\lambda>0$. Then for every finite set $S$ of points of the
disc $|z-z_0|\le\rho$
$$ \sum_{z\in S}\operatorname{ord}_zf<\frac{n}{\lambda}+2\,\frac{1+n^{\lambda}}{\lambda\log
n}\,(1+\rho\Omega), $$
where for $n=1$ the second term is read as $0$. No separation between the $\omega_j$ is assumed. -/
theorem expPoly_zero_count
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0)
    (z₀ : ℂ) (ρ : ℝ) (hρ : 0 ≤ ρ) (lam : ℝ) (hlam : 0 < lam)
    (S : Finset ℂ) (hS : ∀ z ∈ S, ‖z - z₀‖ ≤ ρ) :
    (∑ z ∈ S, (analyticOrderNatAt
        (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
      < ((∑ j, q j : ℕ) : ℝ) / lam
        + 2 * (1 + ((∑ j, q j : ℕ) : ℝ) ^ lam) / (lam * Real.log ((∑ j, q j : ℕ) : ℝ))
          * (1 + ρ * ⨆ j, ‖ω j‖) := by
  classical
  have hΩ0 : 0 ≤ ⨆ j, ‖ω j‖ := Real.iSup_nonneg (fun j => norm_nonneg _)
  have hx : 0 ≤ ρ * ⨆ j, ‖ω j‖ := mul_nonneg hρ hΩ0
  have hcast : (∑ z ∈ S, (analyticOrderNatAt
      (fun w : ℂ => ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℝ))
      = ((∑ z ∈ S, analyticOrderNatAt
      (fun w : ℂ => ∑ j, ∑ i : Fin (q j),
          b j i * w ^ (i : ℕ) * Complex.exp (ω j * w)) z : ℕ) : ℝ) := by
    push_cast; rfl
  by_cases hdeg : (∑ j, q j) ≤ 1 ∨ (⨆ j, ‖ω j‖) = 0
  · have h1 := zero_count_degenerate q ω hω b hb S hdeg
    rw [hcast]
    exact zero_count_arith_poly (∑ j, q j) (ρ * ⨆ j, ‖ω j‖) lam hx hlam _ h1
  · push Not at hdeg
    obtain ⟨hn, hΩ⟩ := hdeg
    have hΩpos : 0 < ⨆ j, ‖ω j‖ := lt_of_le_of_ne hΩ0 (Ne.symm hΩ)
    have h2 := expPoly_zero_count_scaled q ω hω b hb z₀ ρ hρ S hS hΩpos
    exact zero_count_arith (∑ j, q j) (by omega) (ρ * ⨆ j, ‖ω j‖) lam hx hlam _
      (Finset.sum_nonneg (fun z _ => Nat.cast_nonneg _)) h2

end FourExponentials
