/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.AuxLinearSystem
public import LeanPool.FourExponentials.SiegelAux

/-!
# The auxiliary function

Let $x_1,x_2,y_1,y_2\in\mathbb{C}$ have presentation data, and suppose every $e^{x_iy_j}$ is
algebraic. There is $\kappa>0$ such that for every large $N$ there are $M\le\kappa S$ and integers
$q(i,j,h,\mu,\nu)$ ($i<S$, $j,h<2N$, $\mu<M$, $\nu<d$) of absolute value at most $e^{\kappa
N^{2}\sqrt{\log N}}$, such that the coefficients $c_q(i,j,h)$ are not all zero and of absolute value
at most $e^{\kappa N^{2}\sqrt{\log N}}$, and
$$ F_q^{(m)}(ay_1+by_2)=0\qquad\text{for all }a<t_1,\ b<t_2,\ m<S. $$

Source: [Wal73, Lemme 4], with Siegel's lemma.

## References

* [Wal73] M. Waldschmidt, *Solution du huitième problème de Schneider*, J. Number Theory 5 (1973),
  191–202.

From `Diaz/Mirror/auxiliary_function_alg.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `FourExp.auxiliary_function_alg`.
-/

@[expose] public section

namespace FourExponentials

/-- **The auxiliary function.** Let $x_1,x_2,y_1,y_2\in\mathbb{C}$ have presentation data, and
suppose every $e^{x_iy_j}$ is algebraic. There is $\kappa>0$ such that for every large $N$ there are
$M\le\kappa S$ and integers $q(i,j,h,\mu,\nu)$ ($i<S$, $j,h<2N$, $\mu<M$, $\nu<d$) of absolute value
at most $e^{\kappa N^{2}\sqrt{\log N}}$, such that the coefficients $c_q(i,j,h)$ are not all zero
and of absolute value at most $e^{\kappa N^{2}\sqrt{\log N}}$, and
$$ F_q^{(m)}(ay_1+by_2)=0\qquad\text{for all }a<t_1,\ b<t_2,\ m<S. $$ -/
theorem auxiliary_function_alg
    (x₁ x₂ y₁ y₂ : ℂ)
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁,
        y₂] j))) (ω ω₁ : ℂ) (hω : Transcendental ℚ ω) (Q : Polynomial (Polynomial ℤ)) (hQm :
            Q.Monic) (hQd : 0 < Q.natDegree)
    (hQroot : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0)
    (hQmin : ∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree →
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0)
    (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 →
        Polynomial (Polynomial ℤ))
    (hD : Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0) (hE : ∀ i,
        ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
            Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i))
    (hG : ∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j))
    (hH : ∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) *
        Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D =
            Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ < N →
      ∃ M : ℕ, (M : ℝ) ≤ κ * ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ ∧
      ∃ q : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ → Fin (2 * N) → Fin (2 * N) → Fin M →
          Fin Q.natDegree → ℤ,
        (∀ i j k' μ ν, |((q i j k' μ ν : ℤ) : ℝ)| ≤ Real.exp (κ * ((N : ℝ) ^ 2 *
            Real.sqrt (Real.log (N : ℝ))))) ∧
        (∃ i j k', (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) *
            ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' ≠ 0) ∧
        (∀ i j k', ‖(fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) *
            ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k'‖ ≤ Real.exp (κ * ((N : ℝ) ^ 2 *
                Real.sqrt (Real.log (N : ℝ))))) ∧
        (∀ a b m : ℕ, a < ⌊(N : ℝ) / Real.sqrt (Real.log (N : ℝ))⌋₊ → b < ⌊(N : ℝ) *
            Real.sqrt (Real.log (N : ℝ))⌋₊ → m < ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊ →
          iteratedDeriv m (fun z : ℂ => ∑ i : Fin ⌊(N : ℝ) ^ 2 / Real.sqrt (Real.log (N : ℝ))⌋₊,
              ∑ j : Fin (2 * N), ∑ k' : Fin (2 * N),
              (fun i j k' => ∑ μ : Fin M, ∑ ν : Fin Q.natDegree, ((q i j k' μ ν : ℤ) : ℂ) *
                  ω ^ (μ : ℕ) * ω₁ ^ (ν : ℕ)) i j k' * z ^ (i : ℕ) * Complex.exp ((((j : ℕ) : ℂ) *
                      x₁ + ((k' : ℕ) : ℂ) * x₂) * z)) ((a : ℂ) * y₁ + (b : ℂ) * y₂) = 0) := by
  obtain ⟨κ₁, hκ₁, N₁, hsys⟩ := aux_linear_system x₁ x₂ y₁ y₂ hexp ω ω₁ hω Q hQm hQd hQroot hQmin
    D E G H hD hE hG hH
  obtain ⟨κ, hκle, N₂, hsieg⟩ := siegel_aux ω ω₁ Q hQd hQmin κ₁ hκ₁
  refine ⟨κ, lt_of_lt_of_le hκ₁ hκle, max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨M, hM0, hMle, R, hR, B, hBb, hvan⟩ := hsys N (lt_of_le_of_lt (le_max_left _ _) hN)
  obtain ⟨q, hBq, hqb, hc0, hcb⟩ :=
      hsieg N (lt_of_le_of_lt (le_max_right _ _) hN) M hM0 hMle R hR B hBb
  exact ⟨M, hMle.trans (mul_le_mul_of_nonneg_right hκle (Nat.cast_nonneg _)), q, hqb, hc0, hcb,
    hvan q hBq⟩

end FourExponentials
