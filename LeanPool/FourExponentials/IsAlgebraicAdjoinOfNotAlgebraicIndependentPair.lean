/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FinCases

/-!
# Pair dependence: `z` is algebraic over `R[t]`

Let `t` be transcendental over `R`, so that the one-element family `t` is algebraically
independent. Suppose that `z` is transcendental over `R[t]`. Then the family indexed by
`Option Unit` that sends `none` to `z` and `some ()` to `t` is algebraically independent
(`AlgebraicIndependent.option_iff_transcendental`), and `![t, z]` is that family composed with the
injection `![some (), none]`, hence algebraically independent too. This contradicts the hypothesis.

From `Diaz/Mirror/isAlgebraic_adjoin_of_not_algebraicIndependent_pair.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where it mirrors the
proof accepted on Prove2Me as `Transcendence.isAlgebraic_adjoin_of_not_algebraicIndependent_pair`.
-/

@[expose] public section

namespace FourExponentials.Transcendence

/-- **A dependent pair.** Let $R$ be a commutative ring, $A$ a commutative $R$-algebra and $t\in A$
transcendental over $R$. If $t$ and $z\in A$ are not algebraically independent over $R$, then $z$ is
algebraic over the subalgebra $R[t]$. -/
theorem isAlgebraic_adjoin_of_not_algebraicIndependent_pair {R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] {t z : A} (ht : Transcendental R t)
    (h : ¬ AlgebraicIndependent R ![t, z]) :
    IsAlgebraic ↥(Algebra.adjoin R ({t} : Set A)) z := by
  by_contra hz
  apply h
  -- `t` alone is algebraically independent
  have hind : AlgebraicIndependent R (fun _ : Unit => t) :=
    (algebraicIndependent_singleton_iff ()).2 ht
  -- `z` is transcendental over `R[t]`, so the family `(t, z)` indexed by `Option Unit` is too
  have htrans : Transcendental ↥(Algebra.adjoin R (Set.range fun _ : Unit => t)) z := by
    rw [Set.range_const]
    exact hz
  have hopt := (hind.option_iff_transcendental z).2 htrans
  -- `![t, z]` is that family along an injection `Fin 2 → Option Unit`
  have he : Function.Injective (![some (), none] : Fin 2 → Option Unit) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  convert hopt.comp _ he using 1
  funext i
  fin_cases i <;> rfl

end FourExponentials.Transcendence
