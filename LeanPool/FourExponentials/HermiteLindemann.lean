/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import TauCeti.NumberTheory.Transcendental.Lindemann.Corollaries

/-!
# Hermite–Lindemann

The library states the Hermite–Lindemann theorem as `FourExponentials.HermiteLindemannProp` and uses it as
`FourExponentials.hermite_lindemann_holds`. The proof is Tau Ceti's
`TauCeti.transcendental_exp_of_isAlgebraic`.

From `Diaz/HermiteLindemann.lean` and `Diaz/Multipliers.lean` of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean) at `465147a`, where the theorem is
proved from a port of the Lindemann–Weierstrass development of Mathlib pull request #28013; Tau
Ceti's proof replaces that port here.
-/

@[expose] public section

namespace FourExponentials

/-- **Hermite–Lindemann**, as the library states it: for non-zero algebraic `a`, `exp a` is
transcendental. -/
def HermiteLindemannProp : Prop :=
  ∀ a : ℂ, a ≠ 0 → IsAlgebraic ℚ a → Transcendental ℚ (Complex.exp a)

/-- **Hermite–Lindemann** (Tau Ceti's `transcendental_exp_of_isAlgebraic`). -/
theorem hermite_lindemann_holds : HermiteLindemannProp :=
  fun _ ha0 ha => TauCeti.transcendental_exp_of_isAlgebraic ha ha0

end FourExponentials
