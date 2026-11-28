/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.FourExponentials.ExpEOrExpESqTranscendental
public import LeanPool.FourExponentials.FourExponentialsTrdegOne
public import LeanPool.FourExponentials.TwoAlgebraicallyIndependentOfExpColumn

/-!
# The four exponentials theorem in transcendence degree one

Source: url:https://github.com/carlok/four-exponentials-palomar
Authors: Carlo Perassi
Status: verified
Main declarations: `FourExponentials.four_exponentials_trdeg_one`,
  `FourExponentials.Transcendence.exp_e_or_exp_e_sq_transcendental`,
  `FourExponentials.two_algebraically_independent_of_exp_column`
Tags: transcendence, four-exponentials, gelfond-criterion, algebraic-independence
MSC: 11J81, 11J85, 68V20
-/

/-!
Ported from `carlok/four-exponentials-palomar` at `COMMIT` (Apache-2.0). That repository is a
self-contained extract, from `carlok/diaz-modulus-lean` at `465147a`, of the three compared
theorems and their import closure; its commit `adc5d6e` is the one registered with Palomar as
`PALOMAR-2026-11-28-000054`. Claude agents wrote the proofs under the author's direction, and the
Prove2Me platform checked them. The later commits of that repository, ported here, build it on
Lean and Mathlib v4.36.0 and the pool's linters: they take Hermite–Lindemann from Tau Ceti instead
of a port of the Lindemann–Weierstrass development of Mathlib pull request #28013, prove the Cauchy
estimate with zeros from Tau Ceti's Schwarz lemma with prescribed zeros, drop the unused modules
of the library, and replace `import Mathlib` by the imports each file needs. The port renames the
modules, and the namespaces `Diaz` and `Transcendence` to `FourExponentials` and
`FourExponentials.Transcendence`.

The pool's `SixExponentials` proves the six exponentials theorem of Lang and Ramachandra, which has
no hypothesis on the transcendence degree but needs three exponents in one direction; the four
exponentials theorem here needs only two in each direction, at the cost of the hypothesis that the
four logarithms generate a field of transcendence degree at most one.
-/
