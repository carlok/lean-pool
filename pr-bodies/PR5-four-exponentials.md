Adds `LeanPool/FourExponentials`, the four exponentials theorem in transcendence degree one (Waldschmidt 1973; Brownawell 1974), with two consequences:

- `FourExponentials.four_exponentials_trdeg_one`: if λ₁₁, λ₁₂, λ₂₁, λ₂₂ are non-zero complex numbers whose exponentials are algebraic, λ₁₁ λ₂₂ = λ₁₂ λ₂₁, and ℚ[λ₁₁, λ₁₂, λ₂₁, λ₂₂] has transcendence degree at most one, then the rows or the columns of (λᵢⱼ) are linearly dependent over ℚ. Without the transcendence-degree hypothesis this is the open four exponentials conjecture.
- `FourExponentials.Transcendence.exp_e_or_exp_e_sq_transcendental`: Schneider's eighth problem, that one of e^e and e^{e²} is transcendental.
- `FourExponentials.two_algebraically_independent_of_exp_column`: two of the eight numbers xᵢ, yⱼ, exp(xᵢ yⱼ) are algebraically independent once exp(x₁ y₂) and exp(x₂ y₂) are algebraic.

## Source

The source is [carlok/four-exponentials-palomar](https://github.com/carlok/four-exponentials-palomar) at `8eb91e1`. Its commit `adc5d6e` is registered with Palomar as [PALOMAR-2026-11-28-000054](https://palomar-registry.org/entry?id=PALOMAR-2026-11-28-000054&version=1); Palomar's automated review identified no problems. The repository is an extract of [carlok/diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean). Claude agents wrote the proofs under the author's direction, and the Prove2Me platform checked them (provenance `AI`).

## Changes in `8eb91e1`

`8eb91e1` follows the registered commit and prepares the extract for the pool. The statements are unchanged, and the repository's own CI, including the Comparator check against the registered `Challenge.lean`, passes on it.

- **Tau Ceti instead of vendored code.** Hermite–Lindemann is `TauCeti.transcendental_exp_of_isAlgebraic`; it replaces a 743-line port of Mathlib PR #28013 (Lindemann–Weierstrass). The Cauchy estimate with zeros is proved from `TauCeti.norm_le_mul_prod_div_pow`, as in #992.
- **Unused code dropped.** The ten library modules the three theorems do not use are gone. A declaration-level scan of the remaining modules found no unused declarations.
- **Pool conventions.** Per-file imports instead of `import Mathlib`, and no `set_option` (two proofs that raised heartbeat limits were made cheaper). Every module has a module docstring giving the blueprint statement, its source and references.

The port renames the modules to UpperCamelCase and the namespaces `Diaz` and `Transcendence` to `FourExponentials` and `FourExponentials.Transcendence`.

## Novelty

Neither Mathlib nor Tau Ceti has the four exponentials theorem in transcendence degree one, Schneider's eighth problem, or Gel'fond's transcendence criterion. The pool's `SixExponentials` proves the six exponentials theorem, which needs three exponents in one direction and makes no transcendence-degree assumption.

## Checks

A scratch run on my fork passed:

- the project build, with the pool's `lakefile.toml` and the long-proof plugin;
- `scripts/ci/lint-project.lean`: 60 modules, 639 declarations, no findings;
- `lake exe lint-style`;
- `lake exe mk_all --check`;
- `python -m lean_pool.quality --static-only`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01WtWPYu3oZU7RJEMLVKo1hy
