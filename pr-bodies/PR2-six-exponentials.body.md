Adds `LeanPool/SixExponentials`, a Mathlib proof of the six exponentials theorem in the general form of Lang (1966, ch. II) and Ramachandra (1968). Palomar registered the classical statement as [PALOMAR-2026-11-22-000020](https://palomar-registry.org/entry?id=PALOMAR-2026-11-22-000020&version=1), where Comparator checked it and three kernels (Lean, nanoda, con-ron) checked the proof.

**Main results**
- `SixExponentials.SX.six_exponentials_of_numberField`: let `d + l < d l`, let `x₁, …, x_d` be linearly independent over `ℚ`, let `y₁, …, y_l` be linearly independent over `ℚ`, and let `K ⊆ ℂ` have finite degree over `ℚ`. Then some `exp(xᵢ yⱼ) ∉ K`.
- `SixExponentials.exists_transcendental_exp`: under the same hypotheses on `x` and `y`, some `exp(xᵢ yⱼ)` is transcendental. This PR adds it, and the library's 2 × 3 theorem `six_exponentials` is now its special case.
- `SixExponentials.six_exponentials_theorem`: the classical case `d = 2`, `l = 3`, in the registered Palomar statement.

**Proof.** Schneider's method relative to a number field `K`:
1. Siegel's lemma gives an exponential polynomial with integer coefficients, not all zero, that vanishes on a box of lattice points `∑ mⱼ yⱼ` (`AuxiliaryFunction`).
2. A Cauchy estimate with zeros, played against Liouville's inequality in `K`, extends the vanishing from each box to the next (`DescentStep`).
3. An exponential polynomial vanishing on the whole lattice has zero coefficients, by Dedekind's independence of characters (`CharacterIndependence`).

**Relation to `roy-strong-six` (already in the pool).** `LeanPool.StrongSix.M2.strongSixExponentials` proves Roy's *strong* six exponentials theorem. It assumes `x` and `y` are linearly independent over the **algebraic numbers** and concludes that some `xᵢ yⱼ` lies outside the `Q̄`-span of `1` and the logarithms of algebraic numbers. The present project differs in three ways:
- **Hypotheses:** it assumes only linear independence over **ℚ**. A ℚ-independent pair `x₁, x₂` with `x₂ = β x₁` for an algebraic irrational `β` is covered here but not by the strong theorem. Recovering it from the strong theorem would also need Gelfond–Schneider, which is not used here.
- **Range:** it covers every `(d, l)` with `d + l < d l`, not only `2 × 3`.
- **Method:** the proof is the elementary auxiliary-function method, with no multiplicity estimate. The strong theorem's proof goes through Philippon's multiplicity estimate.

The two developments are independent: nothing here was taken from `telaviv/strong-six-exponentials`.

**Port** from `carlok/six-exponentials-lean` at `b42d65b` (the Palomar commit). That repository is an extract of `Diaz.six_exponentials` and its import closure from `carlok/diaz-modulus-lean`.
- The eleven modules get UpperCamelCase names.
- `import Mathlib` is replaced by the specific imports each file needs.
- Each file gets the four-line header and a module docstring.
- `exists_transcendental_exp` is new.

**Changes made for the pool**

- Modules renamed to UpperCamelCase; `import Mathlib` replaced by each file's own imports, settled bottom-up with `#min_imports`.
- For Mathlib v4.36 and its linters: `push_neg` → `push Not`, goal-changing `show` → `change`, two unused `simp` arguments dropped, one `positivity` after a non-terminal `simp` replaced by `nlinarith`, and the unused hypothesis `hx` of `SX.descent_step` removed (with its one call site).
- Lines wrapped to 100 characters; two garbled words in docstrings (`solution`) restored.
- New: `exists_transcendental_exp`, the Lang–Ramachandra theorem for every `(d, l)` with `d + l < d l`, in `Main.lean`; `six_exponentials` is its case `d = 2`, `l = 3`, so the argument appears once.
- Removed: the unused definition `SX.OrderAtMost`.

**Checks run** on GitHub Actions with Lean v4.36.0 and Mathlib v4.36.0, using the pool's `[leanOptions]` (`warningAsError`, `weak.linter.mathlibStandardSet`):

- `lake build LeanPool.SixExponentials.Imports` with Lean v4.36.0, Mathlib v4.36.0 and the pool's `[leanOptions]` (`weak.linter.mathlibStandardSet`; the build reports no warnings, so it passes with `warningAsError`), with the `LeanPoolLinters` plugin loaded.
- `scripts/ci/lint-project.lean` (Batteries' slow declaration linters) passes for every module of the project.
- `python/lean_pool/quality.py`: header, forbidden-text, file-size and project-card checks pass for this project, and the generated card docstring matches the entry module.
- The content guard: only `LeanPool/SixExponentials.lean`, `LeanPool/SixExponentials/**` and `LeanPool/projects/six-exponentials.yaml` change.

**Provenance: `AI`.** Claude agents (Claude Code) wrote the Lean proofs under my direction, one statement at a time. The Prove2Me platform checked them before they were mirrored into `diaz-modulus-lean`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01WtWPYu3oZU7RJEMLVKo1hy
