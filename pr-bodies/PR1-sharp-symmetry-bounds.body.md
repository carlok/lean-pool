Adds `LeanPool/SharpSymmetryBounds`, a Mathlib formalization of Theorem 1 of my note *Sharp symmetry bounds for real algebraic curves* ([PDF](https://github.com/carlok/curve-symmetry-lean/blob/18d3984fd32e7482b98bc0ac42753e8508d236dd/sharp_symmetry_bounds.pdf)). Palomar registered it as [PALOMAR-2026-09-18-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-09-18-000007&version=1), where Comparator checked the five headline declarations and Lean's kernel and nanoda both checked the proof.

**Theorem.** Let `C` be an infinite real plane curve defined by a polynomial `f` of degree `d ≥ 2` that is irreducible over `ℂ`, and suppose `C` is not a circle.
- `sharp_bounds`: the isometries of `ℂ` mapping `C` onto itself form a finite set. The orientation-preserving ones are the powers of a single isometry and number at most `max(d, 2d − 4)`. All of them together number at most `2d`.
- `rotation_bound_sharp`, `full_bound_sharp`: both bounds are attained in every degree `d ≥ 2`.
- `equality_classification`: for `d ≥ 5`, a curve attaining the rotation bound is mapped by some `z ↦ a z + b` onto `Re(z^(d−2)(|z|² + α)) = 0`, with `|α| = 1` and `α` not real.
- `family_attains_bound`: conversely, for `m ≥ 3` and `α` not real, that curve has degree `m + 2`, is irreducible over `ℂ`, and has exactly `2m` rotations.

The statements use Mathlib's own objects: `MvPolynomial (Fin 2) ℝ`, the real zero set inside `ℂ`, `ℂ ≃ᵢ ℂ` and `Set.ncard`. The library also proves that its isometry subgroup is exhaustive, via Mazur–Ulam and the classification of complex linear isometries.

**Context.**
- The rotation bound uses the coefficient-weight criterion of Lebmeir and Richter-Gebert (CAGD 25 (2008), §4).
- The bound `2d` sharpens the auxiliary constant `4d` in Pach–de Zeeuw (arXiv:1308.0177v3, Lemma 2.6).
- The quintic `Re(z³(|z|² + i)) = 0` has six rotations, which contradicts the degree restriction in Lemma 9 of Alcázar–Lávička–Vršek (arXiv:1801.09962v1).
- The note's second theorem (Möbius symmetries and genus of the extremal family) is not part of this PR.

**Port** from `carlok/sharp-symmetry-bounds-lean` at `ced9fe2` (the Palomar commit):
- The 30 library modules are kept, with their proofs unchanged except where Lean/Mathlib v4.36 and the pool's linters required it. Those changes are listed below.
- Each file now has the module system, the four-line header, and a module docstring.
- `set_option autoImplicit false` and `#print axioms` lines are removed.
- The `Challenge`/`Solution` pair is replaced by `Theorem1.lean`, which keeps the registered statements unchanged.

**Changes made for the pool**

- Module system, the four-line header and a module docstring in every file.
- Docstrings for 41 definitions (`docBlame`), and lines wrapped to 100 characters.
- `set_option autoImplicit false` and `#print axioms` lines removed.
- No proof changed; the five statements are the ones registered with Palomar.

**Checks run locally** with Lean v4.36.0 and Mathlib v4.36.0, using the pool's `[leanOptions]` (`warningAsError`, `weak.linter.mathlibStandardSet`):

- `lake build LeanPool.SharpSymmetryBounds.Imports` with Lean v4.36.0, Mathlib v4.36.0 and the pool's `[leanOptions]` (`weak.linter.mathlibStandardSet`; the build reports no warnings, so it passes with `warningAsError`), with the `LeanPoolLinters` plugin loaded.
- `scripts/ci/lint-project.lean` (Batteries' slow declaration linters) passes for every module of the project.
- `python/lean_pool/quality.py`: header, forbidden-text, file-size and project-card checks pass for this project, and the generated card docstring matches the entry module.
- The content guard: only `LeanPool/SharpSymmetryBounds.lean`, `LeanPool/SharpSymmetryBounds/**` and `LeanPool/projects/sharp-symmetry-bounds.yaml` change.

**Provenance: `AI`.** AI coding agents (Claude Opus 5 in Claude Code, and Codex) wrote and repaired the Lean under my direction, from my note.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01WtWPYu3oZU7RJEMLVKo1hy
