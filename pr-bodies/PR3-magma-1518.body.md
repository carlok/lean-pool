Adds `LeanPool/Magma1518`, a core-Lean project (no Mathlib imports) on law 1518 of the Equational Theories Project, `x = (y ◇ y) ◇ (x ◇ (y ◇ x))`.

**Main result (Theorem A).** In every magma satisfying 1518 and 3862 (`x ◇ x = (x ◇ (x ◇ x)) ◇ x`), write `S x = x ◇ x`. For every `x` the set `T = {x, S x, S (S x)}` is closed under `◇`, carries the table `u ◇ v = S v`, and satisfies `S (S (S x)) = x`. So every one-generated such magma is the trivial magma or the three-element shift `x ◇ y = y + 1`. No finiteness is assumed.

- `Magma1518.table`, `Magma1518.cube`, `Magma1518.words_in_T`, `Magma1518.one_or_three`: these are the four declarations Palomar compared for [PALOMAR-2026-09-30-000005](https://palomar-registry.org/entry?id=PALOMAR-2026-09-30-000005&version=1). The statements are unchanged.
- `Magma1518.family_members`: two finite 1518-magmas, with 15 and 39 elements, that violate all four of 47, 614, 817 and 3862. Kernel evaluation checks both.

**Where the statement comes from.** Terence Tao conjectured the classification on the Lean Zulip (Equational, "Austin pairs", 2024-11-29, [message 485148288](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485148288)). He assumed 1518 together with all four of 47, 614, 817 and 3862. Matthew Bolan replied the same day ([485153888](https://leanprover.zulipchat.com/#narrow/channel/458659-Equational/topic/Austin.20pairs/near/485153888)) that 1518 and 3862 already imply the other three, so the hypotheses here are equivalent to Tao's. I searched the ETP sources, the Equational stream, arXiv and Palomar in September 2026 and found no proof. The result may be folklore.

**What is not new, and what is not here.**
- The 15-element member is isomorphic to the ETP's Lean-verified countermodel `Refutation939` (`teorth/equational_theories` at `88088faa`). Here it is defined by its coefficient matrices on `Z/3 × 𝔽₅`, not by a lookup table. The 39-element member over `𝔽₁₃` is new to my knowledge.
- The general family (Theorem F over any ring with `1/2` and `√−1`) is not formalized.
- Also not formalized: the cohomological results of the upstream repository, and its `bv_decide` census. The census needs a native-evaluation axiom, so it is not ported.

**Changes from upstream** (`carlok/magma-1518-obstruction-lean` at `eb2bbde`):
- The definitions moved to `Laws.lean`, and the lemmas now take `Law1518 op` / `Law3862 op` as hypotheses.
- The family tables are written from their coefficient matrices instead of a base-`3p` integer.
- The upstream `set_option maxRecDepth` / `maxHeartbeats` / `exponentiation.threshold` are replaced by `decide +kernel`.
- `#print axioms` lines are removed.

**Checks run** on GitHub Actions with Lean v4.36.0, Mathlib v4.36.0, the pool's `[leanOptions]` and the `LeanPoolLinters` plugin, plus `scripts/ci/lint-project.lean` (passes for all 4 modules):
- The build is clean. The slowest file, `Family.lean`, builds in about 2 s.
- `#print axioms`:
  - `table`, `cube` and `words_in_T` use no axioms.
  - `one_or_three` uses the standard three.
  - `family_members` uses `propext`.
- `python/lean_pool/quality.py` header, forbidden-text and card checks pass for this project. The card docstring matches the generator.

**Provenance: `AI`.** Vampire 5.1.0 found the nine equational proofs behind Theorem A, and an AI agent (Claude, in Claude Code) transcribed them to Lean under my direction. I chose the questions, checked the statements against their sources, and reviewed the Lean.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01WtWPYu3oZU7RJEMLVKo1hy
