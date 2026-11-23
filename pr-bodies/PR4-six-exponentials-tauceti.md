Follow-up to #990, acting on the review note that Tau Ceti already provides supporting lemmas this project proves itself.

## Changes

- **Liouville's inequality.** `Transcendence.liouville_house` was only used with denominator `c = 1`, and in that case it is Tau Ceti's `NumberField.one_le_norm_mul_house_pow`. `DescentStep` now calls the Tau Ceti lemma directly, and `Liouville.lean` is deleted.
- **Cauchy estimate with zeros.** `cauchy_estimate_with_zeros` now uses Tau Ceti's Schwarz lemma with prescribed zeros (`TauCeti.norm_le_mul_prod_div_pow`) on the unit circle, then applies Cauchy's estimate as before. This removes the local zero-division helpers (`FourExpCauchy.order_sub_self`, `order_sub_of_ne`, `peel_one`, `peel`, `factor`) and the hand-written maximum-modulus step. The statement does not change, so `GridEstimate` is untouched.

Net change: 37 lines added, 183 removed, in `LeanPool/SixExponentials/**` only. The project card is unchanged.

## Checks

The branch builds warning-free in a scratch run on my fork. That run also passed the declaration linter (`scripts/ci/lint-project.lean`), `lint-style`, and `mk_all --check`.

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01WtWPYu3oZU7RJEMLVKo1hy
