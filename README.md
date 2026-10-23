# Erdős Problem 1063 in Lean: a lower bound for n_k and the structure of the exceptional index

For k ≥ 2, **n_k** is the least n ≥ 2k such that n − i divides the binomial coefficient C(n, k)
for all but exactly one 0 ≤ i < k ([erdosproblems.com/1063](https://www.erdosproblems.com/1063),
OEIS [A389360](https://oeis.org/A389360), Guy B31). Erdős and Selfridge observed that at least one
of n, n − 1, …, n − k + 1 always fails, so n_k asks when exactly one does.

This repository proves two results in Lean 4 with Mathlib. It is registered on Palomar as
[PALOMAR-2026-10-23-000014](https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-23-000014&version=1)
(version 1 = commit `ba104cbcf0bb7c555a8b2f0d58018989a08c638e`). The definition of n_k is copied verbatim from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/ac02cd5f50407650b37344083b7c1f0f4ed1f96c/FormalConjectures/ErdosProblems/1063.lean).

| Lean name | Statement |
|---|---|
| `Erdos1063.erdos_1063.variants.lower_bound` | For every k ≥ 2, n_k ≥ W'_k = ∏_{p^a ∥ k} p^(a + ⌊log_p(k − 1)⌋). |
| `Erdos1063.erdos_1063.variants.exception_dvd` | If n ≥ 2k, e < k, and every n − i with 0 ≤ i < k, i ≠ e, divides C(n, k), then e = n mod k and D(k, e) = ∏_{p^a ∥ k} p^(a + v_p(C(k − 1, e)) + ⌊log_p max(e, k − 1 − e)⌋) divides n − e. |

## What the results say

**The lower bound.** For each prime power p^a exactly dividing k, the one element n − i₀ that fails
to divide C(n, k) must be divisible by p^(a + ⌊log_p(k − 1)⌋). So n_k is at least the product. For
example W'_4 = 8, W'_6 = 72 and W'_14 = 784, and these are attained: n_4 − 1 = 8, n_6 − 3 = 72,
n_14 − 9 = 784. For prime k the bound is only k. The k/2 and k − 1 versions of this bound were first
proved informally by the user rickyc in the problem's
[discussion thread](https://www.erdosproblems.com/forum/thread/1063) (26 June and 10 July 2026).
An independent proof, with the equality cases, is in the author's
[preprint](https://github.com/Paulee314/erdos1063) (Theorem 1.2).

**The exceptional index.** rickyc's sharper exponent (10 July 2026) says more: the failing index is
e = n mod k, and D(k, e) divides n − e. The hypothesis only asks that the *other* k − 1 elements
divide C(n, k). This is what makes exhaustive searches for n_k feasible: an admissible n with
exceptional index e must lie in the residue class e modulo D(k, e). The searches by jbell31
(60 ≤ k ≤ 75) and by the author (up to k = 140) rely on it. jbell31 noted in the thread that a
Lean proof of this divisibility would close the remaining gap in their minimality claims; this is
that proof.

formal-conjectures records upper bounds for n_k (Monier, Cambie, and a subexponential bound,
formalized by the LEAP agent) and the small values n_2, …, n_5, but no general lower bound.
These statements were proposed for that file in
[pull request #7552](https://github.com/google-deepmind/formal-conjectures/pull/7552).

## Files

| Path | Content |
|---|---|
| `Challenge.lean` | The definition of n_k and the two statements, with `sorry`. This is the file to audit. |
| `Solution.lean` | The same two declarations, proved. It does not import `Challenge.lean`. |
| `Erdos1063/Lower.lean` | The proof development: the valuation bound for each prime p ∣ k, W'_k ∣ n − i₀, e = n mod k, the sharper exponent and D(k, e) ∣ n − e, the Erdős–Selfridge observation, and Cambie's admissible number k · lcm(1, …, k − 1), which shows that the set defining n_k is nonempty for k ≥ 3. |
| `AxiomAudit.lean` | `#print axioms` for the main results. Each uses only `propext`, `Classical.choice` and `Quot.sound`. |
| `comparator.json` | The two theorems Comparator compares between `Challenge` and `Solution`. |
| `formalization.yaml` | Provenance, sources, automation and review record. |

## Building

Lean `v4.36.0-rc1` and Mathlib at the matching tag (pinned in `lake-manifest.json`).

```
lake exe cache get   # prebuilt Mathlib
lake build           # builds Challenge (two intentional sorries), the proofs, Solution and AxiomAudit
```

The fully elaborated types (`set_option pp.all true`) of both theorems and of `n` are identical in
the `Challenge` and `Solution` environments.

## Provenance and AI use

The Lean code, including the statements, was written by an AI agent (Claude, Anthropic) at the
author's direction, compiling against Lean and iterating on the errors. The author chose what to
formalize and published the result; he did not write the Lean code by hand and is not a
professional mathematician. The informal mathematics in the preprint was refereed by AI systems
(Gemini 4 Argon, a Meta AI model and Claude Fable 5.1), not by a human expert. See
`formalization.yaml` for details.

## License

Apache License 2.0 (`LICENSE`). The definition of n_k is from google-deepmind/formal-conjectures,
also Apache 2.0; see the notices at the top of `Challenge.lean` and `Erdos1063/Lower.lean`.
