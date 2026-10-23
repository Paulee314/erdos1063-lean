/-
Copyright 2026 The Formal Conjectures Authors.
Copyright 2026 Paul Lee.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Adaptation notice: the definition `Erdos1063.n` is copied verbatim from
google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/1063.lean`
(commit `ac02cd5f50407650b37344083b7c1f0f4ed1f96c`). The two theorem statements are the ones
proposed for that file in google-deepmind/formal-conjectures pull request #7552.
-/
module

public import Mathlib

/-!
# Erdős Problem 1063: a lower bound for `n_k` and the structure of the exceptional index

Erdős and Selfridge observed that for `n ≥ 2k` at least one of the `k` consecutive integers
`n, n - 1, …, n - k + 1` fails to divide the binomial coefficient `C(n, k)`. Erdős Problem 1063
(<https://www.erdosproblems.com/1063>; OEIS A389360; Guy, *Unsolved Problems in Number Theory*,
B31) asks for the size of `n_k`, the least `n ≥ 2k` for which exactly one of them fails.
The known upper bounds (Monier, Cambie, and a subexponential bound) are recorded in
google-deepmind/formal-conjectures; this file states two complementary facts.

1. `erdos_1063.variants.lower_bound`: for every `k ≥ 2`,
   `n_k ≥ W'_k := ∏_{p^a ∥ k} p^(a + ⌊log_p (k-1)⌋)`.
   Here `k.primeFactors` is the set of primes dividing `k`, `padicValNat p k = a` is the exponent
   of `p` in `k`, and `Nat.log p (k - 1) = ⌊log_p (k-1)⌋`.
   For example `W'_4 = 8`, `W'_6 = 72`, `W'_14 = 784`, and these are attained:
   `n_4 - 1 = 8`, `n_6 - 3 = 72`, `n_14 - 9 = 784`. For prime `k` the bound is just `k`.

2. `erdos_1063.variants.exception_dvd`: if `n ≥ 2k`, `e < k`, and every `n - i` with
   `0 ≤ i < k`, `i ≠ e`, divides `C(n, k)`, then `e = n mod k` and
   `D(k,e) := ∏_{p^a ∥ k} p^(a + v_p(C(k-1, e)) + ⌊log_p max(e, k-1-e)⌋)` divides `n - e`.
   The hypothesis does not require that `n - e` itself fails to divide `C(n, k)`.
   This sharper exponent was proved informally by the user rickyc in the erdosproblems.com
   discussion thread (10 July 2026). It is the structural fact used by exhaustive searches
   for `n_k`: an admissible `n` with exceptional index `e` must lie in the residue class
   `n ≡ e (mod D(k,e))`.

`n` below is the definition from formal-conjectures, unchanged: `n k` is the infimum of the
set of admissible `m`. (`sInf ∅ = 0` in `ℕ`, but the set is nonempty for every `k ≥ 2`, so the
lower bound is not vacuous; the proof uses Cambie's admissible witness `k · lcm(1, …, k-1)`.)
-/

@[expose] public section

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/-- Lower bound: for $k \ge 2$,
$n_k \ge \prod_{p^a \| k} p^{a + \lfloor \log_p (k-1) \rfloor}$. -/
theorem erdos_1063.variants.lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k := by
  sorry

/-- Structure of the exceptional index: if every $n - i$ with $i \ne e$ divides
$\binom{n}{k}$, then $e = n \bmod k$ and
$\prod_{p^a \| k} p^{a + v_p\binom{k-1}{e} + \lfloor \log_p \max(e, k-1-e) \rfloor}$
divides $n - e$. -/
theorem erdos_1063.variants.exception_dvd {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e := by
  sorry

end Erdos1063
