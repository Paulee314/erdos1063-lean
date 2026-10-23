/-
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
-/
module

public import Erdos1063.Lower

/-!
# Erdős Problem 1063: proved statements

The two declarations below have the same names and types as in `Challenge.lean` (which this
module does not import). The definition `Erdos1063.n` they refer to is the one in
`Erdos1063/Lower.lean`, copied verbatim from formal-conjectures.
-/

@[expose] public section

namespace Erdos1063

/-- Lower bound: for $k \ge 2$,
$n_k \ge \prod_{p^a \| k} p^{a + \lfloor \log_p (k-1) \rfloor}$. -/
theorem erdos_1063.variants.lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k :=
  Erdos1063.lower_bound hk

/-- Structure of the exceptional index: if every $n - i$ with $i \ne e$ divides
$\binom{n}{k}$, then $e = n \bmod k$ and
$\prod_{p^a \| k} p^{a + v_p\binom{k-1}{e} + \lfloor \log_p \max(e, k-1-e) \rfloor}$
divides $n - e$. -/
theorem erdos_1063.variants.exception_dvd {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e :=
  Erdos1063.exception_dvd hk h he hgood

end Erdos1063
