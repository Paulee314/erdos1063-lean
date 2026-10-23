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
(commit `ac02cd5f50407650b37344083b7c1f0f4ed1f96c`). Everything else in this file is new.
-/
module

public import Mathlib

/-!
# Erdős Problem 1063: proofs

For `k ≥ 2`, `n_k` is the least `n ≥ 2k` such that `n - i` divides `n.choose k` for all but
exactly one `0 ≤ i < k`. This file proves:

* `valuation_bound`: if every `n - i` with `i ≠ i0` divides `n.choose k` (and `n ≥ 2k`), then
  `v_p(k) + ⌊log_p (k-1)⌋ ≤ v_p(n - i0)` for every prime `p ∣ k`;
* `W_dvd`, `k_dvd`, `index_eq_mod`: hence `W'_k ∣ n - i0`, `k ∣ n - i0`, and `i0 = n % k`;
* `sharp_valuation_bound`, `D_dvd`: the sharper exponent
  `v_p(k) + v_p(C(k-1,e)) + ⌊log_p max(e, k-1-e)⌋ ≤ v_p(n - e)` (proved by the user rickyc in
  the erdosproblems.com discussion thread, 10 July 2026) and its product form;
* `exists_exception'` (Erdős–Selfridge) and `cambie_mem`, `cambie_upper_bound` (Cambie's
  witness `k · lcm(1, …, k-1)` is admissible), which give `W'_k ≤ n_k` for every `k ≥ 3`
  without assuming that an admissible `n` exists;
* `lower_bound`, `exception_dvd`: the two results compared against `Challenge.lean`.
-/

@[expose] public section

open Finset
open scoped Nat

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
(Copied verbatim from `FormalConjectures/ErdosProblems/1063.lean`.)
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/-- Kummer's carry condition, restated as `n % q < k % q`. -/
lemma carry_iff {n k q : ℕ} (hq : 0 < q) (hkn : k ≤ n) :
    q ≤ k % q + (n - k) % q ↔ n % q < k % q := by
  have h1 : n % q = (k % q + (n - k) % q) % q := by
    rw [← Nat.add_mod]; congr 1; omega
  have hk := Nat.mod_lt k hq
  have hm := Nat.mod_lt (n - k) hq
  constructor
  · intro h
    rw [h1, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro h
    by_contra h'
    push Not at h'
    rw [h1, Nat.mod_eq_of_lt h'] at h
    omega

/-- Core statement: `v_p(C(n,k)) + v_p(k) ≤ v_p(n - i0)` and
`v_p(k) + ⌊log_p (k-1)⌋ ≤ v_p(n - i0)`. -/
theorem valuation_bound_aux {n k p i0 : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) :
    padicValNat p (n.choose k) + padicValNat p k ≤ padicValNat p (n - i0) ∧
      padicValNat p k + Nat.log p (k - 1) ≤ padicValNat p (n - i0) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hC : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  set V := padicValNat p (n.choose k) with hV
  set a := padicValNat p k with ha
  set L' := Nat.log p (k - 1) with hL'
  -- good elements have valuation at most V
  have hle : ∀ i < k, i ≠ i0 → padicValNat p (n - i) ≤ V := by
    intro i hi hne
    have : p ^ padicValNat p (n - i) ∣ n.choose k :=
      (pow_padicValNat_dvd).trans (hgood i hi hne)
    exact (padicValNat_dvd_iff_le hC).mp this
  have hdvd_r : ∀ e, p ^ e ∣ n - n % p ^ e := fun e => Nat.dvd_sub_mod n
  -- two multiples of p^e in the block force e ≤ V
  have two : ∀ e, n % p ^ e + p ^ e < k → e ≤ V := by
    intro e he
    have d1 := hdvd_r e
    have d2 : p ^ e ∣ n - (n % p ^ e + p ^ e) := by
      have : n - (n % p ^ e + p ^ e) = (n - n % p ^ e) - p ^ e := by omega
      rw [this]; exact Nat.dvd_sub d1 (dvd_refl _)
    by_cases h : n % p ^ e = i0
    · have hne : n % p ^ e + p ^ e ≠ i0 := by
        have := pow_pos hp.pos e; omega
      have hpos : n - (n % p ^ e + p ^ e) ≠ 0 := by omega
      exact ((padicValNat_dvd_iff_le hpos).mp d2).trans (hle _ he hne)
    · have hpos : n - n % p ^ e ≠ 0 := by omega
      exact ((padicValNat_dvd_iff_le hpos).mp d1).trans (hle _ (by omega) h)
  -- the maximal valuation in the block
  obtain ⟨istar, histar, hmax⟩ := Finset.exists_max_image (Finset.range k)
    (fun i => padicValNat p (n - i)) ⟨0, by simp; omega⟩
  set M := padicValNat p (n - istar) with hM
  have hmaxM : ∀ i < k, padicValNat p (n - i) ≤ M := fun i hi => hmax i (by simpa using hi)
  have reach : ∀ e, n % p ^ e < k → e ≤ M := by
    intro e he
    have hpos : n - n % p ^ e ≠ 0 := by omega
    exact ((padicValNat_dvd_iff_le hpos).mp (hdvd_r e)).trans (hmaxM _ he)
  have hpow_le : ∀ e, p ^ e ≤ k → e ≤ M := fun e he =>
    reach e (lt_of_lt_of_le (Nat.mod_lt _ (pow_pos hp.pos e)) he)
  -- Kummer
  have hkum := padicValNat_choose (p := p) (n := n) (k := k) (b := Nat.log p n + 1)
    (by omega) (Nat.lt_succ_self _)
  set Cset := {i ∈ Finset.Ico 1 (Nat.log p n + 1) | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}
    with hCset
  have hVc : V = Cset.card := hkum
  have carry_mem : ∀ e ∈ Cset, n % p ^ e < k % p ^ e := by
    intro e he
    rw [hCset, Finset.mem_filter] at he
    exact (carry_iff (pow_pos hp.pos e) (by omega)).mp he.2
  have hapos : 1 ≤ a := one_le_padicValNat_of_dvd (by omega) hpk
  have hpa : p ^ a ∣ k := pow_padicValNat_dvd
  have hsub1 : Cset ⊆ Finset.Ioc a M := by
    intro e he
    have hc := carry_mem e he
    rw [Finset.mem_Ioc]
    constructor
    · by_contra hle'
      push Not at hle'
      have : p ^ e ∣ k := (pow_dvd_pow p hle').trans hpa
      rw [Nat.mod_eq_zero_of_dvd this] at hc
      exact Nat.not_lt_zero _ hc
    · exact reach e (lt_of_lt_of_le hc (Nat.mod_le _ _))
  have hVle : V ≤ M - a := by
    rw [hVc]
    have := Finset.card_le_card hsub1
    simpa using this
  have haM : a ≤ M := hpow_le a (Nat.le_of_dvd (by omega) hpa)
  have hL'k : p ^ L' ≤ k - 1 := Nat.pow_log_le_self p (by omega)
  have hL'M : L' ≤ M := hpow_le L' (by omega)
  -- the maximum is attained only at i0
  have hstar : istar = i0 := by
    by_contra hne
    have := hle istar (by simpa using histar) hne
    omega
  have hM0 : padicValNat p (n - i0) = M := by rw [hM, hstar]
  rw [hM0]
  refine ⟨by omega, ?_⟩
  by_cases hcase : L' ≤ V
  · omega
  · push Not at hcase
    have haL : a ≤ L' := by
      by_contra h'
      push Not at h'
      have h1 : p ^ (L' + 1) ≤ k :=
        (Nat.pow_le_pow_right hp.pos h').trans (Nat.le_of_dvd (by omega) hpa)
      have h2 : 2 * p ^ L' ≤ p ^ (L' + 1) := by
        rw [pow_succ]; nlinarith [pow_pos hp.pos L']
      have := two L' (by have := Nat.mod_lt n (pow_pos hp.pos L'); omega)
      omega
    have haV : a ≤ V := by
      have h1 : p ^ a ≤ k - 1 := (Nat.pow_le_pow_right hp.pos haL).trans hL'k
      obtain ⟨m, hm⟩ := hpa
      have hm2 : 2 ≤ m := by
        by_contra h'
        push Not at h'
        interval_cases m <;> simp at hm <;> omega
      have h3 : 2 * p ^ a ≤ k := by rw [hm]; nlinarith [pow_pos hp.pos a]
      exact two a (by have := Nat.mod_lt n (pow_pos hp.pos a); omega)
    have hsub2 : Cset ⊆ Finset.Ioc a M \ Finset.Ioc V L' := by
      intro e he
      rw [Finset.mem_sdiff]
      refine ⟨hsub1 he, ?_⟩
      intro he2
      rw [Finset.mem_Ioc] at he2
      have hc := carry_mem e he
      have hqk : p ^ e ≤ k - 1 := (Nat.pow_le_pow_right hp.pos he2.2).trans hL'k
      have hmodk : k % p ^ e + p ^ e ≤ k := by
        have h5 := Nat.mod_add_div k (p ^ e)
        have hdiv : 1 ≤ k / p ^ e := (Nat.one_le_div_iff (pow_pos hp.pos e)).mpr (by omega)
        have h6 : p ^ e ≤ p ^ e * (k / p ^ e) := by
          simpa using Nat.mul_le_mul_left (p ^ e) hdiv
        omega
      have := two e (by omega)
      omega
    have hsub3 : Finset.Ioc V L' ⊆ Finset.Ioc a M := by
      intro e he; rw [Finset.mem_Ioc] at he ⊢; omega
    have hcard := Finset.card_le_card hsub2
    rw [Finset.card_sdiff_of_subset hsub3] at hcard
    simp only [Nat.card_Ioc] at hcard
    rw [← hVc] at hcard
    omega

/-- **Corollary 5, one prime.** Only the divisibility of the *other* elements is used;
not even `i0 < k` is needed. -/
theorem valuation_bound {n k p i0 : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) :
    padicValNat p k + Nat.log p (k - 1) ≤ padicValNat p (n - i0) :=
  (valuation_bound_aux hp hkn hpk hk hgood).2

/-- A product of powers of distinct primes divides `m` if each factor does. -/
lemma prod_prime_pow_dvd {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (f : ℕ → ℕ) {m : ℕ}
    (h : ∀ p ∈ s, p ^ f p ∣ m) : ∏ p ∈ s, p ^ f p ∣ m := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert q s hq ih =>
    rw [Finset.prod_insert hq]
    have hqs := hs q (Finset.mem_insert_self q s)
    have ih' := ih (fun p hp => hs p (Finset.mem_insert_of_mem hp))
      (fun p hp => h p (Finset.mem_insert_of_mem hp))
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h q (Finset.mem_insert_self q s)) ih'
    apply Nat.Coprime.prod_right
    intro p hp
    have hpp := hs p (Finset.mem_insert_of_mem hp)
    have hne : q ≠ p := fun h' => hq (h' ▸ hp)
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hqs hpp).mpr hne)

/-- `W'_k = ∏_{p ∣ k} p ^ (v_p k + ⌊log_p (k-1)⌋)`. -/
def W (k : ℕ) : ℕ := ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1))

/-- **Corollary 5.** `W'_k` divides the exceptional element. -/
theorem W_dvd {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : W k ∣ n - i0 := by
  unfold W
  apply prod_prime_pow_dvd (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    have := Fact.mk hp.1
    have hpos : n - i0 ≠ 0 := by omega
    exact (padicValNat_dvd_iff_le hpos).mpr (valuation_bound hp.1 hkn hp.2.1 hk hgood)

/-- `k ∣ W'_k`, since `p ^ v_p(k) ∣ p ^ (v_p(k) + ⌊log_p (k-1)⌋)` for every `p ∣ k`. -/
lemma dvd_W {k : ℕ} (hk : k ≠ 0) : k ∣ W k := by
  unfold W
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hk]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  rw [Nat.factorization_def k (Nat.prime_of_mem_primeFactors hp)]
  exact pow_dvd_pow p (Nat.le_add_right _ _)

/-- **The failing index is `n mod k`.** Under the same hypothesis as `W_dvd`, `k ∣ n - i0`;
in particular `i0 = n % k` when `i0 < k`. -/
theorem k_dvd {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : k ∣ n - i0 :=
  (dvd_W (by omega)).trans (W_dvd hkn hk hi0 hgood)

theorem index_eq_mod {n k i0 : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (hi0 : i0 < k)
    (hgood : ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k) : i0 = n % k := by
  obtain ⟨t, ht⟩ := k_dvd hkn hk hi0 hgood
  have h' : n = k * t + i0 := by omega
  rw [h', Nat.mul_add_mod, Nat.mod_eq_of_lt hi0]

lemma padicValNat_prod_range {p : ℕ} [Fact p.Prime] (f : ℕ → ℕ) (m : ℕ)
    (hf : ∀ i < m, f i ≠ 0) :
    padicValNat p (∏ i ∈ Finset.range m, f i) = ∑ i ∈ Finset.range m, padicValNat p (f i) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ,
      padicValNat.mul (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (by simp at hi; omega))
        (hf m (by omega)),
      ih (fun i hi => hf i (by omega))]

lemma prod_range_succ_eq_factorial (m : ℕ) : ∏ y ∈ Finset.range m, (y + 1) = m ! := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.prod_range_succ, ih, Nat.factorial_succ]; ring

/-- **The sharper exponent** (stated and proved by the user rickyc in the erdosproblems.com
thread, 10 July 2026; used by jbell31's search). If every `n - i` with `i ≠ e` divides
`C(n,k)` and `p ∣ k`, then
`v_p(k) + v_p(C(k-1,e)) + ⌊log_p max(e, k-1-e)⌋ ≤ v_p(n - e)`. -/
theorem sharp_valuation_bound {n k p e : ℕ} (hp : p.Prime) (hkn : 2 * k ≤ n) (hpk : p ∣ k)
    (hk : 2 ≤ k) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e))
      ≤ padicValNat p (n - e) := by
  have := Fact.mk hp
  have hC : n.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  obtain ⟨hVM, hLM⟩ := valuation_bound_aux hp hkn hpk hk hgood
  set V := padicValNat p (n.choose k) with hV
  set M := padicValNat p (n - e) with hM
  set a := padicValNat p k with ha
  set m := k - 1 - e with hm
  have hle : ∀ i < k, i ≠ e → padicValNat p (n - i) ≤ V := by
    intro i hi hne
    exact (padicValNat_dvd_iff_le hC).mp ((pow_padicValNat_dvd).trans (hgood i hi hne))
  -- each other element has valuation at most that of its distance to e
  have hlow : ∀ i < e, padicValNat p (n - i) ≤ padicValNat p (e - i) := by
    intro i hi
    have hc := hle i (by omega) (by omega)
    have d1 : p ^ padicValNat p (n - i) ∣ n - i := pow_padicValNat_dvd
    have d2 : p ^ padicValNat p (n - i) ∣ n - e :=
      (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    have d3 := Nat.dvd_sub d1 d2
    rw [show n - i - (n - e) = e - i by omega] at d3
    exact (padicValNat_dvd_iff_le (by omega)).mp d3
  have hhigh : ∀ y < m, padicValNat p (n - (e + 1 + y)) ≤ padicValNat p (y + 1) := by
    intro y hy
    have hc := hle (e + 1 + y) (by omega) (by omega)
    have d1 : p ^ padicValNat p (n - (e + 1 + y)) ∣ n - (e + 1 + y) := pow_padicValNat_dvd
    have d2 : p ^ padicValNat p (n - (e + 1 + y)) ∣ n - e :=
      (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    have d3 := Nat.dvd_sub d2 d1
    rw [show n - e - (n - (e + 1 + y)) = y + 1 by omega] at d3
    exact (padicValNat_dvd_iff_le (by omega)).mp d3
  -- the whole block: sum of valuations = v_p(k!) + V
  have hprod := padicValNat_prod_range (p := p) (fun i => n - i) k (fun i hi => by omega)
  rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose,
    padicValNat.mul (Nat.factorial_ne_zero k) hC] at hprod
  have hsplit : ∑ i ∈ Finset.range k, padicValNat p (n - i) =
      ∑ i ∈ Finset.range e, padicValNat p (n - i) + M +
      ∑ y ∈ Finset.range m, padicValNat p (n - (e + 1 + y)) := by
    have hk' : k = (e + 1) + m := by omega
    conv_lhs => rw [hk']
    rw [Finset.sum_range_add, Finset.sum_range_succ]
  have hefac : padicValNat p (e !) = ∑ i ∈ Finset.range e, padicValNat p (e - i) := by
    have h := padicValNat_prod_range (p := p) (fun i => e - i) e (fun i hi => by omega)
    rw [← Nat.descFactorial_eq_prod_range, Nat.descFactorial_self] at h
    exact h
  have hmfac : padicValNat p (m !) = ∑ y ∈ Finset.range m, padicValNat p (y + 1) := by
    have h := padicValNat_prod_range (p := p) (fun y => y + 1) m (fun y hy => by omega)
    rw [prod_range_succ_eq_factorial] at h
    exact h
  have hkfac : padicValNat p (k !) =
      a + padicValNat p ((k - 1).choose e) + padicValNat p (e !) + padicValNat p (m !) := by
    rw [← Nat.mul_factorial_pred (by omega : k ≠ 0),
      ← Nat.choose_mul_factorial_mul_factorial (by omega : e ≤ k - 1),
      padicValNat.mul (by omega) (Nat.mul_ne_zero (Nat.mul_ne_zero
        (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)),
      padicValNat.mul (Nat.mul_ne_zero (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _),
      padicValNat.mul (Nat.choose_pos (by omega)).ne' (Nat.factorial_ne_zero _)]
    ring
  have hsumlow : ∑ i ∈ Finset.range e, padicValNat p (n - i) ≤
      ∑ i ∈ Finset.range e, padicValNat p (e - i) :=
    Finset.sum_le_sum fun i hi => hlow i (by simpa using hi)
  have hsumhigh : ∑ y ∈ Finset.range m, padicValNat p (n - (e + 1 + y)) ≤
      ∑ y ∈ Finset.range m, padicValNat p (y + 1) :=
    Finset.sum_le_sum fun y hy => hhigh y (by simpa using hy)
  have key : V + a + padicValNat p ((k - 1).choose e) ≤ M := by omega
  -- some other element sits at distance p^u from e, so u ≤ V
  have hu : Nat.log p (max e m) ≤ V := by
    set r := max e m with hr
    have h1 := le_max_left e m
    have h2 := le_max_right e m
    have hrk : r ≤ k - 1 := max_le (by omega) (by omega)
    have hr0 : r ≠ 0 := by omega
    set u := Nat.log p r with hu'
    have hpu : p ^ u ≤ r := Nat.pow_log_le_self p hr0
    have hu1 : 1 ≤ p ^ u := Nat.one_le_pow _ _ hp.pos
    have hulog : u ≤ Nat.log p (k - 1) := Nat.log_mono_right hrk
    have hpuM : p ^ u ∣ n - e := (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    rcases le_total m e with h | h
    · have hre : r = e := by rw [hr]; exact max_eq_left h
      have hd : p ^ u ∣ n - (e - p ^ u) := by
        rw [show n - (e - p ^ u) = (n - e) + p ^ u by omega]
        exact Nat.dvd_add hpuM dvd_rfl
      exact ((padicValNat_dvd_iff_le (by omega)).mp hd).trans (hle _ (by omega) (by omega))
    · have hre : r = m := by rw [hr]; exact max_eq_right h
      have hd : p ^ u ∣ n - (e + p ^ u) := by
        rw [show n - (e + p ^ u) = (n - e) - p ^ u by omega]
        exact Nat.dvd_sub hpuM dvd_rfl
      exact ((padicValNat_dvd_iff_le (by omega)).mp hd).trans (hle _ (by omega) (by omega))
  omega

/-- rickyc's divisibility in product form: `D(k,e) = ∏_{p^a ∥ k}
p^(a + v_p(C(k-1,e)) + ⌊log_p max(e,k-1-e)⌋)` divides `n - e`. Together with
`index_eq_mod` this is exactly the structural input of jbell31's exhaustive search. -/
theorem D_dvd {n k e : ℕ} (hkn : 2 * k ≤ n) (hk : 2 ≤ k) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    (∏ p ∈ k.primeFactors,
      p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e))))
      ∣ n - e := by
  apply prod_prime_pow_dvd (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  intro p hp
  rw [Nat.mem_primeFactors] at hp
  have := Fact.mk hp.1
  exact (padicValNat_dvd_iff_le (by omega)).mpr
    (sharp_valuation_bound hp.1 hkn hp.2.1 hk he hgood)

/-- **Lower bound.** `W'_k ≤ n_k` (whenever an admissible `m` exists, e.g. for `k ≥ 3`
by Cambie's bound, formalized by DeepMind's LEAP agent). -/
theorem W_le_n {k : ℕ} (hk : 2 ≤ k)
    (hne : {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}.Nonempty) : W k ≤ n k := by
  unfold n
  obtain ⟨h2k, i0, hi0, -, hgood⟩ := Nat.sInf_mem hne
  have hd := W_dvd h2k hk hi0 hgood
  exact (Nat.le_of_dvd (by omega) hd).trans (Nat.sub_le _ _)

/-- **Erdős–Selfridge.** Not every element of the block divides `n.choose k`
(derived from `valuation_bound`: a prime `p ∣ k` would have to divide both `n` and `n - 1`). -/
theorem exists_exception' {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) :
    ¬ ∀ i < k, (n - i) ∣ n.choose k := by
  intro hall
  have hp : (k.minFac).Prime := Nat.minFac_prime (by omega)
  have hpk : k.minFac ∣ k := Nat.minFac_dvd k
  have h0 := valuation_bound (i0 := 0) hp hkn hpk hk (fun i hi _ => hall i hi)
  have h1 := valuation_bound (i0 := 1) hp hkn hpk hk (fun i hi _ => hall i hi)
  have := Fact.mk hp
  have ha : 1 ≤ padicValNat k.minFac k := one_le_padicValNat_of_dvd (by omega) hpk
  have d0 : k.minFac ∣ n - 0 := dvd_of_one_le_padicValNat (by omega)
  have d1 : k.minFac ∣ n - 1 := dvd_of_one_le_padicValNat (by omega)
  have hsub := Nat.dvd_sub d0 d1
  rw [show (n - 0) - (n - 1) = 1 by omega] at hsub
  exact hp.one_lt.ne' (Nat.dvd_one.mp hsub)

lemma lcm_facts {k : ℕ} (hk : 3 ≤ k) :
    (Finset.Icc 1 (k - 1)).lcm id ≠ 0 ∧ 2 ≤ (Finset.Icc 1 (k - 1)).lcm id := by
  have hL0 : (Finset.Icc 1 (k - 1)).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; simp
  refine ⟨hL0, Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) ?_⟩
  have : (2:ℕ) ∈ Finset.Icc 1 (k - 1) := by simp; omega
  exact Finset.dvd_lcm this

/-- In Cambie's witness `m = k * lcm(1, …, k-1)`, every `m - i` with `1 ≤ i < k`
divides `m.choose k`. -/
theorem cambie_good {k i : ℕ} (hk : 3 ≤ k) (hi1 : 1 ≤ i) (hik : i < k) :
    (k * (Finset.Icc 1 (k - 1)).lcm id - i) ∣ (k * (Finset.Icc 1 (k - 1)).lcm id).choose k := by
  obtain ⟨hL0, hL2⟩ := lcm_facts hk
  set L := (Finset.Icc 1 (k - 1)).lcm id with hL
  set m := k * L with hm
  have hkm : 2 * k ≤ m := by rw [hm]; nlinarith
  have hC : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p e hp hpe
  have := Fact.mk hp
  have hmi0 : m - i ≠ 0 := by omega
  set c := padicValNat p (m - i) with hc
  have hec : e ≤ c := (padicValNat_dvd_iff_le hmi0).mp hpe
  suffices hcV : c ≤ padicValNat p (m.choose k) from
    (padicValNat_dvd_iff_le hC).mpr (hec.trans hcV)
  set A := Nat.log p (k - 1) with hA
  have hpA : p ^ A ≤ k - 1 := Nat.pow_log_le_self p (by omega)
  have hA1 : k - 1 < p ^ (A + 1) := Nat.lt_pow_succ_log_self hp.one_lt (k - 1)
  have hpAL : p ^ A ∣ L := by
    have : p ^ A ∈ Finset.Icc 1 (k - 1) := by
      simp only [Finset.mem_Icc]; exact ⟨Nat.one_le_pow _ _ hp.pos, hpA⟩
    exact Finset.dvd_lcm this
  have hkum := padicValNat_choose (p := p) (n := m) (k := k) (b := Nat.log p m + 1)
    (by omega) (Nat.lt_succ_self _)
  set Cs := {a ∈ Finset.Ico 1 (Nat.log p m + 1) | p ^ a ≤ k % p ^ a + (m - k) % p ^ a}
    with hCs
  rw [hkum]
  have mem_of : ∀ a, 1 ≤ a → p ^ a ≤ m → m % p ^ a < k % p ^ a → a ∈ Cs := by
    intro a ha1 hpm hcar
    rw [hCs, Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨ha1, Nat.lt_succ_of_le (Nat.le_log_of_pow_le hp.one_lt hpm)⟩, ?_⟩
    exact (carry_iff (pow_pos hp.pos a) (by omega)).mpr hcar
  by_cases hcA : c ≤ A
  · -- carries at the A levels (v_p k, v_p k + A]
    set s := padicValNat p k with hs
    have hsub : Finset.Ioc s (s + A) ⊆ Cs := by
      intro a ha
      rw [Finset.mem_Ioc] at ha
      have hdm : p ^ a ∣ m := (pow_dvd_pow p ha.2).trans (by
        rw [pow_add, hm]; exact Nat.mul_dvd_mul pow_padicValNat_dvd hpAL)
      have hnk : ¬ p ^ a ∣ k := fun h => by
        have := (padicValNat_dvd_iff_le (by omega)).mp h; omega
      apply mem_of a (by omega) (Nat.le_of_dvd (by omega) hdm)
      rw [Nat.mod_eq_zero_of_dvd hdm]
      exact Nat.pos_of_ne_zero (fun h => hnk (Nat.dvd_of_mod_eq_zero h))
    have h := Finset.card_le_card hsub
    rw [Nat.card_Ioc] at h
    omega
  · push Not at hcA
    have hdvd : p ^ (A + 1) ∣ m - i := (pow_dvd_pow p hcA).trans pow_padicValNat_dvd
    have hpk : ¬ p ∣ k := by
      intro hpk
      have hdm : p ^ (A + 1) ∣ m := by
        rw [hm, pow_succ, mul_comm (p ^ A) p]; exact Nat.mul_dvd_mul hpk hpAL
      have hdi : p ^ (A + 1) ∣ i := by
        have h' := Nat.dvd_sub hdm hdvd
        rwa [show m - (m - i) = i by omega] at h'
      have := Nat.le_of_dvd (by omega) hdi
      omega
    have hkp : k < p ^ (A + 1) := by
      rcases Nat.lt_or_ge k (p ^ (A + 1)) with h | h
      · exact h
      · exfalso
        have h' : p ^ (A + 1) = k := by omega
        exact hpk (h' ▸ dvd_pow_self p (Nat.succ_ne_zero A))
    have hsub : Finset.Icc 1 c ⊆ Cs := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have hdmi : p ^ a ∣ m - i := (pow_dvd_pow p ha.2).trans pow_padicValNat_dvd
      by_cases haA : a ≤ A
      · have hdm : p ^ a ∣ m := (pow_dvd_pow p haA).trans (hpAL.trans (dvd_mul_left L k))
        apply mem_of a ha.1 (Nat.le_of_dvd (by omega) hdm)
        rw [Nat.mod_eq_zero_of_dvd hdm]
        apply Nat.pos_of_ne_zero
        intro h
        exact hpk ((dvd_pow_self p (by omega)).trans (Nat.dvd_of_mod_eq_zero h))
      · push Not at haA
        have hka : k < p ^ a := lt_of_lt_of_le hkp (Nat.pow_le_pow_right hp.pos haA)
        have hmod : m % p ^ a = i := by
          obtain ⟨t, ht⟩ := hdmi
          have h' : m = p ^ a * t + i := by omega
          rw [h', Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
        apply mem_of a ha.1 ((Nat.le_of_dvd (Nat.pos_of_ne_zero hmi0) hdmi).trans (Nat.sub_le _ _))
        rw [hmod, Nat.mod_eq_of_lt hka]
        exact hik
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    omega

/-- Cambie's witness is admissible, with exceptional index `0`. -/
theorem cambie_mem {k : ℕ} (hk : 3 ≤ k) :
    k * (Finset.Icc 1 (k - 1)).lcm id ∈ {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k} := by
  obtain ⟨hL0, hL2⟩ := lcm_facts hk
  have h2k : 2 * k ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by nlinarith
  refine ⟨h2k, 0, by omega, ?_, ?_⟩
  · intro hdiv
    apply exists_exception' (by omega) h2k
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact hdiv
    · exact cambie_good hk hpos hi
  · intro i hi hne
    exact cambie_good hk (Nat.pos_of_ne_zero hne) hi

/-- **Cambie's upper bound** (same statement as `erdos_1063.variants.cambie_upper_bound`). -/
theorem cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) : n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id :=
  Nat.sInf_le (cambie_mem hk)

/-- **Main result (unconditional).** For `k ≥ 3`, `W'_k ≤ n_k`. -/
theorem W_le_n_of_three_le {k : ℕ} (hk : 3 ≤ k) : W k ≤ n k :=
  W_le_n (by omega) ⟨_, cambie_mem hk⟩

/-! ### The two headline results (restated with the same types in `Solution.lean`) -/

/-- Lower bound: for $k \ge 2$,
$n_k \ge \prod_{p^a \| k} p^{a + \lfloor \log_p (k-1) \rfloor}$. -/
theorem lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ p ∈ k.primeFactors, p ^ (padicValNat p k + Nat.log p (k - 1)) ≤ n k := by
  rcases Nat.lt_or_ge k 3 with h3 | h3
  · obtain rfl : k = 2 := by omega
    exact W_le_n le_rfl ⟨4, by decide⟩
  · exact W_le_n_of_three_le h3

/-- Structure of the exceptional index: if every $n - i$ with $i \ne e$ divides
$\binom{n}{k}$, then $e = n \bmod k$ and
$\prod_{p^a \| k} p^{a + v_p\binom{k-1}{e} + \lfloor \log_p \max(e, k-1-e) \rfloor}$
divides $n - e$. -/
theorem exception_dvd {n k e : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) (he : e < k)
    (hgood : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k) :
    e = n % k ∧
      ∏ p ∈ k.primeFactors,
        p ^ (padicValNat p k + padicValNat p ((k - 1).choose e) + Nat.log p (max e (k - 1 - e)))
        ∣ n - e :=
  ⟨index_eq_mod h hk he hgood, D_dvd h hk he hgood⟩

end Erdos1063
