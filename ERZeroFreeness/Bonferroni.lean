/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Poisson limits from factorial moments (`lem:cycle-counts`, method of moments)

The factorial-moment criterion used in the proof of `lem:cycle-counts` (cited there as
[JLR, Theorem 6.10]), for `ℕ^r`-valued variables on finite spaces: if all joint factorial
moments of `X_n` converge to `∏ λ_i^{k_i}`, then `P[X_n = x] → ∏ e^{-λ_i} λ_i^{x_i}/x_i!`
(`tendsto_prob_eq_of_factorial_moments`).  Here `P` and `E` are sums against weights `w_n` on
finite sets `Ω_n`, which only need to be eventually nonnegative.

## Proof

Bonferroni inequalities in one coordinate, then induction on the number `r` of coordinates.

* **One coordinate** (`tendsto_prob_eq_single`).  For `Y, y ∈ ℕ` put
  `B_m(Y) = ∑_{j ≤ m} (-1)^j (Y)_{y+j} / (y! j!) = binom(Y, y) ∑_{j ≤ m} (-1)^j binom(Y - y, j)`
  (`Nat.descFactorial_mul_descFactorial`, `Nat.descFactorial_eq_factorial_mul_choose`).  By
  `Int.alternating_sum_range_choose_eq_choose`, `B_{2M+1}(Y) ≤ 1{Y = y} ≤ B_{2M}(Y)`.  If
  `E_w[(Y)_k] → c λ^k` for all `k`, then `E_w[B_m(Y)] → c (λ^y/y!) ∑_{j ≤ m} (-λ)^j/j!`, and
  these limits tend to `c · e^{-λ} λ^y/y!` as `m → ∞` (exponential series); squeezing gives
  `P_w[Y = y] → c · e^{-λ} λ^y/y!`.  No sign condition on `λ` or `c` is needed.
* **Induction on `r`** (`tendsto_prob_eq_multi`, with an extra constant factor `c`).  For
  `r + 1` coordinates, let `w'` be `w` restricted to the event `X_0 = x_0`.  The factorial
  moment `E_{w'}[∏_{i ≥ 1} (X_i)_{k_i}]` is `P_{u}[X_0 = x_0]` for the eventually
  nonnegative weights `u = w · ∏_{i ≥ 1} (X_i)_{k_i}`, so the one-coordinate case shows that
  it converges to `c e^{-λ_0} λ_0^{x_0}/x_0! · ∏_{i ≥ 1} λ_i^{k_i}`; the induction hypothesis
  for `w'` and `(X_1, …, X_r)` then handles the remaining coordinates.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Pointwise Bonferroni inequalities -/

/-- The truncated Bonferroni sum `B_m(Y) = ∑_{j ≤ m} (-1)^j (Y)_{y+j} / (y! j!)` for the
event `{Y = y}`. -/
private def bonfSum (y m Y : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ j * ((Y.descFactorial (y + j) : ℝ) / ((y.factorial : ℝ) * (j.factorial : ℝ)))

/-- `(Y)_{y+j} / (y! j!) = binom(Y, y) binom(Y - y, j)`. -/
private lemma bonf_descFactorial_div (Y y j : ℕ) :
    (Y.descFactorial (y + j) : ℝ) / ((y.factorial : ℝ) * (j.factorial : ℝ)) =
      (Y.choose y : ℝ) * ((Y - y).choose j : ℝ) := by
  have h1 : Y.descFactorial (y + j) = (Y - y).descFactorial j * Y.descFactorial y := by
    have := Nat.descFactorial_mul_descFactorial (n := Y) (k := y) (m := y + j)
      (Nat.le_add_right y j)
    rw [Nat.add_sub_cancel_left] at this
    exact this.symm
  rw [h1, Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hy : (y.factorial : ℝ) ≠ 0 := by positivity
  have hj : (j.factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- Partial alternating sums of a row of Pascal's triangle, over `ℝ`. -/
private lemma alt_sum_choose_real (N m : ℕ) :
    ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j * (N.choose j : ℝ) =
      if N = 0 then 1 else (-1) ^ m * ((N - 1).choose m : ℝ) := by
  rcases N with _ | n
  · simp [Finset.sum_range_succ']
  · have h := Int.alternating_sum_range_choose_eq_choose (n := n) (m := m)
    have h' := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at h'
    simpa using h'

private lemma bonfSum_eq (y m Y : ℕ) :
    bonfSum y m Y = (Y.choose y : ℝ) *
      (if Y - y = 0 then 1 else (-1) ^ m * ((Y - y - 1).choose m : ℝ)) := by
  rw [bonfSum, ← alt_sum_choose_real, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bonf_descFactorial_div]
  ring

/-- Even truncations of the Bonferroni sum are upper bounds for `1{Y = y}`. -/
private lemma bonfSum_upper (y M Y : ℕ) :
    (if Y = y then (1 : ℝ) else 0) ≤ bonfSum y (2 * M) Y := by
  rw [bonfSum_eq]
  rcases lt_trichotomy Y y with hlt | heq | hgt
  · rw [Nat.choose_eq_zero_of_lt hlt, if_neg hlt.ne]; simp
  · subst heq; simp
  · rw [if_neg hgt.ne', if_neg (by omega), pow_mul]
    norm_num
    positivity

/-- Odd truncations of the Bonferroni sum are lower bounds for `1{Y = y}`. -/
private lemma bonfSum_lower (y M Y : ℕ) :
    bonfSum y (2 * M + 1) Y ≤ (if Y = y then (1 : ℝ) else 0) := by
  rw [bonfSum_eq]
  rcases lt_trichotomy Y y with hlt | heq | hgt
  · rw [Nat.choose_eq_zero_of_lt hlt, if_neg hlt.ne]; simp
  · subst heq; simp
  · rw [if_neg hgt.ne', if_neg (by omega), pow_succ, pow_mul]
    norm_num
    positivity

/-! ### The exponential partial sums -/

/-- The limits of the expected Bonferroni sums, `c (λ^y/y!) ∑_{j ≤ m} (-λ)^j/j!`, tend to
`c · e^{-λ} λ^y/y!`. -/
private lemma tendsto_bonf_limit (c lam : ℝ) (y : ℕ) :
    Tendsto (fun m => ∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ j / ((y.factorial : ℝ) * (j.factorial : ℝ)) * (c * lam ^ (y + j)))
      atTop (𝓝 (c * poisPMF lam y)) := by
  have hs : HasSum (fun n => (-lam) ^ n / (n.factorial : ℝ)) (Real.exp (-lam)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-lam)
  have h1 := (hs.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).const_mul
    (c * lam ^ y / (y.factorial : ℝ))
  convert h1 using 1
  · ext m
    simp only [Function.comp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_pow lam, pow_add]
    field_simp
  · rw [poisPMF]; congr 1; ring

/-! ### The single-variable method of moments -/

/-- **One coordinate.**  If `E_w[(Y)_k] → c λ^k` for every `k`, then
`P_w[Y = y] → c · e^{-λ} λ^y / y!`. -/
private lemma tendsto_prob_eq_single {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (w : ∀ n, Ω n → ℝ) (hw : ∀ᶠ n in atTop, ∀ ω, 0 ≤ w n ω) (Y : ∀ n, Ω n → ℕ)
    (lam c : ℝ)
    (h : ∀ k : ℕ, Tendsto (fun n => ∑ ω, w n ω * ((Y n ω).descFactorial k : ℝ))
      atTop (𝓝 (c * lam ^ k)))
    (y : ℕ) :
    Tendsto (fun n => ∑ ω, if Y n ω = y then w n ω else 0) atTop (𝓝 (c * poisPMF lam y)) := by
  -- expectations of the Bonferroni sums
  have hE : ∀ m : ℕ, Tendsto (fun n => ∑ ω, w n ω * bonfSum y m (Y n ω)) atTop
      (𝓝 (∑ j ∈ Finset.range (m + 1),
        (-1 : ℝ) ^ j / ((y.factorial : ℝ) * (j.factorial : ℝ)) * (c * lam ^ (y + j)))) := by
    intro m
    have : (fun n => ∑ ω, w n ω * bonfSum y m (Y n ω)) = fun n =>
        ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / ((y.factorial : ℝ) * (j.factorial : ℝ)) *
          ∑ ω, w n ω * ((Y n ω).descFactorial (y + j) : ℝ) := by
      ext n
      simp only [bonfSum, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ω _ => ?_
      ring
    rw [this]
    exact tendsto_finsetSum _ fun j _ => (h (y + j)).const_mul _
  have hL := tendsto_bonf_limit c lam y
  -- the Bonferroni sandwich, integrated against the (eventually nonnegative) weights
  have hup : ∀ M : ℕ, ∀ᶠ n in atTop,
      (∑ ω, if Y n ω = y then w n ω else 0) ≤ ∑ ω, w n ω * bonfSum y (2 * M) (Y n ω) := by
    intro M
    filter_upwards [hw] with n hn
    refine Finset.sum_le_sum fun ω _ => ?_
    have := mul_le_mul_of_nonneg_left (bonfSum_upper y M (Y n ω)) (hn ω)
    split_ifs at this ⊢ <;> simp_all
  have hlo : ∀ M : ℕ, ∀ᶠ n in atTop,
      ∑ ω, w n ω * bonfSum y (2 * M + 1) (Y n ω) ≤ ∑ ω, if Y n ω = y then w n ω else 0 := by
    intro M
    filter_upwards [hw] with n hn
    refine Finset.sum_le_sum fun ω _ => ?_
    have := mul_le_mul_of_nonneg_left (bonfSum_lower y M (Y n ω)) (hn ω)
    split_ifs at this ⊢ <;> simp_all
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hL).1 a ha)
    have h1 := (tendsto_order.1 (hE (2 * N + 1))).1 a (hN _ (by omega))
    filter_upwards [h1, hlo N] with n hn1 hn2
    exact lt_of_lt_of_le hn1 hn2
  · obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hL).2 b hb)
    have h1 := (tendsto_order.1 (hE (2 * N))).2 b (hN _ (by omega))
    filter_upwards [h1, hup N] with n hn1 hn2
    exact lt_of_le_of_lt hn2 hn1

/-! ### The multivariate statement, by induction on the number of coordinates -/

/-- **All coordinates**, with an extra constant factor `c` (so that the induction can absorb
the Poisson mass of the first coordinate). -/
private lemma tendsto_prob_eq_multi : ∀ (r : ℕ) {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (w : ∀ n, Ω n → ℝ) (_hw : ∀ᶠ n in atTop, ∀ ω, 0 ≤ w n ω) (X : ∀ n, Ω n → Fin r → ℕ)
    (lam : Fin r → ℝ) (c : ℝ)
    (_h : ∀ k : Fin r → ℕ,
      Tendsto (fun n => ∑ ω, w n ω * ∏ i, ((X n ω i).descFactorial (k i) : ℝ))
        atTop (𝓝 (c * ∏ i, lam i ^ k i)))
    (x : Fin r → ℕ),
    Tendsto (fun n => ∑ ω, if X n ω = x then w n ω else 0) atTop (𝓝 (c * poisProd lam x)) := by
  intro r
  induction r with
  | zero =>
    intro Ω _ w hw X lam c h x
    have hX : ∀ n ω, X n ω = x := fun n ω => Subsingleton.elim _ _
    simp only [hX, if_true]
    simpa [poisProd] using h x
  | succ r ih =>
    intro Ω _ w hw X lam c h x
    -- the weights restricted to the event `X 0 = x 0`
    set w' : ∀ n, Ω n → ℝ := fun n ω => if X n ω 0 = x 0 then w n ω else 0 with hw'def
    have hw' : ∀ᶠ n in atTop, ∀ ω, 0 ≤ w' n ω := by
      filter_upwards [hw] with n hn ω
      simp only [hw'def]
      split_ifs
      · exact hn ω
      · exact le_rfl
    -- factorial moments of the remaining coordinates under `w'`, via the one-coordinate case
    have h' : ∀ k : Fin r → ℕ, Tendsto (fun n => ∑ ω, w' n ω *
        ∏ i : Fin r, ((X n ω i.succ).descFactorial (k i) : ℝ)) atTop
        (𝓝 ((c * poisPMF (lam 0) (x 0)) * ∏ i : Fin r, lam i.succ ^ k i)) := by
      intro k
      have hs := tendsto_prob_eq_single
        (fun n ω => w n ω * ∏ i : Fin r, ((X n ω i.succ).descFactorial (k i) : ℝ)) ?_
        (fun n ω => X n ω 0) (lam 0) (c * ∏ i : Fin r, lam i.succ ^ k i) ?_ (x 0)
      · convert hs using 1
        · ext n
          refine Finset.sum_congr rfl fun ω _ => ?_
          simp only [hw'def]
          split_ifs <;> simp
        · congr 1; ring
      · filter_upwards [hw] with n hn ω
        exact mul_nonneg (hn ω) (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _)
      · intro k0
        have := h (Fin.cons k0 k)
        convert this using 1
        · ext n
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          ring
        · rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          congr 1; ring
    have := ih w' hw' (fun n ω i => X n ω i.succ) (fun i => lam i.succ)
      (c * poisPMF (lam 0) (x 0)) h' (fun i => x i.succ)
    convert this using 1
    · ext n
      refine Finset.sum_congr rfl fun ω _ => ?_
      simp only [hw'def]
      have hiff : X n ω = x ↔
          X n ω 0 = x 0 ∧ (fun i : Fin r => X n ω i.succ) = fun i => x i.succ := by
        constructor
        · rintro rfl; exact ⟨rfl, rfl⟩
        · rintro ⟨h0, hs⟩
          funext i
          exact Fin.cases h0 (fun j => congrFun hs j) i
      by_cases h1 : X n ω 0 = x 0 <;>
        by_cases h2 : (fun i : Fin r => X n ω i.succ) = fun i => x i.succ <;>
        simp [hiff, h1, h2]
    · rw [poisProd, poisProd, Fin.prod_univ_succ]
      congr 1; ring

/-- **Method of factorial moments.**  Let `w_n` be eventually nonnegative weights on finite sets
`Ω_n` and `X_n : Ω_n → ℕ^r`.  If all joint factorial moments `∑_ω w_n(ω) ∏_i (X_n(ω)_i)_{k_i}`
converge to `∏_i λ_i^{k_i}`, then `∑_{ω : X_n(ω) = x} w_n(ω) → ∏_i e^{-λ_i} λ_i^{x_i}/x_i!`
for every `x ∈ ℕ^r`. -/
theorem tendsto_prob_eq_of_factorial_moments {r : ℕ} {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (w : ∀ n, Ω n → ℝ) (hw : ∀ᶠ n in atTop, ∀ ω, 0 ≤ w n ω) (X : ∀ n, Ω n → Fin r → ℕ)
    {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (h : ∀ k : Fin r → ℕ, Tendsto (fun n => ∑ ω, w n ω * ∏ i, ((X n ω i).descFactorial (k i) : ℝ))
      atTop (𝓝 (∏ i, lam i ^ k i)))
    (x : Fin r → ℕ) :
    Tendsto (fun n => ∑ ω, if X n ω = x then w n ω else 0) atTop (𝓝 (poisProd lam x)) := by
  -- `hlam` is not needed: the Bonferroni sandwich works for every real `lam`.
  have := tendsto_prob_eq_multi r w hw X lam 1 (fun k => by simpa using h k) x
  simpa using this

end

end ERZeroFreeness
