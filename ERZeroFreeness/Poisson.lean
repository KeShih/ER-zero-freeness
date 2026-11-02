/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Poisson facts

Facts about the Poisson mass function `poisPMF` and the product law `poisProd` on `ℕ^r`:
the moments `E P = λ`, `E (P-λ)² = λ` and `E|P-λ| ≤ √λ` (from `|y| ≤ (y²/a + a)/2` with
`a = √λ`), Markov's inequality on `ℕ^r`, and the "limsup over arbitrary sets" lemma
`eventually_sum_mem_le`: pointwise convergence of mass functions on the countable space `ℕ^r`
to the product Poisson law gives `limsup P_n(B) ≤ P(B)` for every `B` (pick a finite `F` with
`P(F) > 1-ε`; `P_n(B) ≤ total_n - P_n(F \ B)`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

theorem poisPMF_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) : 0 ≤ poisPMF lam k := by
  unfold poisPMF
  positivity

theorem hasSum_poisPMF {lam : ℝ} (hlam : 0 ≤ lam) : HasSum (poisPMF lam) 1 :=
  ProbabilityTheory.hasSum_one_poissonMeasure ⟨lam, hlam⟩

theorem summable_poisPMF_mul_pow {lam : ℝ} (hlam : 0 ≤ lam) (m : ℕ) :
    Summable fun k => poisPMF lam k * (k : ℝ) ^ m := by
  have hs : Summable fun k : ℕ =>
      Real.exp (-lam) * m.factorial * ((Real.exp 1 * lam) ^ k / k.factorial) :=
    (Real.summable_pow_div_factorial _).mul_left _
  refine hs.of_nonneg_of_le (fun k => mul_nonneg (poisPMF_nonneg hlam k) (by positivity))
    (fun k => ?_)
  have h1 : (k : ℝ) ^ m ≤ m.factorial * Real.exp k := by
    have := Real.pow_div_factorial_le_exp (k : ℝ) k.cast_nonneg m
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h2 : Real.exp k = Real.exp 1 ^ k := by
    rw [← Real.exp_nat_mul, mul_one]
  calc poisPMF lam k * (k : ℝ) ^ m ≤ poisPMF lam k * (m.factorial * Real.exp k) :=
        mul_le_mul_of_nonneg_left h1 (poisPMF_nonneg hlam k)
    _ = _ := by unfold poisPMF; rw [h2, mul_pow]; ring

/-- A series on `ℕ` whose first `k` terms vanish has the same sum as its `k`-shift. -/
private lemma hasSum_of_hasSum_shift_of_vanish {f : ℕ → ℝ} (k : ℕ) (hf : ∀ i < k, f i = 0)
    {a : ℝ} (h : HasSum (fun n => f (n + k)) a) : HasSum f a := by
  refine (hasSum_nat_add_iff' k).mp ?_
  rwa [Finset.sum_eq_zero (fun i hi => hf i (Finset.mem_range.mp hi)), sub_zero]

/-- First moment of the Poisson law, as a `HasSum`. -/
private lemma hasSum_poisPMF_mul_natCast {lam : ℝ} (hlam : 0 ≤ lam) :
    HasSum (fun k => poisPMF lam k * (k : ℝ)) lam := by
  refine hasSum_of_hasSum_shift_of_vanish 1 (fun i hi => ?_) ?_
  · obtain rfl : i = 0 := by omega
    simp
  · have key : ∀ k : ℕ, poisPMF lam (k + 1) * ((k + 1 : ℕ) : ℝ) = lam * poisPMF lam k := by
      intro k
      unfold poisPMF
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    simp_rw [key]
    simpa using (hasSum_poisPMF hlam).mul_left lam

/-- Second factorial moment of the Poisson law, as a `HasSum`. -/
private lemma hasSum_poisPMF_mul_descFactorial {lam : ℝ} (hlam : 0 ≤ lam) :
    HasSum (fun k => poisPMF lam k * ((k : ℝ) * ((k : ℝ) - 1))) (lam ^ 2) := by
  refine hasSum_of_hasSum_shift_of_vanish 2 (fun i hi => ?_) ?_
  · interval_cases i <;> simp
  · have key : ∀ k : ℕ, poisPMF lam (k + 2) * (((k + 2 : ℕ) : ℝ) * (((k + 2 : ℕ) : ℝ) - 1)) =
        lam ^ 2 * poisPMF lam k := by
      intro k
      unfold poisPMF
      rw [Nat.factorial_succ, Nat.factorial_succ, pow_add]
      push_cast
      field_simp
      ring
    simp_rw [key]
    simpa using (hasSum_poisPMF hlam).mul_left (lam ^ 2)

/-- Variance of the Poisson law, as a `HasSum`. -/
private lemma hasSum_poisPMF_mul_sub_sq {lam : ℝ} (hlam : 0 ≤ lam) :
    HasSum (fun k => poisPMF lam k * ((k : ℝ) - lam) ^ 2) lam := by
  have h := ((hasSum_poisPMF_mul_descFactorial hlam).add
    ((hasSum_poisPMF_mul_natCast hlam).mul_left (1 - 2 * lam))).add
    ((hasSum_poisPMF hlam).mul_left (lam ^ 2))
  convert h using 1
  · ext k
    ring
  · ring

theorem poisExp_natCast {lam : ℝ} (hlam : 0 ≤ lam) : poisExp lam (fun k => (k : ℝ)) = lam :=
  (hasSum_poisPMF_mul_natCast hlam).tsum_eq

theorem poisExp_sub_sq {lam : ℝ} (hlam : 0 ≤ lam) :
    poisExp lam (fun k => ((k : ℝ) - lam) ^ 2) = lam :=
  (hasSum_poisPMF_mul_sub_sq hlam).tsum_eq

theorem summable_poisPMF_mul_abs_sub {lam : ℝ} (hlam : 0 ≤ lam) :
    Summable fun k => poisPMF lam k * |(k : ℝ) - lam| := by
  have hs : Summable fun k => poisPMF lam k * (k : ℝ) + lam * poisPMF lam k :=
    (hasSum_poisPMF_mul_natCast hlam).summable.add ((hasSum_poisPMF hlam).summable.mul_left lam)
  refine hs.of_nonneg_of_le (fun k => mul_nonneg (poisPMF_nonneg hlam k) (abs_nonneg _))
    (fun k => ?_)
  have hk : |(k : ℝ) - lam| ≤ k + lam := by
    rw [abs_le]
    constructor <;> linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
  calc poisPMF lam k * |(k : ℝ) - lam| ≤ poisPMF lam k * (k + lam) :=
        mul_le_mul_of_nonneg_left hk (poisPMF_nonneg hlam k)
    _ = _ := by ring

theorem poisExp_abs_sub_le {lam : ℝ} (hlam : 0 ≤ lam) :
    poisExp lam (fun k => |(k : ℝ) - lam|) ≤ Real.sqrt lam := by
  rcases hlam.eq_or_lt with h | h
  · -- `λ = 0`: the law is the point mass at `0`.
    subst h
    unfold poisExp
    have h0 : (fun k : ℕ => poisPMF 0 k * |(k : ℝ) - 0|) = fun _ => 0 := by
      funext k
      cases k with
      | zero => simp
      | succ k => simp [poisPMF]
    rw [h0, tsum_zero, Real.sqrt_zero]
  · set a := Real.sqrt lam with ha_def
    have ha : 0 < a := Real.sqrt_pos.mpr h
    have hlam_a : lam = a ^ 2 := (Real.sq_sqrt hlam).symm
    have hle : ∀ k : ℕ, poisPMF lam k * |(k : ℝ) - lam| ≤
        (1 / (2 * a)) * (poisPMF lam k * ((k : ℝ) - lam) ^ 2) + (a / 2) * poisPMF lam k := by
      intro k
      have hy : |(k : ℝ) - lam| ≤ (1 / (2 * a)) * ((k : ℝ) - lam) ^ 2 + a / 2 := by
        have h1 := sq_nonneg (|(k : ℝ) - lam| - a)
        have h2 := sq_abs ((k : ℝ) - lam)
        rw [div_mul_eq_mul_div, one_mul, div_add_div _ _ (by positivity) (by norm_num),
          le_div_iff₀ (by positivity)]
        nlinarith
      calc poisPMF lam k * |(k : ℝ) - lam|
          ≤ poisPMF lam k * ((1 / (2 * a)) * ((k : ℝ) - lam) ^ 2 + a / 2) :=
            mul_le_mul_of_nonneg_left hy (poisPMF_nonneg hlam k)
        _ = _ := by ring
    have hsum : HasSum (fun k => (1 / (2 * a)) * (poisPMF lam k * ((k : ℝ) - lam) ^ 2) +
        (a / 2) * poisPMF lam k) ((1 / (2 * a)) * lam + (a / 2) * 1) :=
      ((hasSum_poisPMF_mul_sub_sq hlam).mul_left _).add ((hasSum_poisPMF hlam).mul_left _)
    have := hasSum_le hle (summable_poisPMF_mul_abs_sub hlam).hasSum hsum
    calc poisExp lam (fun k => |(k : ℝ) - lam|) ≤ (1 / (2 * a)) * lam + (a / 2) * 1 := this
      _ = a := by rw [hlam_a]; field_simp; ring

theorem poisProd_nonneg {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i) (x : Fin r → ℕ) :
    0 ≤ poisProd lam x :=
  Finset.prod_nonneg fun i _ => poisPMF_nonneg (hlam i) (x i)

/-- Product of nonnegative series over `ℕ^r`: if `F i` has sum `s i` for every `i`, then
`x ↦ ∏ i, F i (x i)` has sum `∏ i, s i`. -/
private lemma hasSum_fin_pi_prod {r : ℕ} (F : Fin r → ℕ → ℝ) (hF : ∀ i k, 0 ≤ F i k)
    (s : Fin r → ℝ) (h : ∀ i, HasSum (F i) (s i)) :
    HasSum (fun x : Fin r → ℕ => ∏ i, F i (x i)) (∏ i, s i) := by
  induction r with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact hasSum_unique (fun _ : Fin 0 → ℕ => (1 : ℝ))
  | succ r ih =>
    have h0 := h 0
    have ht := ih (fun i => F i.succ) (fun i k => hF i.succ k) (fun i => s i.succ)
      (fun i => h i.succ)
    have hsumm : Summable fun p : ℕ × (Fin r → ℕ) => F 0 p.1 * ∏ i : Fin r, F i.succ (p.2 i) :=
      Summable.mul_of_nonneg (f := F 0) (g := fun x : Fin r → ℕ => ∏ i : Fin r, F i.succ (x i))
        h0.summable ht.summable (fun k => hF 0 k)
        (fun x => Finset.prod_nonneg fun i _ => hF i.succ (x i))
    have hmul := h0.mul ht hsumm
    have hfun : (fun x : Fin (r + 1) → ℕ => ∏ i, F i (x i)) ∘ (Fin.consEquiv (fun _ => ℕ)) =
        fun p : ℕ × (Fin r → ℕ) => F 0 p.1 * ∏ i : Fin r, F i.succ (p.2 i) := by
      funext ⟨k, y⟩
      simp [Fin.consEquiv_apply, Fin.prod_univ_succ]
    have hcomp : HasSum ((fun x : Fin (r + 1) → ℕ => ∏ i, F i (x i)) ∘
        (Fin.consEquiv (fun _ => ℕ))) (∏ i, s i) := by
      rw [hfun, Fin.prod_univ_succ]
      exact hmul
    exact (Fin.consEquiv (fun _ => ℕ)).hasSum_iff.mp hcomp

theorem hasSum_poisProd {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i) :
    HasSum (poisProd lam) 1 := by
  have H := hasSum_fin_pi_prod (fun i k => poisPMF (lam i) k)
    (fun i k => poisPMF_nonneg (hlam i) k) (fun _ => 1) (fun i => hasSum_poisPMF (hlam i))
  simp only [Finset.prod_const_one] at H
  exact H

theorem poisProb_nonneg {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (B : Set (Fin r → ℕ)) : 0 ≤ poisProb lam B :=
  tsum_nonneg fun x => Set.indicator_nonneg (fun x _ => poisProd_nonneg hlam x) x

theorem poisProb_mono {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B B' : Set (Fin r → ℕ)} (h : B ⊆ B') : poisProb lam B ≤ poisProb lam B' := by
  have hs := (hasSum_poisProd hlam).summable
  exact Summable.tsum_le_tsum
    (fun x => Set.indicator_le_indicator_of_subset h (fun x => poisProd_nonneg hlam x) x)
    (hs.indicator _) (hs.indicator _)

theorem poisProb_union_le {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (B B' : Set (Fin r → ℕ)) : poisProb lam (B ∪ B') ≤ poisProb lam B + poisProb lam B' := by
  have hs := (hasSum_poisProd hlam).summable
  unfold poisProb
  rw [← Summable.tsum_add (hs.indicator _) (hs.indicator _)]
  refine Summable.tsum_le_tsum (fun x => ?_) (hs.indicator _)
    ((hs.indicator _).add (hs.indicator _))
  have h1 := congrFun (Set.indicator_union_add_inter (poisProd lam) B B') x
  have h2 : 0 ≤ (B ∩ B').indicator (poisProd lam) x :=
    Set.indicator_nonneg (fun x _ => poisProd_nonneg hlam x) x
  simp only [Pi.add_apply] at h1
  linarith

/-- Marginal of the product Poisson law: `E[g(P_{i₀})]` computed on `ℕ^r`. -/
private lemma hasSum_poisProd_mul_coord {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (i₀ : Fin r) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (hsum : Summable fun k => poisPMF (lam i₀) k * g k) :
    HasSum (fun x : Fin r → ℕ => poisProd lam x * g (x i₀)) (poisExp (lam i₀) g) := by
  have H := hasSum_fin_pi_prod (fun i k => poisPMF (lam i) k * (if i = i₀ then g k else 1))
    (fun i k => mul_nonneg (poisPMF_nonneg (hlam i) k) (by split_ifs <;> simp [hg]))
    (fun i => if i = i₀ then poisExp (lam i₀) g else 1) (fun i => by
      by_cases hi : i = i₀
      · subst hi
        simpa [poisExp] using hsum.hasSum
      · simpa [hi] using hasSum_poisPMF (hlam i))
  convert H using 1
  · ext x
    rw [Finset.prod_mul_distrib, poisProd]
    congr 1
    rw [Fintype.prod_ite_eq' i₀ (fun i => g (x i))]
  · rw [Fintype.prod_ite_eq' i₀ (fun _ => poisExp (lam i₀) g)]

/-- Markov's inequality for a sum of single-coordinate functions under independent
Poisson laws. -/
theorem poisProb_le_of_sum {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (f : Fin r → ℕ → ℝ) (hf : ∀ i k, 0 ≤ f i k)
    (hsum : ∀ i, Summable fun k => poisPMF (lam i) k * f i k) {y : ℝ} (hy : 0 < y) :
    poisProb lam {x | y ≤ ∑ i, f i (x i)} ≤ (∑ i, poisExp (lam i) (f i)) / y := by
  have hS : HasSum (fun x => poisProd lam x * (∑ i, f i (x i)) / y)
      ((∑ i, poisExp (lam i) (f i)) / y) := by
    have := (hasSum_sum (s := Finset.univ) fun i _ =>
      hasSum_poisProd_mul_coord hlam i (f i) (hf i) (hsum i)).div_const y
    have hfun : (fun x => poisProd lam x * (∑ i, f i (x i)) / y) =
        fun x => (∑ i, poisProd lam x * f i (x i)) / y := by
      funext x
      rw [Finset.mul_sum]
    rw [hfun]
    exact this
  unfold poisProb
  refine hasSum_le (fun x => ?_) ((hasSum_poisProd hlam).summable.indicator _).hasSum hS
  by_cases hx : y ≤ ∑ i, f i (x i)
  · have hx' : x ∈ {x : Fin r → ℕ | y ≤ ∑ i, f i (x i)} := hx
    rw [Set.indicator_of_mem hx', le_div_iff₀ hy]
    exact mul_le_mul_of_nonneg_left hx (poisProd_nonneg hlam x)
  · have hx' : x ∉ {x : Fin r → ℕ | y ≤ ∑ i, f i (x i)} := hx
    rw [Set.indicator_of_notMem hx']
    exact div_nonneg (mul_nonneg (poisProd_nonneg hlam x)
      (Finset.sum_nonneg fun i _ => hf i (x i))) hy.le

/-- Pointwise convergence of mass functions on `ℕ^r` to a Poisson law bounds the limsup of
the probability of any set. -/
theorem eventually_sum_mem_le {r : ℕ} {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (w : ∀ n, Ω n → ℝ) (hw : ∀ᶠ n in atTop, ∀ ω, 0 ≤ w n ω)
    (htot : Tendsto (fun n => ∑ ω, w n ω) atTop (𝓝 1))
    (X : ∀ n, Ω n → Fin r → ℕ) {lam : Fin r → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (hconv : ∀ x, Tendsto (fun n => ∑ ω, if X n ω = x then w n ω else 0) atTop
      (𝓝 (poisProd lam x)))
    (B : Set (Fin r → ℕ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (∑ ω, if X n ω ∈ B then w n ω else 0) ≤ poisProb lam B + ε := by
  have hP := hasSum_poisProd hlam
  -- a finite set carrying all but `ε/3` of the Poisson mass
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin r → ℕ), 1 - ε / 3 < ∑ x ∈ F, poisProd lam x :=
    (hP.eventually (lt_mem_nhds (by linarith : 1 - ε / 3 < 1))).exists
  set G := F.filter (fun x => x ∉ B) with hG_def
  have hG : Tendsto (fun n => ∑ x ∈ G, ∑ ω, if X n ω = x then w n ω else 0) atTop
      (𝓝 (∑ x ∈ G, poisProd lam x)) :=
    tendsto_finsetSum G (fun x _ => hconv x)
  have h1 : ∀ᶠ n in atTop, ∑ x ∈ G, poisProd lam x - ε / 3 <
      ∑ x ∈ G, ∑ ω, if X n ω = x then w n ω else 0 :=
    hG.eventually (lt_mem_nhds (by linarith))
  have h2 : ∀ᶠ n in atTop, ∑ ω, w n ω < 1 + ε / 3 :=
    htot.eventually (gt_mem_nhds (by linarith))
  have h3 : ∑ x ∈ F.filter (· ∈ B), poisProd lam x ≤ poisProb lam B := by
    unfold poisProb
    calc ∑ x ∈ F.filter (· ∈ B), poisProd lam x
        = ∑ x ∈ F.filter (· ∈ B), B.indicator (poisProd lam) x := by
          refine Finset.sum_congr rfl fun x hx => ?_
          rw [Set.indicator_of_mem (Finset.mem_filter.mp hx).2]
      _ ≤ ∑' x, B.indicator (poisProd lam) x :=
          Summable.sum_le_tsum _
            (fun x _ => Set.indicator_nonneg (fun x _ => poisProd_nonneg hlam x) x)
            (hP.summable.indicator B)
  have h4 : ∑ x ∈ F, poisProd lam x =
      ∑ x ∈ F.filter (· ∈ B), poisProd lam x + ∑ x ∈ G, poisProd lam x :=
    (Finset.sum_filter_add_sum_filter_not F (· ∈ B) _).symm
  filter_upwards [hw, h1, h2] with n hwn h1n h2n
  have h5 : (∑ ω, if X n ω ∈ B then w n ω else 0) +
      ∑ x ∈ G, ∑ ω, (if X n ω = x then w n ω else 0) ≤ ∑ ω, w n ω := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [Finset.sum_ite_eq]
    by_cases hB : X n ω ∈ B
    · have hnG : X n ω ∉ G := by simp [hG_def, hB]
      simp [hB, hnG]
    · simp only [hB, if_false, zero_add]
      split_ifs
      · exact le_rfl
      · exact hwn ω
  linarith

end

end ERZeroFreeness
