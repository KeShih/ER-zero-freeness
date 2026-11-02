/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.VBSecondMoment
import ERZeroFreeness.VBTaylor
import ERZeroFreeness.VBCycleMoments
import ERZeroFreeness.VBCycleModel
import ERZeroFreeness.VBDisk
import ERZeroFreeness.DenseSubgraph

/-! # `VBTransfer`: part of Theorem 1.5 (`thm:ising-applications`), zero-freeness

Proof plans for the statements of this module: `docs/ising-vb/blueprint.md`, section
"Module `VBTransfer`" (and Appendix A for proofs already checked).  Frozen statements carry their
blueprint item numbers in the comments.

Structure of the proof of `vb_disk_zero_free` (the argument of `zero_free_of_first_moment`, on
disks).  Fix `R₀ < R < R₁ < 1` with `d R₁² < 1` (`VBTransfer_exists_radii`).  `vb_sup_bound`
gives `C`, and `sgCyclePoly_bounds` (radius `R`) gives `σ` and `E = ∑' i, E σ_i(P_i)`.  Given
`η > 0`, put `Y = 2E/η + 1`, `M = max 1 (C/η) e^Y`, `ε = e^{-Y}/(2M)` and take `k` from
`disk_norm_le_of_isBigO_pow`.  The bad event is contained in
`Dense(2(k+2)) ∪ {∃ |t| ≤ R, M < |𝓘(t)|} ∪ {X_k ∈ 𝔅}` (`VBTransfer_subset`), where
`𝔅 = VBTransfer_badSet R₀ R M k ⊆ {Y ≤ Σ}` (`VBTransfer_badSet_subset`) has Poisson
probability `≤ 2E/Y ≤ η` (`VBTransfer_poisProb_le`). -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

-- [VX1]
theorem tendsto_sgProb_hasDenseSubgraph {d : ℝ} (hd : 0 < d) (b : ℕ) :
    Tendsto (fun n : ℕ => sgProb n (d / n) {GJ | HasDenseSubgraph GJ.1 b}) atTop (𝓝 0) := by
  have h : ∀ n : ℕ, sgProb n (d / n) {GJ | HasDenseSubgraph GJ.1 b} =
      erProb n (d / n) {G | HasDenseSubgraph G b} := fun n =>
    sgProb_fst n (d / n) {G | HasDenseSubgraph G b}
  exact (tendsto_erProb_hasDenseSubgraph hd b).congr fun n => (h n).symm

-- [VX2] `lem:holomorphic-tightness` as used: `P[sup_{|t| ≤ R} |I_n| > M] ≤ C/M`.
theorem vb_sup_bound {d : ℝ} (hd : 0 < d) {R R₁ : ℝ} (hR : 0 ≤ R) (hRR : R < R₁)
    (hdR : d * R₁ ^ 2 < 1) :
    ∃ C : ℝ, ∀ M : ℝ, 0 < M → ∀ n : ℕ, d ≤ n →
      sgProb n (d / n) {GJ | ∃ t : ℂ, ‖t‖ ≤ R ∧
        M < ‖(signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t‖} ≤ C / M := by
  obtain ⟨B, hB⟩ := vb_first_moment hd hdR
  refine ⟨R₁ / (R₁ - R) * B, fun M hM n hn => ?_⟩
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  have hmom : ∀ t : ℂ, ‖t‖ = R₁ →
      ∑ GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool), sgWeight n (d / n) GJ.1 GJ.2 *
        ‖(signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t‖ ≤ B := by
    intro t ht
    have h1 := hB n hn t ht.le
    rw [sgExp_eq_sum] at h1
    exact h1
  have key := sum_exists_norm_gt_le (Ω := SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))
    (fun GJ => sgWeight n (d / n) GJ.1 GJ.2) (fun GJ => sgWeight_nonneg hp0 hp1 GJ.1 GJ.2)
    (fun GJ => signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))) hR hRR hmom hM
  rw [sgProb_eq_sum]
  exact key

/-! ### Helpers for `vb_disk_zero_free` -/

/-- Intermediate radii `R₀ < R < R₁ < 1` with `d R₁² < 1`. -/
private theorem VBTransfer_exists_radii {d R₀ : ℝ} (hR₁ : R₀ < 1) (hdR : d * R₀ ^ 2 < 1) :
    ∃ R R₁ : ℝ, R₀ < R ∧ R < R₁ ∧ R₁ < 1 ∧ d * R₁ ^ 2 < 1 := by
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), R₀ + δ < 1 :=
    ContinuousAt.eventually_lt (f := fun δ : ℝ => R₀ + δ) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [add_zero]; exact hR₁)
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), d * (R₀ + δ) ^ 2 < 1 :=
    ContinuousAt.eventually_lt (f := fun δ : ℝ => d * (R₀ + δ) ^ 2) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [add_zero]; exact hdR)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  have hmem : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  obtain ⟨h1, h2⟩ := hδP hmem
  exact ⟨R₀ + δ / 4, R₀ + δ / 2, by linarith, by linarith, h1, h2⟩

/-- A copy of the private `TransferAux.tendsto_zero_of_eventually_le`. -/
private theorem VBTransfer_tendsto_zero_of_eventually_le {f : ℕ → ℝ}
    (h0 : ∀ᶠ n in atTop, 0 ≤ f n) (h : ∀ η > 0, ∀ᶠ n in atTop, f n ≤ 4 * η) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => h0.mono fun n hn => ha.trans_le hn, fun a ha => ?_⟩
  filter_upwards [h (a / 8) (by positivity)] with n hn
  linarith

/-- The set `𝔅` of signed cycle-count vectors `x` for which some holomorphic `g` on the open disk
`D(0,R)`, bounded by `M` there and vanishing somewhere on `|t| ≤ R₀`, agrees with
`Q^{sg}_{k+2}(·;x)` to order `k + 2` at `0`. -/
private def VBTransfer_badSet (R₀ R M : ℝ) (k : ℕ) : Set (Fin (k + k) → ℕ) :=
  {x | ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (Metric.ball 0 R) ∧
    (∀ t ∈ Metric.ball (0 : ℂ) R, ‖g t‖ ≤ M) ∧ (∃ t : ℂ, ‖t‖ ≤ R₀ ∧ g t = 0) ∧
    (fun t => g t - (sgCyclePoly k x).eval t) =O[𝓝 0] fun t => t ^ (k + 3)}

/-- If `Σ(x) < Y`, then `Q^{sg}` is bounded by `M` on `D(0,R)` and bounded below by
`e^{-Σ} > e^{-Y} = 2Mε` on `|t| ≤ R₀`, so no `g` as in `𝔅` exists (quantitative identity theorem
applied to `(g - Q^{sg})/(2M)`). -/
private theorem VBTransfer_badSet_subset {R₀ R M Y : ℝ} (hR₀R : R₀ ≤ R) (hM : 0 < M)
    (hYM : Real.exp Y ≤ M) {σ : ℕ → ℕ → ℝ}
    (hW : ∀ (r : ℕ) (x : Fin (r + r) → ℕ) (t : ℂ), ‖t‖ ≤ R →
        Real.exp (-∑ i : Fin r, (σ i (x (Fin.castAdd r i)) + σ i (x (Fin.natAdd r i)))) ≤
            ‖(sgCyclePoly r x).eval t‖ ∧
          ‖(sgCyclePoly r x).eval t‖ ≤
            Real.exp (∑ i : Fin r, (σ i (x (Fin.castAdd r i)) + σ i (x (Fin.natAdd r i)))))
    {k : ℕ} (hk : ∀ k' ≥ k, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.ball 0 R) →
      (∀ t ∈ Metric.ball (0 : ℂ) R, ‖h t‖ ≤ 1) → (h =O[𝓝 0] fun t => t ^ k') →
        ∀ t : ℂ, ‖t‖ ≤ R₀ → ‖h t‖ ≤ Real.exp (-Y) / (2 * M)) :
    VBTransfer_badSet R₀ R M k ⊆
      {x | Y ≤ ∑ i : Fin k, (σ i (x (Fin.castAdd k i)) + σ i (x (Fin.natAdd k i)))} := by
  rintro x ⟨g, hgd, hgM, ⟨t₀, ht₀, hgt₀⟩, hgO⟩
  by_contra hlt'
  have hlt : ∑ i : Fin k, (σ i (x (Fin.castAdd k i)) + σ i (x (Fin.natAdd k i))) < Y :=
    lt_of_not_ge hlt'
  have h2M : (0 : ℝ) < 2 * M := by positivity
  have hWL : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖(sgCyclePoly k x).eval t‖ ≤ M := by
    intro t ht
    have htR : ‖t‖ ≤ R := (mem_ball_zero_iff.1 ht).le
    calc ‖(sgCyclePoly k x).eval t‖
        ≤ Real.exp (∑ i : Fin k, (σ i (x (Fin.castAdd k i)) + σ i (x (Fin.natAdd k i)))) :=
          (hW k x t htR).2
      _ ≤ Real.exp Y := Real.exp_le_exp.2 hlt.le
      _ ≤ M := hYM
  obtain ⟨h, hh⟩ : ∃ h : ℂ → ℂ,
      h = fun t => ((2 * M : ℝ) : ℂ)⁻¹ * (g t - (sgCyclePoly k x).eval t) := ⟨_, rfl⟩
  have hhd : DifferentiableOn ℂ h (Metric.ball 0 R) := by
    rw [hh]
    exact (hgd.sub (sgCyclePoly k x).differentiableOn).const_mul _
  have hnorm : ∀ t, ‖h t‖ = (2 * M)⁻¹ * ‖g t - (sgCyclePoly k x).eval t‖ := by
    intro t
    rw [hh, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2M]
  have hhb : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖h t‖ ≤ 1 := by
    intro t ht
    rw [hnorm, inv_mul_le_iff₀ h2M]
    calc ‖g t - (sgCyclePoly k x).eval t‖ ≤ ‖g t‖ + ‖(sgCyclePoly k x).eval t‖ :=
          norm_sub_le _ _
      _ ≤ M + M := add_le_add (hgM t ht) (hWL t ht)
      _ = 2 * M * 1 := by ring
  have hhO : h =O[𝓝 0] fun t => t ^ (k + 3) := by
    rw [hh]
    exact hgO.const_mul_left _
  have hsmall := hk (k + 3) (by omega) h hhd hhb hhO t₀ ht₀
  rw [hnorm, hgt₀, zero_sub, norm_neg, inv_mul_le_iff₀ h2M, mul_div_cancel₀ _ h2M.ne']
    at hsmall
  have hlow := (hW k x t₀ (ht₀.trans hR₀R)).1
  have hlt2 : Real.exp (-Y) <
      Real.exp (-∑ i : Fin k, (σ i (x (Fin.castAdd k i)) + σ i (x (Fin.natAdd k i)))) :=
    Real.exp_lt_exp.2 (by linarith)
  linarith

/-- The Poisson means `sgCycleMeans d k` are nonnegative. -/
private theorem VBTransfer_sgCycleMeans_nonneg {d : ℝ} (hd : 0 < d) (k : ℕ)
    (j : Fin (k + k)) : 0 ≤ sgCycleMeans d k j := by
  induction j using Fin.addCases with
  | left i =>
    rw [sgCycleMeans, Fin.append_left]
    unfold cycleMean
    positivity
  | right i =>
    rw [sgCycleMeans, Fin.append_right]
    unfold cycleMean
    positivity

/-- Markov's inequality for `Σ = ∑_i (σ_i(x^+_i) + σ_i(x^-_i))` under the limiting Poisson law:
`P[Y ≤ Σ] ≤ 2E/Y`. -/
private theorem VBTransfer_poisProb_le {d : ℝ} (hd : 0 < d) {σ : ℕ → ℕ → ℝ}
    (hσ0 : ∀ i k, 0 ≤ σ i k)
    (hσsum : ∀ i, Summable fun k => poisPMF (cycleMean d i / 2) k * σ i k)
    (hEsum : Summable fun i => poisExp (cycleMean d i / 2) (σ i))
    (k : ℕ) {B : Set (Fin (k + k) → ℕ)} {Y : ℝ} (hY : 0 < Y)
    (hB : B ⊆ {x | Y ≤ ∑ i : Fin k, (σ i (x (Fin.castAdd k i)) + σ i (x (Fin.natAdd k i)))}) :
    poisProb (sgCycleMeans d k) B ≤ 2 * (∑' i, poisExp (cycleMean d i / 2) (σ i)) / Y := by
  set f : Fin (k + k) → ℕ → ℝ := Fin.append (fun i : Fin k => σ i) (fun i : Fin k => σ i)
    with hf
  have hlam := VBTransfer_sgCycleMeans_nonneg hd k
  have hf0 : ∀ j m, 0 ≤ f j m := by
    intro j m
    induction j using Fin.addCases with
    | left i => rw [hf, Fin.append_left]; exact hσ0 _ _
    | right i => rw [hf, Fin.append_right]; exact hσ0 _ _
  have hfsum : ∀ j, Summable fun m => poisPMF (sgCycleMeans d k j) m * f j m := by
    intro j
    induction j using Fin.addCases with
    | left i =>
      rw [hf, Fin.append_left, sgCycleMeans, Fin.append_left]
      exact hσsum _
    | right i =>
      rw [hf, Fin.append_right, sgCycleMeans, Fin.append_right]
      exact hσsum _
  have hsumeq : ∀ x : Fin (k + k) → ℕ, ∑ j, f j (x j) =
      ∑ i : Fin k, (σ i (x (Fin.castAdd k i)) + σ i (x (Fin.natAdd k i))) := by
    intro x
    rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, Fin.append_left, Fin.append_right]
  have hexpeq : ∑ j, poisExp (sgCycleMeans d k j) (f j) =
      2 * ∑ i : Fin k, poisExp (cycleMean d i / 2) (σ i) := by
    rw [Fin.sum_univ_add, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, Fin.append_left, Fin.append_right, sgCycleMeans, Fin.append_left, Fin.append_right]
    ring
  have hpe : ∀ i, 0 ≤ poisExp (cycleMean d i / 2) (σ i) := fun i =>
    tsum_nonneg fun j =>
      mul_nonneg (poisPMF_nonneg (by unfold cycleMean; positivity) j) (hσ0 i j)
  have hfin : ∑ i : Fin k, poisExp (cycleMean d i / 2) (σ i) ≤
      ∑' i, poisExp (cycleMean d i / 2) (σ i) :=
    (Fin.sum_univ_eq_sum_range (fun i => poisExp (cycleMean d i / 2) (σ i)) k).le.trans
      (hEsum.sum_le_tsum _ fun i _ => hpe i)
  calc poisProb (sgCycleMeans d k) B
      ≤ poisProb (sgCycleMeans d k) {x | Y ≤ ∑ j, f j (x j)} := by
        refine poisProb_mono hlam fun x hx => ?_
        show Y ≤ ∑ j, f j (x j)
        rw [hsumeq]
        exact hB hx
    _ ≤ (∑ j, poisExp (sgCycleMeans d k j) (f j)) / Y :=
        poisProb_le_of_sum hlam f hf0 hfsum hY
    _ = 2 * (∑ i : Fin k, poisExp (cycleMean d i / 2) (σ i)) / Y := by rw [hexpeq]
    _ ≤ 2 * (∑' i, poisExp (cycleMean d i / 2) (σ i)) / Y := by
        gcongr

/-- Off the dense event and the large-supremum event, a zero of `𝓘_{G,J}` on `|t| ≤ R₀` makes
`𝓘_{G,J}` itself a witness for `X_k(G,J) ∈ 𝔅`. -/
private theorem VBTransfer_subset {n : ℕ} (R₀ R M : ℝ) (k : ℕ) :
    {GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool) | ∃ t : ℂ, ‖t‖ ≤ R₀ ∧
        (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t = 0} ⊆
      ({GJ | HasDenseSubgraph GJ.1 (2 * (k + 2))} ∪
        {GJ | ∃ t : ℂ, ‖t‖ ≤ R ∧
          M < ‖(signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t‖}) ∪
        {GJ | sgCycleCounts k GJ.1 GJ.2 ∈ VBTransfer_badSet R₀ R M k} := by
  rintro GJ ⟨t₀, ht₀, hz⟩
  by_cases hD : HasDenseSubgraph GJ.1 (2 * (k + 2))
  · exact Or.inl (Or.inl hD)
  by_cases hS : ∃ t : ℂ, ‖t‖ ≤ R ∧
      M < ‖(signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t‖
  · exact Or.inl (Or.inr hS)
  refine Or.inr ⟨fun t => (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t,
    (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).differentiableOn, ?_, ⟨t₀, ht₀, hz⟩,
    signedPoly_sub_sgCyclePoly_isBigO k GJ.1 GJ.2 hD⟩
  intro t ht
  by_contra hlt
  exact hS ⟨t, (mem_ball_zero_iff.1 ht).le, lt_of_not_ge hlt⟩

/-- Union bound for three events. -/
private theorem VBTransfer_union3_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B C D : Set (SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))} (h : A ⊆ (B ∪ C) ∪ D) :
    sgProb n p A ≤ sgProb n p B + sgProb n p C + sgProb n p D := by
  calc sgProb n p A ≤ sgProb n p ((B ∪ C) ∪ D) := sgProb_mono hp0 hp1 h
    _ ≤ sgProb n p (B ∪ C) + sgProb n p D := sgProb_union_le hp0 hp1 _ _
    _ ≤ sgProb n p B + sgProb n p C + sgProb n p D := by
        linarith [sgProb_union_le hp0 hp1 B C]

-- [VX3] `t`-plane zero-freeness of `𝓘_{G_n,J}` on every closed disk of radius `< r_d`.
theorem vb_disk_zero_free {d : ℝ} (hd : 0 < d) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hR₁ : R₀ < 1)
    (hdR : d * R₀ ^ 2 < 1) :
    Tendsto (fun n : ℕ => sgProb n (d / n)
        {GJ | ∀ t : ℂ, ‖t‖ ≤ R₀ → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0})
      atTop (𝓝 1) := by
  obtain ⟨R, R₁, hR₀R, hRR₁, hR₁1, hdR₁⟩ := VBTransfer_exists_radii hR₁ hdR
  have hR0 : 0 ≤ R := by linarith
  have hR1 : R < 1 := by linarith
  have hdR' : d * R ^ 2 < 1 := by
    have : R ^ 2 ≤ R₁ ^ 2 := pow_le_pow_left₀ hR0 hRR₁.le 2
    nlinarith
  obtain ⟨C, hC⟩ := vb_sup_bound hd hR0 hRR₁ hdR₁
  obtain ⟨σ, hσ0, hσsum, hEsum, hW⟩ := sgCyclePoly_bounds hd hR0 hR1 hdR'
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = ∑' i, poisExp (cycleMean d i / 2) (σ i) := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hE]
    exact tsum_nonneg fun i => tsum_nonneg fun j =>
      mul_nonneg (poisPMF_nonneg (by unfold cycleMean; positivity) j) (hσ0 i j)
  have hn0 : ∀ᶠ n : ℕ in atTop, d ≤ n := by
    filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    exact (Nat.le_ceil d).trans (by exact_mod_cast hn)
  -- the bad event has probability tending to `0`
  have hbad : Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∃ t : ℂ, ‖t‖ ≤ R₀ ∧ (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t = 0})
      atTop (𝓝 0) := by
    refine VBTransfer_tendsto_zero_of_eventually_le ?_ ?_
    · filter_upwards [hn0] with n hn
      obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
      exact sgProb_nonneg hp0 hp1 _
    intro η hη
    -- the parameters `Y`, `M`, `ε`, `k`
    obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = 2 * E / η + 1 := ⟨_, rfl⟩
    have hY0 : 0 < Y := by
      have := div_nonneg (mul_nonneg zero_le_two hE0) hη.le
      rw [hY]
      linarith
    have hEY : 2 * E / Y ≤ η := by
      rw [div_le_iff₀ hY0, hY, mul_add, mul_div_cancel₀ _ hη.ne', mul_one]
      linarith
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = max 1 (max (C / η) (Real.exp Y)) := ⟨_, rfl⟩
    have hM0 : 0 < M := by
      rw [hM]
      exact lt_of_lt_of_le one_pos (le_max_left _ _)
    have hCM : C / M ≤ η := by
      rw [div_le_iff₀ hM0]
      have h1 : C / η ≤ M := by
        rw [hM]
        exact (le_max_left _ _).trans (le_max_right _ _)
      calc C = η * (C / η) := (mul_div_cancel₀ _ hη.ne').symm
        _ ≤ η * M := mul_le_mul_of_nonneg_left h1 hη.le
    have hYM : Real.exp Y ≤ M := by
      rw [hM]
      exact (le_max_right _ _).trans (le_max_right _ _)
    have hε : 0 < Real.exp (-Y) / (2 * M) := by positivity
    obtain ⟨k, hk⟩ := disk_norm_le_of_isBigO_pow hR₀ hR₀R hε
    have h𝔅 := VBTransfer_badSet_subset hR₀R.le hM0 hYM hW hk
    have hpois : poisProb (sgCycleMeans d k) (VBTransfer_badSet R₀ R M k) ≤ η := by
      have := VBTransfer_poisProb_le hd hσ0 hσsum hEsum k hY0 h𝔅
      rw [← hE] at this
      exact this.trans hEY
    have hA1 := (tendsto_order.1 (tendsto_sgProb_hasDenseSubgraph hd (2 * (k + 2)))).2 η hη
    have hA3 := eventually_sgProb_sgCycleCounts_mem_le hd k (VBTransfer_badSet R₀ R M k) hη
    filter_upwards [hA1, hA3, hn0] with n h1 h3 hn
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    have h2 := hC M hM0 n hn
    have hU := VBTransfer_union3_le hp0 hp1 (VBTransfer_subset (n := n) R₀ R M k)
    linarith
  -- pass to the complement
  have hcompl : ∀ n : ℕ, sgProb n (d / n)
      {GJ | ∀ t : ℂ, ‖t‖ ≤ R₀ → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0} =
      1 - sgProb n (d / n)
        {GJ | ∃ t : ℂ, ‖t‖ ≤ R₀ ∧
          (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t = 0} := by
    intro n
    rw [← sgProb_compl]
    congr 1
    ext GJ
    constructor
    · rintro hG ⟨t, ht, hz⟩
      exact hG t ht hz
    · intro hG t ht hz
      exact hG ⟨t, ht, hz⟩
  have hlim := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  rw [sub_zero] at hlim
  exact hlim.congr fun n => (hcompl n).symm

end

end ERZeroFreeness
