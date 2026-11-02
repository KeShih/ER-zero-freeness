/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# A quantitative identity theorem on tubes

A function holomorphic on the open tube `U_{4ρ}(I_s)`, bounded by `1` on `L_{3ρ}(I_s)` and
vanishing to order `k` at `0` is uniformly small on `L_ρ(I_s)` once `k` is large, uniformly in
the function (`exists_norm_le_of_isBigO_pow`).  This replaces the compactness argument (Montel,
Prokhorov, identity theorem) in the proof of Theorem 3.1 (`lem:analytic-transfer`).

Proof (a chain of disks and Cauchy estimates).  Let `R = 3ρ` and pick points
`x_0 = 0, x_1, …, x_N = -s` of `I_s` with `|x_{j+1} - x_j| ≤ R/4`; every closed disk
`D(x_j, R)` lies in `L_R(I_s)`, and `L_ρ(I_s) ⊆ ⋃_j D(x_j, R/2)`.
Let `e_j = sup_{D(x_j, R/2)} |h|`.  The Taylor coefficients `c_i` of `h` at `x_j` satisfy
`|c_i| ≤ R^{-i}` (`DifferentiableOn.hasFPowerSeriesOnBall`, `norm_cauchyPowerSeries_le`).
* At `x_0 = 0`, `h = O(t^k)` forces `c_i = 0` for `i < k`
  (`HasFPowerSeriesAt.isBigO_sub_partialSum_pow`), so `e_0 ≤ ∑_{i≥k} 2^{-i} = 2^{1-k}`.
* Since `D(x_{j+1}, R/4) ⊆ D(x_j, R/2)`, the coefficients at `x_{j+1}` also satisfy
  `|c_i| ≤ e_j (R/4)^{-i}`; hence for every `J`,
  `e_{j+1} ≤ ∑_{i<J} e_j 2^i + ∑_{i≥J} 2^{-i} ≤ e_j 2^J + 2^{1-J}`.
So `e_N → 0` as `k → ∞` (uniformly in `h`), by induction on the finite chain.

The single-disk estimates are `vanishing_base` (the bound at `0`, via `vanishing_apply_eq_zero`)
and `vanishing_one_disk` (the step `e_j ↦ e_{j+1}`).  The chain is an induction on `j`: for
every `δ > 0` there is `k₀` such that `‖h‖ ≤ δ` on `D(x, 3ρ/2)` for all `x ∈ I_s` with
`-x ≤ j ρ/2`, all `k ≥ k₀` and all admissible `h`; the step from `j` to `j+1` uses the bound
at `x' = min (x + ρ/2) 0`, whose disk `D(x', 3ρ/2)` contains `D(x, 3ρ/4)`.  Finally
`L_ρ(I_s) ⊆ ⋃_{x ∈ I_s} D(x, 3ρ/2)`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Cauchy estimate: a bound `M` for `‖h‖` on the circle `|t - c| = r` bounds the coefficients
of the Cauchy power series of radius `r` by `M r⁻ⁿ`. -/
private lemma vanishing_norm_cauchyPowerSeries_le {h : ℂ → ℂ} {c : ℂ} {r M : ℝ} (hr : 0 < r)
    (hM : ∀ t ∈ Metric.sphere c r, ‖h t‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries h c r n‖ ≤ M * r⁻¹ ^ n := by
  refine (norm_cauchyPowerSeries_le h c r n).trans ?_
  rw [abs_of_pos hr]
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : ∫ θ in (0 : ℝ)..2 * Real.pi, ‖h (circleMap c r θ)‖ ≤ M * (2 * Real.pi) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
      (C := M) (f := fun θ => ‖h (circleMap c r θ)‖) (fun θ _ => by
        rw [norm_norm]; exact hM _ (circleMap_mem_sphere c hr.le θ))
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpi] at this
    exact (le_abs_self _).trans this
  have h2 : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖h (circleMap c r θ)‖ ≤ M := by
    calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖h (circleMap c r θ)‖
        ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) := by gcongr
      _ = M := by field_simp
  gcongr

/-- The Cauchy power series of `h` at `c` does not depend on the radius. -/
private lemma vanishing_cauchyPowerSeries_eq {h : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hd : DifferentiableOn ℂ h (Metric.closedBall c R)) :
    cauchyPowerSeries h c r = cauchyPowerSeries h c R := by
  have hR : 0 < R := hr.trans_le hrR
  lift r to NNReal using hr.le
  lift R to NNReal using hR.le
  have h1 := (hd.mono (Metric.closedBall_subset_closedBall hrR)).hasFPowerSeriesOnBall
    (by exact_mod_cast hr)
  have h2 := hd.hasFPowerSeriesOnBall (by exact_mod_cast hR)
  exact h1.hasFPowerSeriesAt.eq_formalMultilinearSeries h2.hasFPowerSeriesAt

private lemma vanishing_norm_apply (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (y : ℂ) :
    ‖p n (fun _ => y)‖ = ‖p n‖ * ‖y‖ ^ n := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, norm_smul, norm_pow,
    FormalMultilinearSeries.norm_apply_eq_norm_coef, mul_comm]

/-- Tail estimate: on the half disk, `h` differs from its `J`-th Taylor polynomial by at most
`2 M 2^{-J}`. -/
private lemma vanishing_tail_le {h : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (Metric.closedBall c R))
    (hM : ∀ t ∈ Metric.closedBall c R, ‖h t‖ ≤ M) (J : ℕ) {y : ℂ} (hy : ‖y‖ ≤ R / 2) :
    ‖h (c + y) - (cauchyPowerSeries h c R).partialSum J y‖ ≤ M * (1 / 2) ^ J * 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (Metric.mem_closedBall_self hR.le))
  have hyR : ‖y‖ < R := by linarith
  have hcoef : ∀ n, ‖cauchyPowerSeries h c R n‖ ≤ M * R⁻¹ ^ n :=
    vanishing_norm_cauchyPowerSeries_le hR fun t ht => hM t (Metric.sphere_subset_closedBall ht)
  lift R to NNReal using hR.le
  have hp := hd.hasFPowerSeriesOnBall (by exact_mod_cast hR)
  have hy' : y ∈ Metric.eball (0 : ℂ) R := by
    rw [mem_eball_zero_iff, enorm_lt_coe, ← NNReal.coe_lt_coe, coe_nnnorm]
    exact hyR
  have htail := (hasSum_nat_add_iff' J).mpr (hp.hasSum hy')
  have hg : HasSum (fun n : ℕ => M * (1 / 2) ^ J * (1 / 2) ^ n) (M * (1 / 2) ^ J * 2) :=
    hasSum_geometric_two.mul_left _
  refine htail.norm_le_of_bounded hg fun n => ?_
  rw [vanishing_norm_apply]
  calc ‖cauchyPowerSeries h c R (n + J)‖ * ‖y‖ ^ (n + J)
      ≤ M * (R : ℝ)⁻¹ ^ (n + J) * ((R : ℝ) / 2) ^ (n + J) := by
        gcongr
        exact hcoef _
    _ = M * ((R : ℝ)⁻¹ * ((R : ℝ) / 2)) ^ (n + J) := by rw [mul_pow, mul_assoc]
    _ = M * (1 / 2) ^ J * (1 / 2) ^ n := by
        have hR0 : (R : ℝ) ≠ 0 := hR.ne'
        rw [show (R : ℝ)⁻¹ * ((R : ℝ) / 2) = 1 / 2 by field_simp, pow_add, mul_assoc,
          mul_comm ((1 / 2 : ℝ) ^ n)]

/-- **One disk.** If `‖h‖ ≤ M` on `D(c,R)` and `‖h‖ ≤ e` on `D(c,R/4)`, then
`‖h‖ ≤ e 2^J + 2 M 2^{-J}` on `D(c,R/2)` for every `J`. -/
private lemma vanishing_one_disk {h : ℂ → ℂ} {c : ℂ} {R M e : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (Metric.closedBall c R))
    (hM : ∀ t ∈ Metric.closedBall c R, ‖h t‖ ≤ M)
    (he : ∀ t ∈ Metric.closedBall c (R / 4), ‖h t‖ ≤ e) (J : ℕ) :
    ∀ t ∈ Metric.closedBall c (R / 2), ‖h t‖ ≤ e * 2 ^ J + M * (1 / 2) ^ J * 2 := by
  intro t ht
  have hR4 : 0 < R / 4 := by positivity
  have he0 : 0 ≤ e := (norm_nonneg _).trans (he c (Metric.mem_closedBall_self hR4.le))
  set y := t - c with hy_def
  have hy : ‖y‖ ≤ R / 2 := by rwa [Metric.mem_closedBall, dist_eq_norm] at ht
  have htc : t = c + y := by rw [hy_def]; ring
  rw [htc]
  have htail := vanishing_tail_le hR hd hM J hy
  have heq : cauchyPowerSeries h c R = cauchyPowerSeries h c (R / 4) :=
    (vanishing_cauchyPowerSeries_eq hR4 (by linarith) hd).symm
  have hcoef : ∀ n, ‖cauchyPowerSeries h c (R / 4) n‖ ≤ e * (R / 4)⁻¹ ^ n :=
    vanishing_norm_cauchyPowerSeries_le hR4 fun t ht => he t (Metric.sphere_subset_closedBall ht)
  have geom : ∀ J : ℕ, ∑ i ∈ Finset.range J, (2 : ℝ) ^ i ≤ 2 ^ J := by
    intro J
    induction J with
    | zero => simp
    | succ J ih => rw [Finset.sum_range_succ, pow_succ]; linarith
  have hpart : ‖(cauchyPowerSeries h c R).partialSum J y‖ ≤ e * 2 ^ J := by
    rw [heq, FormalMultilinearSeries.partialSum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ Finset.range J, ‖cauchyPowerSeries h c (R / 4) i (fun _ => y)‖
        ≤ ∑ i ∈ Finset.range J, e * 2 ^ i := by
          gcongr with i hi
          rw [vanishing_norm_apply]
          calc ‖cauchyPowerSeries h c (R / 4) i‖ * ‖y‖ ^ i
              ≤ e * (R / 4)⁻¹ ^ i * (R / 2) ^ i := by
                gcongr
                exact hcoef i
            _ = e * ((R / 4)⁻¹ * (R / 2)) ^ i := by rw [mul_pow, mul_assoc]
            _ = e * 2 ^ i := by
                rw [show (R / 4)⁻¹ * (R / 2) = 2 by field_simp; norm_num]
      _ = e * ∑ i ∈ Finset.range J, (2 : ℝ) ^ i := by rw [Finset.mul_sum]
      _ ≤ e * 2 ^ J := by gcongr; exact geom J
  calc ‖h (c + y)‖ ≤ ‖(cauchyPowerSeries h c R).partialSum J y‖ +
        ‖h (c + y) - (cauchyPowerSeries h c R).partialSum J y‖ := norm_le_norm_add_norm_sub' _ _
    _ ≤ e * 2 ^ J + M * (1 / 2) ^ J * 2 := add_le_add hpart htail

/-- Vanishing to order `k` at `0` kills the first `k` Taylor coefficients. -/
private lemma vanishing_apply_eq_zero {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) {k : ℕ} (hk : f =O[𝓝 0] fun t => t ^ k) :
    ∀ n < k, ∀ y : ℂ, p n (fun _ => y) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have psum_eq : p.partialSum (n + 1) = fun y => p n fun _ => y := by
      funext z
      refine Finset.sum_eq_single _ (fun b hb hnb => ?_) fun hn => ?_
      · have := Finset.mem_range_succ_iff.mp hb
        exact ih b (this.lt_of_ne hnb) (by omega) z
      · exact False.elim (hn (Finset.mem_range.mpr (lt_add_one n)))
    have h1 := hp.isBigO_sub_partialSum_pow (n + 1)
    have h2 : (fun y : ℂ => f (0 + y)) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1) := by
      simp only [zero_add]
      refine hk.trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) one_pos] with t ht
      rw [mem_ball_zero_iff] at ht
      simp only [norm_pow, norm_norm, one_mul]
      exact pow_le_pow_of_le_one (norm_nonneg _) ht.le (by omega)
    have h3 := h2.sub h1
    simp only [sub_sub_cancel, psum_eq] at h3
    exact h3.continuousMultilinearMap_apply_eq_zero

/-- **Base disk.** If `‖h‖ ≤ 1` on `D(0,R)` and `h = O(t^k)` at `0`, then `‖h‖ ≤ 2^{1-k}` on
`D(0,R/2)`. -/
private lemma vanishing_base {h : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hd : DifferentiableOn ℂ h (Metric.closedBall 0 R))
    (hM : ∀ t ∈ Metric.closedBall (0 : ℂ) R, ‖h t‖ ≤ 1) {k : ℕ}
    (hk : h =O[𝓝 0] fun t => t ^ k) :
    ∀ t ∈ Metric.closedBall (0 : ℂ) (R / 2), ‖h t‖ ≤ (1 / 2) ^ k * 2 := by
  intro t ht
  have hp : HasFPowerSeriesAt h (cauchyPowerSeries h 0 R) 0 := by
    lift R to NNReal using hR.le
    exact (hd.hasFPowerSeriesOnBall (by exact_mod_cast hR)).hasFPowerSeriesAt
  have hzero := vanishing_apply_eq_zero hp hk
  have ht' : ‖t‖ ≤ R / 2 := by rwa [Metric.mem_closedBall, dist_zero_right] at ht
  have htail := vanishing_tail_le hR hd hM k ht'
  have hps : (cauchyPowerSeries h 0 R).partialSum k t = 0 :=
    Finset.sum_eq_zero fun i hi => hzero i (Finset.mem_range.mp hi) t
  rw [hps, sub_zero, zero_add, one_mul] at htail
  exact htail

/-- **Quantitative identity theorem.**  For every `ε > 0` there is `k` such that every `h`
holomorphic on `U_{4ρ}(I_s)`, bounded by `1` on `L_{3ρ}(I_s)` and with `h = O(t^{k'})` at `0`
for some `k' ≥ k`, satisfies `‖h‖ ≤ ε` on `L_ρ(I_s)`. -/
theorem exists_norm_le_of_isBigO_pow {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 0 < ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, ∀ k' ≥ k, ∀ h : ℂ → ℂ, DifferentiableOn ℂ h (openTube s (4 * ρ)) →
      (∀ t ∈ tube s (3 * ρ), ‖h t‖ ≤ 1) → (h =O[𝓝 0] fun t => t ^ k') →
        ∀ t ∈ tube s ρ, ‖h t‖ ≤ ε := by
  have hR : 0 < 3 * ρ := by positivity
  have hball_d : ∀ x : ℝ, x ∈ Set.Icc (-s) 0 →
      Metric.closedBall (x : ℂ) (3 * ρ) ⊆ openTube s (4 * ρ) := fun x hx t ht =>
    ⟨x, hx, by rw [Metric.mem_closedBall, dist_eq_norm] at ht; linarith⟩
  have hball_b : ∀ x : ℝ, x ∈ Set.Icc (-s) 0 →
      Metric.closedBall (x : ℂ) (3 * ρ) ⊆ tube s (3 * ρ) := fun x hx t ht =>
    ⟨x, hx, by rwa [Metric.mem_closedBall, dist_eq_norm] at ht⟩
  -- Induction along `I_s` in steps of `ρ/2`: smallness propagates from `0` to `-s`.
  have key : ∀ j : ℕ, ∀ δ > 0, ∃ k0 : ℕ, ∀ k ≥ k0, ∀ h : ℂ → ℂ,
      DifferentiableOn ℂ h (openTube s (4 * ρ)) → (∀ t ∈ tube s (3 * ρ), ‖h t‖ ≤ 1) →
      (h =O[𝓝 0] fun t => t ^ k) → ∀ x : ℝ, x ∈ Set.Icc (-s) 0 → -x ≤ j * (ρ / 2) →
      ∀ t ∈ Metric.closedBall (x : ℂ) (3 * ρ / 2), ‖h t‖ ≤ δ := by
    intro j
    induction j with
    | zero =>
      intro δ hδ
      obtain ⟨k0, hk0⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 2 by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      refine ⟨k0, fun k hk h hd hb hO x hx hxj t ht => ?_⟩
      have hx0 : x = 0 := by
        have := hx.2
        simp only [CharP.cast_eq_zero, zero_mul] at hxj
        linarith
      subst hx0
      rw [Complex.ofReal_zero] at ht
      have hd0 : DifferentiableOn ℂ h (Metric.closedBall 0 (3 * ρ)) :=
        hd.mono (by simpa using hball_d 0 hx)
      have hb0 : ∀ u ∈ Metric.closedBall (0 : ℂ) (3 * ρ), ‖h u‖ ≤ 1 := fun u hu =>
        hb u (by simpa using hball_b 0 hx (by simpa using hu))
      have hbase := vanishing_base hR hd0 hb0 hO t ht
      calc ‖h t‖ ≤ (1 / 2) ^ k * 2 := hbase
        _ ≤ (1 / 2) ^ k0 * 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk)
            (by norm_num)
        _ ≤ δ := by linarith
    | succ j ih =>
      intro δ hδ
      obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 4 by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      obtain ⟨k0, hk0⟩ := ih (δ / (2 * 2 ^ J)) (by positivity)
      refine ⟨k0, fun k hk h hd hb hO x hx hxj t ht => ?_⟩
      obtain ⟨x', hx', hx'j, hxx'⟩ : ∃ x' : ℝ, x' ∈ Set.Icc (-s) 0 ∧ -x' ≤ j * (ρ / 2) ∧
          |x - x'| ≤ ρ / 2 := by
        rcases le_total (x + ρ / 2) 0 with h1 | h1
        · refine ⟨x + ρ / 2, ⟨by linarith [hx.1], h1⟩, ?_, ?_⟩
          · push_cast at hxj; linarith
          · rw [show x - (x + ρ / 2) = -(ρ / 2) by ring, abs_neg, abs_of_pos (by positivity)]
        · refine ⟨0, ⟨by linarith, le_refl _⟩, ?_, ?_⟩
          · simp only [neg_zero]; positivity
          · rw [sub_zero, abs_le]; constructor <;> linarith [hx.2]
      have he : ∀ u ∈ Metric.closedBall (x : ℂ) (3 * ρ / 4), ‖h u‖ ≤ δ / (2 * 2 ^ J) := by
        intro u hu
        refine hk0 k hk h hd hb hO x' hx' hx'j u ?_
        rw [Metric.mem_closedBall] at hu ⊢
        calc dist u x' ≤ dist u x + dist (x : ℂ) x' := dist_triangle _ _ _
          _ ≤ 3 * ρ / 4 + ρ / 2 := by
            gcongr
            rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
            exact hxx'
          _ ≤ 3 * ρ / 2 := by linarith
      have hdisk := vanishing_one_disk hR (hd.mono (hball_d x hx))
        (fun u hu => hb u (hball_b x hx hu)) he J t ht
      calc ‖h t‖ ≤ δ / (2 * 2 ^ J) * 2 ^ J + 1 * (1 / 2) ^ J * 2 := hdisk
        _ ≤ δ := by
          have h2J : (0 : ℝ) < 2 ^ J := by positivity
          rw [show δ / (2 * 2 ^ J) * 2 ^ J = δ / 2 by field_simp]
          linarith
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * s / ρ)
  obtain ⟨k0, hk0⟩ := key N ε hε
  refine ⟨k0, fun k' hk' h hd hb hO t ht => ?_⟩
  obtain ⟨x, hx, htx⟩ := ht
  refine hk0 k' hk' h hd hb hO x hx ?_ t ?_
  · calc -x ≤ s := by linarith [hx.1]
      _ = 2 * s / ρ * (ρ / 2) := by field_simp
      _ ≤ N * (ρ / 2) := by gcongr
  · rw [Metric.mem_closedBall, dist_eq_norm]; linarith

end

end ERZeroFreeness
