/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.VBTransfer
import ERZeroFreeness.VBRelation
import ERZeroFreeness.IsingMain

/-! # `VBMain`: part of Theorem 1.5 (`thm:ising-applications`), zero-freeness

Proof plans for the statements of this module: `docs/ising-vb/blueprint.md`, section
"Module `VBMain`" (and Appendix A for proofs already checked).  Frozen statements carry their
blueprint item numbers in the comments. -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- A radius `R` with `a < R < 1` and `d R² < 1`, from `a < 1` and `d a² < 1` (continuity). -/
private theorem VBMain_exists_radius {d a : ℝ} (ha1 : a < 1) (hda : d * a ^ 2 < 1) :
    ∃ R : ℝ, a < R ∧ R < 1 ∧ d * R ^ 2 < 1 := by
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), a + δ < 1 :=
    ContinuousAt.eventually_lt (f := fun δ : ℝ => a + δ) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [add_zero]; exact ha1)
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), d * (a + δ) ^ 2 < 1 :=
    ContinuousAt.eventually_lt (f := fun δ : ℝ => d * (a + δ) ^ 2) (g := fun _ => (1 : ℝ))
      (by fun_prop) (by fun_prop) (by simp only [add_zero]; exact hda)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (e1.and e2)
  have hmem : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  obtain ⟨h1, h2⟩ := hδP hmem
  exact ⟨a + δ / 2, by linarith, h1, h2⟩

/-- `tanh β* ≥ 0` for `β* ≥ 0`. -/
private theorem VBMain_tanh_nonneg {βs : ℝ} (hβ : 0 ≤ βs) : 0 ≤ Real.tanh βs := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hβ) (Real.cosh_pos βs).le

/-- The uniform signs `boolSign b` are `±1`. -/
private theorem VBMain_boolSign {α : Type*} (J : α → Bool) (e : α) :
    boolSign (J e) = 1 ∨ boolSign (J e) = -1 := by
  cases J e <;> simp [boolSign]

/-- The pointwise inclusion: on the event of `vb_disk_zero_free` (radius `R`), both conjuncts of
the target event hold, given the conclusion of `vb_beta_nbhd` for `(β*, R)`. -/
private theorem VBMain_subset {n : ℕ} {βs R ρ : ℝ} (haR : Real.tanh βs < R)
    (hβnb : ∀ β : ℂ, (∃ x : ℝ, x ∈ Set.Icc (-βs) βs ∧ ‖β - x‖ ≤ ρ) →
      Complex.cosh β ≠ 0 ∧ ‖Complex.tanh β‖ ≤ R) :
    {GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool) | ∀ t : ℂ, ‖t‖ ≤ R →
        (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0} ⊆
      {GJ | (∀ t : ℂ, ‖t‖ ≤ Real.tanh βs →
            (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0) ∧
          ∀ β : ℂ, (∃ x : ℝ, x ∈ Set.Icc (-βs) βs ∧ ‖β - x‖ ≤ ρ) →
            vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β ≠ 0} := by
  intro GJ hGJ
  refine ⟨fun t ht => hGJ t (ht.trans haR.le), fun β hβ => ?_⟩
  obtain ⟨hc, ht⟩ := hβnb β hβ
  rw [vbZ_eq GJ.1 (fun e => boolSign (GJ.2 e)) (fun e _ => VBMain_boolSign GJ.2 e) hc]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ two_ne_zero) (pow_ne_zero _ hc)) (hGJ _ ht)

-- [VZ1] **Theorem 1.5 (ii)** (`thm:ising-applications`, Viana–Bray diluted spin glass).
theorem viana_bray_zero_free {d : ℝ} (hd : 0 < d) {βs : ℝ} (hβ : 0 < βs)
    (hdβ : d * Real.tanh βs ^ 2 < 1) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => sgProb n (d / n)
        {GJ | (∀ t : ℂ, ‖t‖ ≤ Real.tanh βs →
            (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0) ∧
          ∀ β : ℂ, (∃ x : ℝ, x ∈ Set.Icc (-βs) βs ∧ ‖β - x‖ ≤ ρ) →
            vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β ≠ 0})
      atTop (𝓝 1) := by
  -- a radius `R ∈ (tanh β*, r_d)`
  obtain ⟨R, haR, hR1, hdR⟩ := VBMain_exists_radius (Real.tanh_lt_one βs) hdβ
  have hR0 : 0 ≤ R := (VBMain_tanh_nonneg hβ.le).trans haR.le
  -- `t`-plane zero-freeness on the closed disk of radius `R` (VX3)
  have hlim := vb_disk_zero_free hd hR0 hR1 hdR
  -- the `β`-neighbourhood of `[-β*, β*]` on which `cosh β ≠ 0` and `|tanh β| ≤ R` (VR3)
  obtain ⟨ρ, hρ, hβnb⟩ := vb_beta_nbhd haR
  refine ⟨ρ, hρ, ?_⟩
  -- for `n ≥ d` the edge probability `d/n` lies in `[0,1]`
  have hn0 : ∀ᶠ n : ℕ in atTop, d ≤ n := by
    filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    exact (Nat.le_ceil d).trans (by exact_mod_cast hn)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [hn0] with n hn
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    exact sgProb_mono hp0 hp1 (VBMain_subset haR hβnb)
  · filter_upwards [hn0] with n hn
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    exact sgProb_le_one hp0 hp1 _

-- [VZ2] **Theorem 1.5** (`thm:ising-applications`), both zero-freeness assertions.
theorem ising_applications_zero_free {d : ℝ} (hd : 0 < d) :
    (∀ xs : ℝ, 0 < xs → xs < 1 → d * ((1 - xs) / (1 + xs)) ^ 2 < 1 →
      ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
          {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc xs 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G 2 z ≠ 0})
        atTop (𝓝 1)) ∧
    (∀ βs : ℝ, 0 < βs → d * Real.tanh βs ^ 2 < 1 →
      ∃ ρ > 0, Tendsto (fun n : ℕ => sgProb n (d / n)
          {GJ | (∀ t : ℂ, ‖t‖ ≤ Real.tanh βs →
              (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0) ∧
            ∀ β : ℂ, (∃ x : ℝ, x ∈ Set.Icc (-βs) βs ∧ ‖β - x‖ ≤ ρ) →
              vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β ≠ 0})
        atTop (𝓝 1)) :=
  ⟨fun _ hx0 hx1 hdx => ising_af_zero_free hd hx0 hx1 hdx,
    fun _ hβ hdβ => viana_bray_zero_free hd hβ hdβ⟩

end

end ERZeroFreeness
