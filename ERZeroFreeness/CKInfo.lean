/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Lemmas 1.5–1.7 (entropy, mutual information, decorrelation)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`.

A law on `[q]^n` is a function `μ : (Fin n → Fin q) → ℝ` with `IsPMF μ`.  Entropies are written
with cylinder masses: `h_μ(S) = ckH μ S = -∑_τ μ(τ) log μ(τ'_S = τ_S)`, and
`I(τ_A; τ_B | τ_S) = ckMI μ A B S`.

* Lemma 1.5 (finite entropy calculus): (E1) `ck_H_nonneg`, `ck_H_empty`, `ck_H_le`;
  (E2) `ck_H_cond_avg`, `ck_MI_cond_avg`; (E3) `ck_H_mono`, `ck_H_submod`, `ck_MI_nonneg`;
  (E5) `ck_MI_mono`; and `ck_MI_single_le`.
* Lemma 1.6 (`∑ |p - p'| ≤ 2 √D(p ‖ p')`): the private `CKInfoB_L1_le_KL`.
* Lemma 1.7 (decorrelation): `ck_cov_le` (a), `ck_prod_decorr` (b) and `ck_pair_decorr` (c).
* `ck_marg_mem`, `ck_cond_isPMF`: marginals and conditional laws are probability vectors.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### Cylinder masses; Lemma 1.5 (finite entropy calculus) -/

private lemma CKInfoA_agree_refl {n q : ℕ} (S : Finset (Fin n)) (τ : Fin n → Fin q) :
    ckAgree S τ τ := fun _ _ => rfl

private lemma CKInfoA_agree_symm {n q : ℕ} {S : Finset (Fin n)} {σ τ : Fin n → Fin q}
    (h : ckAgree S σ τ) : ckAgree S τ σ := fun v hv => (h v hv).symm

private lemma CKInfoA_agree_trans {n q : ℕ} {S : Finset (Fin n)} {ρ σ τ : Fin n → Fin q}
    (h₁ : ckAgree S ρ σ) (h₂ : ckAgree S σ τ) : ckAgree S ρ τ :=
  fun v hv => (h₂ v hv).trans (h₁ v hv)

private lemma CKInfoA_agree_mono {n q : ℕ} {S T : Finset (Fin n)} (h : S ⊆ T)
    {σ τ : Fin n → Fin q} (hT : ckAgree T σ τ) : ckAgree S σ τ := fun v hv => hT v (h hv)

private lemma CKInfoA_cyl_eq_sum_ite {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S : Finset (Fin n))
    (τ : Fin n → Fin q) : ckCyl μ S τ = ∑ σ, if ckAgree S τ σ then μ σ else 0 := by
  rw [ckCyl, Finset.sum_filter]

private lemma CKInfoA_cyl_nonneg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) (τ : Fin n → Fin q) : 0 ≤ ckCyl μ S τ :=
  Finset.sum_nonneg fun σ _ => hμ.1 σ

private lemma CKInfoA_cyl_le_one {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) (τ : Fin n → Fin q) : ckCyl μ S τ ≤ 1 := by
  calc ckCyl μ S τ ≤ ∑ σ, μ σ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun σ _ _ => hμ.1 σ)
    _ = 1 := hμ.2

private lemma CKInfoA_self_le_cyl {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) (τ : Fin n → Fin q) : μ τ ≤ ckCyl μ S τ := by
  rw [ckCyl]
  exact Finset.single_le_sum (f := μ) (fun σ _ => hμ.1 σ)
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, CKInfoA_agree_refl S τ⟩)

private lemma CKInfoA_cyl_pos {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) {τ : Fin n → Fin q} (hτ : 0 < μ τ) : 0 < ckCyl μ S τ :=
  hτ.trans_le (CKInfoA_self_le_cyl hμ S τ)

private lemma CKInfoA_cyl_congr {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) {S : Finset (Fin n)}
    {σ τ : Fin n → Fin q} (h : ckAgree S σ τ) : ckCyl μ S σ = ckCyl μ S τ := by
  rw [ckCyl, ckCyl]
  refine Finset.sum_congr (Finset.filter_congr fun ρ _ => ?_) fun _ _ => rfl
  exact ⟨fun h' => CKInfoA_agree_trans (CKInfoA_agree_symm h) h',
    fun h' => CKInfoA_agree_trans h h'⟩

private lemma CKInfoA_cyl_anti {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    {S T : Finset (Fin n)} (h : S ⊆ T) (τ : Fin n → Fin q) : ckCyl μ T τ ≤ ckCyl μ S τ := by
  rw [ckCyl, ckCyl]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun σ hσ => ?_) (fun σ _ _ => hμ.1 σ)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  exact CKInfoA_agree_mono h hσ

private lemma CKInfoA_cyl_empty {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (τ : Fin n → Fin q) : ckCyl μ ∅ τ = 1 := by
  rw [ckCyl, Finset.filter_true_of_mem fun σ _ v hv => absurd hv (Finset.notMem_empty v)]
  exact hμ.2

/-- A set of configurations that pairwise agree on `U` lies in one `U`-class, so the
conditional masses `μ(τ)/μ(τ'_U = τ_U)` over it sum to at most `1`. -/
private lemma CKInfoA_finset_class_sum_le_one {n q : ℕ} {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) (U : Finset (Fin n)) (s : Finset (Fin n → Fin q))
    (hs : ∀ τ ∈ s, ∀ τ' ∈ s, ckAgree U τ τ') : ∑ τ ∈ s, μ τ / ckCyl μ U τ ≤ 1 := by
  rcases s.eq_empty_or_nonempty with hs0 | ⟨τ₀, hτ₀⟩
  · simp [hs0]
  · have hc : ∑ τ ∈ s, μ τ / ckCyl μ U τ = ∑ τ ∈ s, μ τ / ckCyl μ U τ₀ :=
      Finset.sum_congr rfl fun τ hτ => by rw [CKInfoA_cyl_congr μ (hs τ₀ hτ₀ τ hτ)]
    have hsub : ∑ τ ∈ s, μ τ ≤ ckCyl μ U τ₀ := by
      rw [ckCyl]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun τ hτ => ?_) (fun τ _ _ => hμ.1 τ)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hs τ₀ hτ₀ τ hτ⟩
    rw [hc, ← Finset.sum_div]
    exact (div_le_div_of_nonneg_right hsub (CKInfoA_cyl_nonneg hμ U τ₀)).trans
      (div_self_le_one _)

/-- `∑_τ μ(τ)/μ(τ'_S = τ_S)` counts the `S`-classes of positive mass, hence is at most
`q^{|S|}`. -/
private lemma CKInfoA_sum_div_cyl_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) : ∑ τ, μ τ / ckCyl μ S τ ≤ (q : ℝ) ^ S.card := by
  calc ∑ τ, μ τ / ckCyl μ S τ
      = ∑ ξ : (S → Fin q), ∑ τ ∈ Finset.univ with (fun v : S => τ v) = ξ,
          μ τ / ckCyl μ S τ :=
        (Finset.sum_fiberwise Finset.univ (fun τ : Fin n → Fin q => fun v : S => τ v)
          (fun τ => μ τ / ckCyl μ S τ)).symm
    _ ≤ ∑ _ξ : (S → Fin q), (1 : ℝ) := by
        refine Finset.sum_le_sum fun ξ _ => CKInfoA_finset_class_sum_le_one hμ S _ ?_
        intro τ hτ τ' hτ' v hv
        rw [Finset.mem_filter] at hτ hτ'
        exact congrFun (hτ'.2.trans hτ.2.symm) ⟨v, hv⟩
    _ = (q : ℝ) ^ S.card := by simp

/-- The marginal `μ_v` of a law `μ` on `[q]^n` lies in the simplex. -/
theorem ck_marg_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (v : Fin n) :
    ckMarg μ v ∈ stdSimplex ℝ (Fin q) := by
  refine ⟨fun a => Finset.sum_nonneg fun τ _ => hμ.1 τ, ?_⟩
  exact (Finset.sum_fiberwise Finset.univ (fun τ : Fin n → Fin q => τ v) μ).trans hμ.2

/-- (E1): `h_μ(S) ≥ 0`. -/
theorem ck_H_nonneg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (S : Finset (Fin n)) :
    0 ≤ ckH μ S := by
  rw [ckH, neg_nonneg]
  exact Finset.sum_nonpos fun τ _ => mul_nonpos_of_nonneg_of_nonpos (hμ.1 τ)
    (Real.log_nonpos (CKInfoA_cyl_nonneg hμ S τ) (CKInfoA_cyl_le_one hμ S τ))

/-- (E1): `h_μ(∅) = 0`. -/
theorem ck_H_empty {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) : ckH μ ∅ = 0 := by
  simp [ckH, CKInfoA_cyl_empty hμ]

/-- (E1): `h_μ(S) ≤ |S| log q`.  Proof: Gibbs' inequality via `log y ≥ 1 - 1/y`, together with
the bound `q^{|S|}` on the number of classes of configurations that agree on `S`. -/
theorem ck_H_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (S : Finset (Fin n)) :
    ckH μ S ≤ S.card * Real.log q := by
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = (q : ℝ) ^ S.card := ⟨_, rfl⟩
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      have hS : S = ∅ := by
        by_contra hne
        obtain ⟨v, -⟩ := Finset.nonempty_iff_ne_empty.2 hne
        have h0 : ∑ τ, μ τ = 0 := Finset.sum_eq_zero fun τ _ => (τ v).elim0
        rw [hμ.2] at h0
        exact one_ne_zero h0
      simp [hNdef, hS]
    · rw [hNdef]; exact pow_pos (Nat.cast_pos.2 hq) _
  have key : ∀ τ, μ τ * (-Real.log (ckCyl μ S τ) - Real.log N) ≤
      N⁻¹ * (μ τ / ckCyl μ S τ) - μ τ := by
    intro τ
    rcases (hμ.1 τ).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hc := CKInfoA_cyl_pos hμ S hpos
      have h1 := Real.one_sub_inv_le_log_of_pos (mul_pos hN hc)
      rw [Real.log_mul hN.ne' hc.ne'] at h1
      calc μ τ * (-Real.log (ckCyl μ S τ) - Real.log N)
          ≤ μ τ * ((N * ckCyl μ S τ)⁻¹ - 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hpos.le
        _ = N⁻¹ * (μ τ / ckCyl μ S τ) - μ τ := by rw [mul_inv]; ring
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => key τ
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hμ.2] at hsum
  have hlhs : ∑ τ, μ τ * (-Real.log (ckCyl μ S τ) - Real.log N) = ckH μ S - Real.log N := by
    have e1 : ∀ τ, μ τ * (-Real.log (ckCyl μ S τ) - Real.log N) =
        -(μ τ * Real.log (ckCyl μ S τ)) - μ τ * Real.log N := fun τ => by ring
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      ← Finset.sum_mul, hμ.2, ckH]
    ring
  have hcount : N⁻¹ * ∑ τ, μ τ / ckCyl μ S τ ≤ 1 := by
    calc N⁻¹ * ∑ τ, μ τ / ckCyl μ S τ ≤ N⁻¹ * N :=
          mul_le_mul_of_nonneg_left (hNdef ▸ CKInfoA_sum_div_cyl_le hμ S) (inv_nonneg.2 hN.le)
      _ = 1 := inv_mul_cancel₀ hN.ne'
  have hlogN : Real.log N = S.card * Real.log q := by rw [hNdef, Real.log_pow]
  rw [hlhs] at hsum
  linarith

/-- (E3): `h_μ` is monotone. -/
theorem ck_H_mono {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) {S T : Finset (Fin n)}
    (h : S ⊆ T) : ckH μ S ≤ ckH μ T := by
  rw [ckH, ckH, neg_le_neg_iff]
  refine Finset.sum_le_sum fun τ _ => ?_
  rcases (hμ.1 τ).eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (CKInfoA_cyl_pos hμ T hpos) (CKInfoA_cyl_anti hμ h τ)) hpos.le

/-- Inner sum of the submodularity identity: for fixed `σ, ρ`, the configurations `τ` with
`τ_S = σ_S` and `τ_T = ρ_T` form (at most) one `(S ∪ T)`-class, and exist only if
`σ_{S ∩ T} = ρ_{S ∩ T}`. -/
private lemma CKInfoA_submod_inner {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S T : Finset (Fin n)) (σ ρ : Fin n → Fin q) :
    ∑ τ, (if ckAgree S τ σ then μ σ else 0) * (if ckAgree T τ ρ then μ ρ else 0) *
        (μ τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) ≤
      (if ckAgree (S ∩ T) σ ρ then μ ρ else 0) * (μ σ / ckCyl μ (S ∩ T) σ) := by
  have hterm : ∀ τ, (if ckAgree S τ σ then μ σ else 0) * (if ckAgree T τ ρ then μ ρ else 0) *
        (μ τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) =
      (if ckAgree S τ σ ∧ ckAgree T τ ρ then μ τ / ckCyl μ (S ∪ T) τ else 0) *
        (μ ρ * (μ σ / ckCyl μ (S ∩ T) σ)) := by
    intro τ
    by_cases h1 : ckAgree S τ σ
    · by_cases h2 : ckAgree T τ ρ
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩,
          CKInfoA_cyl_congr μ (CKInfoA_agree_mono Finset.inter_subset_left h1)]
        ring
      · rw [if_neg h2, if_neg fun h : ckAgree S τ σ ∧ ckAgree T τ ρ => h2 h.2]; ring
    · rw [if_neg h1, if_neg fun h : ckAgree S τ σ ∧ ckAgree T τ ρ => h1 h.1]; ring
  rw [Finset.sum_congr rfl fun τ _ => hterm τ, ← Finset.sum_mul, ← Finset.sum_filter]
  by_cases hI : ckAgree (S ∩ T) σ ρ
  · rw [if_pos hI]
    have hle : ∑ τ ∈ Finset.univ with (ckAgree S τ σ ∧ ckAgree T τ ρ),
        μ τ / ckCyl μ (S ∪ T) τ ≤ 1 := by
      refine CKInfoA_finset_class_sum_le_one hμ (S ∪ T) _ fun τ hτ τ' hτ' v hv => ?_
      rw [Finset.mem_filter] at hτ hτ'
      rcases Finset.mem_union.1 hv with hv | hv
      · exact (hτ'.2.1 v hv).symm.trans (hτ.2.1 v hv)
      · exact (hτ'.2.2 v hv).symm.trans (hτ.2.2 v hv)
    have hnn : 0 ≤ μ ρ * (μ σ / ckCyl μ (S ∩ T) σ) :=
      mul_nonneg (hμ.1 ρ) (div_nonneg (hμ.1 σ) (CKInfoA_cyl_nonneg hμ _ σ))
    calc _ ≤ 1 * (μ ρ * (μ σ / ckCyl μ (S ∩ T) σ)) := mul_le_mul_of_nonneg_right hle hnn
      _ = _ := one_mul _
  · rw [if_neg hI, zero_mul]
    refine le_of_eq (mul_eq_zero_of_left (Finset.sum_eq_zero fun τ hτ => ?_) _)
    rw [Finset.mem_filter] at hτ
    exact absurd (fun v hv => (hτ.2.2 v (Finset.mem_of_mem_inter_right hv)).trans
      (hτ.2.1 v (Finset.mem_of_mem_inter_left hv)).symm) hI

/-- The key identity behind submodularity:
`∑_τ μ(τ) μ(τ_S) μ(τ_T) / (μ(τ_{S ∪ T}) μ(τ_{S ∩ T})) ≤ 1`. -/
private lemma CKInfoA_submod_ratio_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S T : Finset (Fin n)) :
    ∑ τ, μ τ * (ckCyl μ S τ * ckCyl μ T τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) ≤ 1 := by
  have hexp : ∀ τ, μ τ * (ckCyl μ S τ * ckCyl μ T τ /
      (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) =
      ∑ σ, ∑ ρ, (if ckAgree S τ σ then μ σ else 0) * (if ckAgree T τ ρ then μ ρ else 0) *
        (μ τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) := by
    intro τ
    rw [CKInfoA_cyl_eq_sum_ite μ S τ, CKInfoA_cyl_eq_sum_ite μ T τ, Finset.sum_mul_sum,
      Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  calc ∑ τ, μ τ * (ckCyl μ S τ * ckCyl μ T τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ))
      = ∑ τ, ∑ σ, ∑ ρ, (if ckAgree S τ σ then μ σ else 0) *
          (if ckAgree T τ ρ then μ ρ else 0) *
          (μ τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) :=
        Finset.sum_congr rfl fun τ _ => hexp τ
    _ = ∑ σ, ∑ ρ, ∑ τ, (if ckAgree S τ σ then μ σ else 0) *
          (if ckAgree T τ ρ then μ ρ else 0) *
          (μ τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) :=
        Finset.sum_comm.trans (Finset.sum_congr rfl fun σ _ => Finset.sum_comm)
    _ ≤ ∑ σ, ∑ ρ, (if ckAgree (S ∩ T) σ ρ then μ ρ else 0) * (μ σ / ckCyl μ (S ∩ T) σ) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun ρ _ =>
          CKInfoA_submod_inner hμ S T σ ρ
    _ = ∑ σ, ckCyl μ (S ∩ T) σ * (μ σ / ckCyl μ (S ∩ T) σ) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.sum_mul, ← CKInfoA_cyl_eq_sum_ite]
    _ ≤ ∑ σ, μ σ := Finset.sum_le_sum fun σ _ => by
        rcases eq_or_ne (ckCyl μ (S ∩ T) σ) 0 with h | h
        · rw [h, zero_mul]; exact hμ.1 σ
        · rw [mul_div_cancel₀ _ h]
    _ = 1 := hμ.2

/-- (E3), submodularity: `h(S ∪ T) + h(S ∩ T) ≤ h(S) + h(T)`.  In place of the concavity argument,
the proof applies `log y ≤ y - 1` to the cylinder ratio
`y = μ(τ_S) μ(τ_T) / (μ(τ_{S ∪ T}) μ(τ_{S ∩ T}))`, whose `μ`-average is at most `1`
(`CKInfoA_submod_ratio_le`). -/
theorem ck_H_submod {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (S T : Finset (Fin n)) :
    ckH μ (S ∪ T) + ckH μ (S ∩ T) ≤ ckH μ S + ckH μ T := by
  have key : ∀ τ, μ τ * (Real.log (ckCyl μ S τ) + Real.log (ckCyl μ T τ) -
      Real.log (ckCyl μ (S ∪ T) τ) - Real.log (ckCyl μ (S ∩ T) τ)) ≤
      μ τ * (ckCyl μ S τ * ckCyl μ T τ / (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ)) - μ τ := by
    intro τ
    rcases (hμ.1 τ).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have h1 := CKInfoA_cyl_pos hμ S hpos
      have h2 := CKInfoA_cyl_pos hμ T hpos
      have h3 := CKInfoA_cyl_pos hμ (S ∪ T) hpos
      have h4 := CKInfoA_cyl_pos hμ (S ∩ T) hpos
      have hlog := Real.log_le_sub_one_of_pos (div_pos (mul_pos h1 h2) (mul_pos h3 h4))
      rw [Real.log_div (mul_pos h1 h2).ne' (mul_pos h3 h4).ne', Real.log_mul h1.ne' h2.ne',
        Real.log_mul h3.ne' h4.ne'] at hlog
      calc μ τ * (Real.log (ckCyl μ S τ) + Real.log (ckCyl μ T τ) -
            Real.log (ckCyl μ (S ∪ T) τ) - Real.log (ckCyl μ (S ∩ T) τ))
          = μ τ * (Real.log (ckCyl μ S τ) + Real.log (ckCyl μ T τ) -
            (Real.log (ckCyl μ (S ∪ T) τ) + Real.log (ckCyl μ (S ∩ T) τ))) := by ring
        _ ≤ μ τ * (ckCyl μ S τ * ckCyl μ T τ /
            (ckCyl μ (S ∪ T) τ * ckCyl μ (S ∩ T) τ) - 1) :=
          mul_le_mul_of_nonneg_left hlog hpos.le
        _ = _ := by ring
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => key τ
  rw [Finset.sum_sub_distrib, hμ.2] at hsum
  have hratio := CKInfoA_submod_ratio_le hμ S T
  have hexp : ∑ τ, μ τ * (Real.log (ckCyl μ S τ) + Real.log (ckCyl μ T τ) -
      Real.log (ckCyl μ (S ∪ T) τ) - Real.log (ckCyl μ (S ∩ T) τ)) =
      ∑ τ, μ τ * Real.log (ckCyl μ S τ) + ∑ τ, μ τ * Real.log (ckCyl μ T τ) -
      ∑ τ, μ τ * Real.log (ckCyl μ (S ∪ T) τ) - ∑ τ, μ τ * Real.log (ckCyl μ (S ∩ T) τ) := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hexp] at hsum
  simp only [ckH]
  linarith

/-- (E3): `I(τ_A; τ_B | τ_S) ≥ 0`. -/
theorem ck_MI_nonneg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (A B S : Finset (Fin n)) : 0 ≤ ckMI μ A B S := by
  have h1 := ck_H_submod hμ (A ∪ S) (B ∪ S)
  have h2 : A ∪ S ∪ (B ∪ S) = A ∪ B ∪ S := by
    ext x; simp only [Finset.mem_union]; tauto
  have h3 := ck_H_mono hμ (show S ⊆ (A ∪ S) ∩ (B ∪ S) from
    Finset.subset_inter Finset.subset_union_right Finset.subset_union_right)
  rw [h2] at h1
  rw [ckMI]
  linarith

/-- (E5): `I(τ_A; τ_B | τ_S) ≤ I(τ_A; τ_{B'} | τ_S)` for `B ⊆ B'`. -/
theorem ck_MI_mono {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (A : Finset (Fin n))
    {B B' : Finset (Fin n)} (h : B ⊆ B') (S : Finset (Fin n)) :
    ckMI μ A B S ≤ ckMI μ A B' S := by
  have hBB : ∀ x, x ∈ B → x ∈ B' := fun x hx => h hx
  have h1 := ck_H_submod hμ (A ∪ B ∪ S) (B' ∪ S)
  have h2 : A ∪ B ∪ S ∪ (B' ∪ S) = A ∪ B' ∪ S := by
    ext x; have := hBB x; simp only [Finset.mem_union]; tauto
  have h3 := ck_H_mono hμ (show B ∪ S ⊆ (A ∪ B ∪ S) ∩ (B' ∪ S) by
    intro x hx; have := hBB x
    simp only [Finset.mem_union, Finset.mem_inter] at hx ⊢; tauto)
  rw [h2] at h1
  rw [ckMI, ckMI]
  linarith

/-- `I(τ_w; τ_B | τ_S) ≤ H(τ_w) ≤ log q`. -/
theorem ck_MI_single_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (w : Fin n)
    (B S : Finset (Fin n)) : ckMI μ {w} B S ≤ Real.log q := by
  have h1 := ck_H_mono hμ (show B ∪ S ⊆ {w} ∪ B ∪ S by
    intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto)
  have h2 := ck_H_submod hμ {w} S
  have h3 := ck_H_nonneg hμ ({w} ∩ S)
  have h4 := ck_H_le hμ {w}
  rw [Finset.card_singleton, Nat.cast_one, one_mul] at h4
  rw [ckMI]
  linarith

/-- The conditional law `μ(· | τ_S = ξ_S)` is a probability vector when `μ(ξ) > 0`. -/
theorem ck_cond_isPMF {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (S : Finset (Fin n))
    {ξ : Fin n → Fin q} (hξ : 0 < μ ξ) : IsPMF (ckCond μ S ξ) := by
  have hc := CKInfoA_cyl_pos hμ S hξ
  refine ⟨fun τ => ?_, ?_⟩
  · rw [ckCond]
    split_ifs
    · exact div_nonneg (hμ.1 τ) hc.le
    · exact le_rfl
  · calc ∑ τ, ckCond μ S ξ τ = ∑ τ, (if ckAgree S ξ τ then μ τ else 0) / ckCyl μ S ξ := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [ckCond]
          split_ifs <;> simp
      _ = ckCyl μ S ξ / ckCyl μ S ξ := by rw [← Finset.sum_div, ← CKInfoA_cyl_eq_sum_ite]
      _ = 1 := div_self hc.ne'

/-- Cylinder masses of the conditional law `μ(· | τ_S = ξ_S)` at a point `σ` of the pinned
class: `μ^ξ(σ'_B = σ_B) = μ(σ'_{B ∪ S} = σ_{B ∪ S}) / μ(σ'_S = ξ_S)`. -/
private lemma CKInfoA_cyl_cond {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S B : Finset (Fin n))
    {τ σ : Fin n → Fin q} (h : ckAgree S τ σ) :
    ckCyl (ckCond μ S τ) B σ = ckCyl μ (B ∪ S) σ / ckCyl μ S τ := by
  rw [CKInfoA_cyl_eq_sum_ite (ckCond μ S τ) B σ, CKInfoA_cyl_eq_sum_ite μ (B ∪ S) σ,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hiff : ckAgree (B ∪ S) σ ρ ↔ ckAgree B σ ρ ∧ ckAgree S τ ρ := by
    constructor
    · intro h3
      exact ⟨fun v hv => h3 v (Finset.mem_union_left _ hv),
        fun v hv => (h3 v (Finset.mem_union_right _ hv)).trans (h v hv)⟩
    · rintro ⟨h1, h2⟩ v hv
      rcases Finset.mem_union.1 hv with hv | hv
      · exact h1 v hv
      · exact (h2 v hv).trans (h v hv).symm
  rw [ckCond]
  by_cases h1 : ckAgree B σ ρ
  · by_cases h2 : ckAgree S τ ρ
    · rw [if_pos h1, if_pos h2, if_pos (hiff.2 ⟨h1, h2⟩)]
    · rw [if_pos h1, if_neg h2, if_neg fun h3 => h2 (hiff.1 h3).2, zero_div]
  · rw [if_neg h1, if_neg fun h3 => h1 (hiff.1 h3).1, zero_div]

/-- (E2), chain rule: averaging the entropy of `τ_B` under `μ(· | τ'_S = τ_S)` against `μ(τ)`
gives `h(B ∪ S) - h(S)`. -/
theorem ck_H_cond_avg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S B : Finset (Fin n)) :
    ∑ τ, μ τ * ckH (ckCond μ S τ) B = ckH μ (B ∪ S) - ckH μ S := by
  have hterm : ∀ τ σ, μ τ * (ckCond μ S τ σ * Real.log (ckCyl (ckCond μ S τ) B σ)) =
      (if ckAgree S σ τ then μ τ else 0) *
        (μ σ / ckCyl μ S σ * Real.log (ckCyl μ (B ∪ S) σ / ckCyl μ S σ)) := by
    intro τ σ
    by_cases h : ckAgree S τ σ
    · have hc : ckCond μ S τ σ = μ σ / ckCyl μ S τ := by rw [ckCond, if_pos h]
      rw [if_pos (CKInfoA_agree_symm h), CKInfoA_cyl_cond μ S B h, hc, CKInfoA_cyl_congr μ h]
    · have hc : ckCond μ S τ σ = 0 := by rw [ckCond, if_neg h]
      rw [if_neg fun h' => h (CKInfoA_agree_symm h'), hc]
      ring
  have hL : ∑ τ, μ τ * ckH (ckCond μ S τ) B =
      -∑ σ, ckCyl μ S σ *
        (μ σ / ckCyl μ S σ * Real.log (ckCyl μ (B ∪ S) σ / ckCyl μ S σ)) := by
    simp only [ckH, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    rw [neg_inj, Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => hterm τ σ,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← Finset.sum_mul, ← CKInfoA_cyl_eq_sum_ite]
  have h3 : ∀ σ, ckCyl μ S σ *
      (μ σ / ckCyl μ S σ * Real.log (ckCyl μ (B ∪ S) σ / ckCyl μ S σ)) =
      μ σ * Real.log (ckCyl μ (B ∪ S) σ) - μ σ * Real.log (ckCyl μ S σ) := by
    intro σ
    rcases (hμ.1 σ).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hS := CKInfoA_cyl_pos hμ S hpos
      have hBS := CKInfoA_cyl_pos hμ (B ∪ S) hpos
      rw [Real.log_div hBS.ne' hS.ne', ← mul_assoc, mul_div_cancel₀ _ hS.ne']
      ring
  rw [hL, Finset.sum_congr rfl fun σ _ => h3 σ, Finset.sum_sub_distrib, ckH, ckH]
  ring

/-- (E2) for mutual information: averaging `I(τ_A; τ_B)` under `μ(· | τ'_S = τ_S)` against `μ(τ)`
gives `I_μ(τ_A; τ_B | τ_S)`. -/
theorem ck_MI_cond_avg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S A B : Finset (Fin n)) :
    ∑ τ, μ τ * ckMI (ckCond μ S τ) A B ∅ = ckMI μ A B S := by
  have e : ∀ τ, μ τ * ckMI (ckCond μ S τ) A B ∅ =
      μ τ * ckH (ckCond μ S τ) A + μ τ * ckH (ckCond μ S τ) B -
        μ τ * ckH (ckCond μ S τ) (A ∪ B) - μ τ * ckH (ckCond μ S τ) ∅ := by
    intro τ
    simp only [ckMI, Finset.union_empty]
    ring
  rw [Finset.sum_congr rfl fun τ _ => e τ, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ck_H_cond_avg hμ, ck_H_cond_avg hμ, ck_H_cond_avg hμ,
    ck_H_cond_avg hμ, Finset.empty_union, ckMI]
  ring

/-! ### Lemma 1.6: `∑ |p - p'| ≤ 2 √D(p ‖ p')` -/

/-- Pointwise Hellinger bound in square-root coordinates `x = √a`, `y = √b`. -/
private lemma CKInfoB_hell_pt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (x - y) ^ 2 ≤ x ^ 2 * Real.log (x ^ 2 / y ^ 2) - x ^ 2 + y ^ 2 := by
  have h1 : Real.log (x ^ 2 / y ^ 2) = 2 * Real.log (x / y) := by
    rw [← div_pow, Real.log_pow]; norm_num
  have h2 : 1 - (x / y)⁻¹ ≤ Real.log (x / y) := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  rw [inv_div] at h2
  have h3 : x ^ 2 * (1 - y / x) = x ^ 2 - x * y := by field_simp
  have h4 : x ^ 2 * (1 - y / x) ≤ x ^ 2 * Real.log (x / y) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [h1]
  nlinarith [h3, h4]

/-- `(√a - √b)² ≤ a log(a/b) - a + b` for `a, b ≥ 0` with `a > 0 → b > 0`. -/
private lemma CKInfoB_hell {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a → 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a * Real.log (a / b) - a + b := by
  rcases ha.lt_or_eq with ha' | ha'
  · have hx := Real.sqrt_pos.2 ha'
    have hy := Real.sqrt_pos.2 (hab ha')
    have := CKInfoB_hell_pt hx hy
    rwa [Real.sq_sqrt ha, Real.sq_sqrt hb] at this
  · subst ha'
    rw [Real.sqrt_zero, zero_sub, neg_sq, Real.sq_sqrt hb, zero_mul, sub_zero, zero_add]

/-- **Lemma 1.6.** `∑ |p - p'| ≤ 2 √(∑ p log (p/p'))` for probability vectors with `p ≪ p'`. -/
private lemma CKInfoB_L1_le_KL {ι : Type*} [Fintype ι] (p p' : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp' : ∀ i, 0 ≤ p' i) (hs : ∑ i, p i = 1) (hs' : ∑ i, p' i = 1)
    (hac : ∀ i, 0 < p i → 0 < p' i) :
    ∑ i, |p i - p' i| ≤ 2 * Real.sqrt (∑ i, p i * Real.log (p i / p' i)) := by
  have hH : ∑ i, (Real.sqrt (p i) - Real.sqrt (p' i)) ^ 2 ≤
      ∑ i, p i * Real.log (p i / p' i) := by
    have := Finset.sum_le_sum
      (fun i (_ : i ∈ Finset.univ) => CKInfoB_hell (hp i) (hp' i) (hac i))
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hs, hs'] at this
    linarith
  have hD0 : 0 ≤ ∑ i, p i * Real.log (p i / p' i) :=
    le_trans (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hH
  have habs : ∀ i, |p i - p' i| =
      |Real.sqrt (p i) - Real.sqrt (p' i)| * (Real.sqrt (p i) + Real.sqrt (p' i)) := by
    intro i
    have e1 := Real.sq_sqrt (hp i)
    have e2 := Real.sq_sqrt (hp' i)
    have h1 : p i - p' i =
        (Real.sqrt (p i) - Real.sqrt (p' i)) * (Real.sqrt (p i) + Real.sqrt (p' i)) := by
      nlinarith
    rw [h1, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (p i) + Real.sqrt (p' i))]
  have hplus : ∑ i, (Real.sqrt (p i) + Real.sqrt (p' i)) ^ 2 ≤ 4 := by
    have h : ∀ i, (Real.sqrt (p i) + Real.sqrt (p' i)) ^ 2 ≤ 2 * (p i + p' i) := by
      intro i
      have e1 := Real.sq_sqrt (hp i)
      have e2 := Real.sq_sqrt (hp' i)
      nlinarith [sq_nonneg (Real.sqrt (p i) - Real.sqrt (p' i))]
    calc ∑ i, (Real.sqrt (p i) + Real.sqrt (p' i)) ^ 2 ≤ ∑ i, 2 * (p i + p' i) :=
          Finset.sum_le_sum (fun i _ => h i)
      _ = 4 := by rw [← Finset.mul_sum, Finset.sum_add_distrib, hs, hs']; norm_num
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |Real.sqrt (p i) - Real.sqrt (p' i)|) (fun i => Real.sqrt (p i) + Real.sqrt (p' i))
  simp only [sq_abs] at hCS
  have hsum : ∑ i, |p i - p' i| =
      ∑ i, |Real.sqrt (p i) - Real.sqrt (p' i)| * (Real.sqrt (p i) + Real.sqrt (p' i)) :=
    Finset.sum_congr rfl (fun i _ => habs i)
  have h4 : (∑ i, |p i - p' i|) ^ 2 ≤
      (2 * Real.sqrt (∑ i, p i * Real.log (p i / p' i))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hD0, hsum]
    calc _ ≤ (∑ i, (Real.sqrt (p i) - Real.sqrt (p' i)) ^ 2) *
          ∑ i, (Real.sqrt (p i) + Real.sqrt (p' i)) ^ 2 := hCS
      _ ≤ (∑ i, p i * Real.log (p i / p' i)) * 4 :=
          mul_le_mul hH hplus (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hD0
      _ = 2 ^ 2 * ∑ i, p i * Real.log (p i / p' i) := by ring
  exact (sq_le_sq₀ (Finset.sum_nonneg (fun i _ => abs_nonneg _)) (by positivity)).1 h4

/-! ### Cylinder sums over `[q]^n`; Lemma 1.7 (decorrelation) -/

/-- The number of configurations in an `S`-cylinder, `q^{n - |S|}` (independent of the base). -/
private def CKInfoB_N (n q : ℕ) (S : Finset (Fin n)) : ℝ :=
  ∏ v : Fin n, if v ∈ S then (1 : ℝ) else (q : ℝ)

private lemma CKInfoB_count {n q : ℕ} (S : Finset (Fin n)) (ξ : Fin n → Fin q) :
    ∑ σ : Fin n → Fin q, (if ckAgree S σ ξ then (1 : ℝ) else 0) = CKInfoB_N n q S := by
  rw [Finset.sum_boole]
  have hset : (Finset.univ.filter fun σ : Fin n → Fin q => ckAgree S σ ξ) =
      Fintype.piFinset (fun v => if v ∈ S then {ξ v} else Finset.univ) := by
    ext σ
    rw [Finset.mem_filter_univ, Fintype.mem_piFinset]
    constructor
    · intro h v
      split_ifs with hv
      · rw [Finset.mem_singleton]; exact (h v hv).symm
      · exact Finset.mem_univ _
    · intro h v hv
      have := h v
      rw [if_pos hv, Finset.mem_singleton] at this
      exact this.symm
  rw [hset, Fintype.card_piFinset]
  unfold CKInfoB_N
  push_cast
  refine Finset.prod_congr rfl (fun v _ => ?_)
  split_ifs <;> simp

private lemma CKInfoB_N_pos {n q : ℕ} (S : Finset (Fin n)) (ξ : Fin n → Fin q) :
    0 < CKInfoB_N n q S := by
  rw [← CKInfoB_count S ξ]
  have h1 : (if ckAgree S ξ ξ then (1 : ℝ) else 0) = 1 := if_pos (fun v _ => rfl)
  calc (0 : ℝ) < 1 := one_pos
    _ = if ckAgree S ξ ξ then (1 : ℝ) else 0 := h1.symm
    _ ≤ ∑ σ, (if ckAgree S σ ξ then (1 : ℝ) else 0) :=
        Finset.single_le_sum (f := fun σ => if ckAgree S σ ξ then (1 : ℝ) else 0)
          (fun σ _ => by split_ifs <;> norm_num) (Finset.mem_univ ξ)

private lemma CKInfoB_cyl_nonneg {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) (τ : Fin n → Fin q) : 0 ≤ ckCyl μ S τ :=
  Finset.sum_nonneg (fun τ' _ => hμ.1 τ')

private lemma CKInfoB_cyl_self {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (S : Finset (Fin n)) (τ : Fin n → Fin q) : μ τ ≤ ckCyl μ S τ := by
  unfold ckCyl
  exact Finset.single_le_sum (f := μ) (fun τ' _ => hμ.1 τ')
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, fun v _ => rfl⟩)

private lemma CKInfoB_cyl_mono {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    {A S : Finset (Fin n)} (h : A ⊆ S) (τ : Fin n → Fin q) : ckCyl μ S τ ≤ ckCyl μ A τ := by
  unfold ckCyl
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro τ' hτ'
    rw [Finset.mem_filter] at hτ' ⊢
    exact ⟨hτ'.1, fun v hv => hτ'.2 v (h hv)⟩
  · intro τ' _ _
    exact hμ.1 τ'

private lemma CKInfoB_cyl_congr {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) {A S : Finset (Fin n)}
    (h : A ⊆ S) {σ τ : Fin n → Fin q} (hst : ckAgree S σ τ) : ckCyl μ A σ = ckCyl μ A τ := by
  unfold ckCyl
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext τ'
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hu, h'⟩
    refine ⟨hu, fun v hv => ?_⟩
    rw [h' v hv]
    exact (hst v (h hv)).symm
  · rintro ⟨hu, h'⟩
    refine ⟨hu, fun v hv => ?_⟩
    rw [h' v hv]
    exact hst v (h hv)

/-- Spreading a cylinder mass uniformly over its cylinder:
`∑_σ μ(τ_S = σ_S) G(σ) = N_S ∑_τ μ(τ) G(τ)` for `G` depending on `σ_S` only. -/
private lemma CKInfoB_cyl_sum {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (S : Finset (Fin n))
    (G : (Fin n → Fin q) → ℝ) (hG : ∀ σ τ, ckAgree S σ τ → G σ = G τ) :
    ∑ σ, ckCyl μ S σ * G σ = CKInfoB_N n q S * ∑ τ, μ τ * G τ := by
  have h1 : ∀ σ, ckCyl μ S σ * G σ = ∑ τ, if ckAgree S σ τ then μ τ * G τ else 0 := by
    intro σ
    unfold ckCyl
    rw [Finset.sum_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    split_ifs with h
    · rw [hG σ τ h]
    · simp
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  have h2 : ∀ σ, (if ckAgree S σ τ then μ τ * G τ else 0) =
      μ τ * G τ * (if ckAgree S σ τ then (1 : ℝ) else 0) := by
    intro σ
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun σ _ => h2 σ), ← Finset.mul_sum, CKInfoB_count]
  ring

/-- The product of two cylinder masses, spread over `[q]^n`:
`∑_σ μ(τ_A = σ_A) μ(τ_B = σ_B) F(σ,σ) = N_{A ∪ B} ∑_{τ,τ'} μ(τ) μ(τ') F(τ,τ')`. -/
private lemma CKInfoB_prod_sum {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) {A B : Finset (Fin n)}
    (hAB : Disjoint A B) (F : (Fin n → Fin q) → (Fin n → Fin q) → ℝ)
    (hF : ∀ τ₁ τ₂ τ₁' τ₂', ckAgree A τ₁ τ₂ → ckAgree B τ₁' τ₂' → F τ₁ τ₁' = F τ₂ τ₂') :
    ∑ σ, ckCyl μ A σ * ckCyl μ B σ * F σ σ =
      CKInfoB_N n q (A ∪ B) * ∑ τ, ∑ τ', μ τ * μ τ' * F τ τ' := by
  have h1 : ∀ σ, ckCyl μ A σ * ckCyl μ B σ * F σ σ =
      ∑ τ, ∑ τ', if ckAgree A σ τ ∧ ckAgree B σ τ' then μ τ * μ τ' * F τ τ' else 0 := by
    intro σ
    unfold ckCyl
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun τ' _ => ?_)
    by_cases hA : ckAgree A σ τ
    · by_cases hB : ckAgree B σ τ'
      · rw [if_pos hA, if_pos hB, if_pos ⟨hA, hB⟩, hF σ τ σ τ' hA hB]
      · rw [if_neg hB, if_neg (show ¬(ckAgree A σ τ ∧ ckAgree B σ τ') from fun h => hB h.2)]
        ring
    · rw [if_neg hA, if_neg (show ¬(ckAgree A σ τ ∧ ckAgree B σ τ') from fun h => hA h.1)]
      ring
  rw [Finset.sum_congr rfl (fun σ _ => h1 σ), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ' _ => ?_)
  have hglue : ∀ σ, (ckAgree A σ τ ∧ ckAgree B σ τ') ↔
      ckAgree (A ∪ B) σ (fun v => if v ∈ A then τ v else τ' v) := by
    intro σ
    constructor
    · rintro ⟨hA, hB⟩ v hv
      rcases Finset.mem_union.1 hv with hvA | hvB
      · simp only [if_pos hvA]
        exact hA v hvA
      · have hvA : v ∉ A := Finset.disjoint_right.1 hAB hvB
        simp only [if_neg hvA]
        exact hB v hvB
    · intro h
      constructor
      · intro v hvA
        have := h v (Finset.mem_union_left _ hvA)
        simp only [if_pos hvA] at this
        exact this
      · intro v hvB
        have hvA : v ∉ A := Finset.disjoint_right.1 hAB hvB
        have := h v (Finset.mem_union_right _ hvB)
        simp only [if_neg hvA] at this
        exact this
  rw [← CKInfoB_count (A ∪ B) (fun v => if v ∈ A then τ v else τ' v), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  by_cases h : ckAgree A σ τ ∧ ckAgree B σ τ'
  · rw [if_pos h, if_pos ((hglue σ).1 h)]
    ring
  · rw [if_neg h, if_neg (fun h' => h ((hglue σ).2 h'))]
    ring

/-- (E4) in `τ`-sum form: `I(τ_A; τ_B) = ∑_τ μ(τ) log (μ(τ_{A∪B}) / (μ(τ_A) μ(τ_B)))`. -/
private lemma CKInfoB_MI_eq {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (A B : Finset (Fin n)) :
    ckMI μ A B ∅ =
      ∑ τ, μ τ * Real.log (ckCyl μ (A ∪ B) τ / (ckCyl μ A τ * ckCyl μ B τ)) := by
  have key : ∀ τ, μ τ * Real.log (ckCyl μ (A ∪ B) τ / (ckCyl μ A τ * ckCyl μ B τ)) =
      μ τ * Real.log (ckCyl μ (A ∪ B) τ) - μ τ * Real.log (ckCyl μ A τ) -
        μ τ * Real.log (ckCyl μ B τ) := by
    intro τ
    rcases (hμ.1 τ).lt_or_eq with h | h
    · have hP := lt_of_lt_of_le h (CKInfoB_cyl_self hμ (A ∪ B) τ)
      have ha := lt_of_lt_of_le h (CKInfoB_cyl_self hμ A τ)
      have hb := lt_of_lt_of_le h (CKInfoB_cyl_self hμ B τ)
      rw [Real.log_div hP.ne' (mul_pos ha hb).ne', Real.log_mul ha.ne' hb.ne']
      ring
    · rw [← h]
      ring
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  unfold ckMI
  rw [ck_H_empty hμ]
  simp only [Finset.union_empty]
  unfold ckH
  ring

/-- The arithmetic of the induction step in the proof of Lemma 1.7(b). -/
private lemma CKInfoB_step {E1 mx EW PW c b Ix IW IW' : ℝ} (h1 : |E1 - mx * EW| ≤ c * b * Ix)
    (h2 : |EW - PW| ≤ c * IW) (hmx0 : 0 ≤ mx) (hmxb : mx ≤ b) (hIW : IW ≤ IW')
    (hc : 0 ≤ c * b) : |E1 - mx * PW| ≤ c * b * (Ix + IW') := by
  have e : E1 - mx * PW = (E1 - mx * EW) + mx * (EW - PW) := by ring
  rw [e]
  have h3 : |mx * (EW - PW)| ≤ b * (c * IW) := by
    rw [abs_mul, abs_of_nonneg hmx0]
    exact mul_le_mul hmxb h2 (abs_nonneg _) (le_trans hmx0 hmxb)
  have h4 : b * (c * IW) ≤ c * b * IW' := by
    have e' : b * (c * IW) = c * b * IW := by ring
    rw [e']
    exact mul_le_mul_of_nonneg_left hIW hc
  calc |E1 - mx * EW + mx * (EW - PW)| ≤ |E1 - mx * EW| + |mx * (EW - PW)| := abs_add_le _ _
    _ ≤ c * b * Ix + c * b * IW' := by linarith
    _ = c * b * (Ix + IW') := by ring

/-- Lemma 1.7(a), for a general bounded test function: if `A`, `B` are disjoint, `F(τ, τ')`
depends only on `τ_A` and `τ'_B`, and `|F| ≤ C`, then
`|⟨F(τ, τ)⟩_μ - ⟨F(τ, τ')⟩_{μ ⊗ μ}| ≤ 2C √I(τ_A; τ_B)`.  Proof: spread the law of `τ_{A ∪ B}` and
the product of the laws of `τ_A`, `τ_B` uniformly over `[q]^n` (`CKInfoB_cyl_sum`,
`CKInfoB_prod_sum`), then apply Lemma 1.6 and (E4) (`CKInfoB_MI_eq`). -/
theorem ck_cov_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) {A B : Finset (Fin n)}
    (hAB : Disjoint A B) (F : (Fin n → Fin q) → (Fin n → Fin q) → ℝ)
    (hF : ∀ τ₁ τ₂ τ₁' τ₂', ckAgree A τ₁ τ₂ → ckAgree B τ₁' τ₂' → F τ₁ τ₁' = F τ₂ τ₂')
    {C : ℝ} (hC : ∀ τ τ', |F τ τ'| ≤ C) :
    |∑ τ, μ τ * F τ τ - ∑ τ, ∑ τ', μ τ * μ τ' * F τ τ'| ≤
      2 * C * Real.sqrt (ckMI μ A B ∅) := by
  -- the configuration space is nonempty
  obtain ⟨τ₀⟩ : Nonempty (Fin n → Fin q) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := hμ.2
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC τ₀ τ₀)
  have hAS : A ⊆ A ∪ B := Finset.subset_union_left
  have hBS : B ⊆ A ∪ B := Finset.subset_union_right
  have hNpos : 0 < CKInfoB_N n q (A ∪ B) := CKInfoB_N_pos (A ∪ B) τ₀
  have hN0 : CKInfoB_N n q (A ∪ B) ≠ 0 := hNpos.ne'
  -- spread the joint law and the product law over `[q]^n`
  have e1 : ∑ σ, ckCyl μ (A ∪ B) σ * F σ σ = CKInfoB_N n q (A ∪ B) * ∑ τ, μ τ * F τ τ :=
    CKInfoB_cyl_sum μ (A ∪ B) (fun σ => F σ σ)
      (fun σ τ h => hF σ τ σ τ (fun v hv => h v (hAS hv)) (fun v hv => h v (hBS hv)))
  have e2 : ∑ σ, ckCyl μ A σ * ckCyl μ B σ * F σ σ =
      CKInfoB_N n q (A ∪ B) * ∑ τ, ∑ τ', μ τ * μ τ' * F τ τ' :=
    CKInfoB_prod_sum μ hAB F hF
  have s1 : ∑ σ, ckCyl μ (A ∪ B) σ = CKInfoB_N n q (A ∪ B) := by
    have h := CKInfoB_cyl_sum μ (A ∪ B) (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
    simp only [mul_one] at h
    rw [h, hμ.2, mul_one]
  have s2 : ∑ σ, ckCyl μ A σ * ckCyl μ B σ = CKInfoB_N n q (A ∪ B) := by
    have h := CKInfoB_prod_sum μ hAB (fun _ _ => (1 : ℝ)) (fun _ _ _ _ _ _ => rfl)
    simp only [mul_one] at h
    rw [h, ← Finset.sum_mul_sum, hμ.2, mul_one, mul_one]
  have e3 : ∑ σ, ckCyl μ (A ∪ B) σ *
      Real.log (ckCyl μ (A ∪ B) σ / (ckCyl μ A σ * ckCyl μ B σ)) =
      CKInfoB_N n q (A ∪ B) * ckMI μ A B ∅ := by
    rw [CKInfoB_MI_eq hμ A B]
    refine CKInfoB_cyl_sum μ (A ∪ B) _ (fun σ τ h => ?_)
    rw [CKInfoB_cyl_congr μ (subset_refl _) h, CKInfoB_cyl_congr μ hAS h,
      CKInfoB_cyl_congr μ hBS h]
  -- Lemma 1.6 for the spread laws
  have hL1 := CKInfoB_L1_le_KL (fun σ => ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B))
    (fun σ => ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B))
    (fun σ => div_nonneg (CKInfoB_cyl_nonneg hμ _ σ) hNpos.le)
    (fun σ => div_nonneg (mul_nonneg (CKInfoB_cyl_nonneg hμ _ σ) (CKInfoB_cyl_nonneg hμ _ σ))
      hNpos.le)
    (by rw [← Finset.sum_div, s1, div_self hN0])
    (by rw [← Finset.sum_div, s2, div_self hN0])
    (fun σ hσ => by
      have hP : 0 < ckCyl μ (A ∪ B) σ := by
        have := (div_pos_iff_of_pos_right hNpos).1 hσ
        exact this
      have ha := lt_of_lt_of_le hP (CKInfoB_cyl_mono hμ hAS σ)
      have hb := lt_of_lt_of_le hP (CKInfoB_cyl_mono hμ hBS σ)
      exact div_pos (mul_pos ha hb) hNpos)
  have hD : ∑ σ, ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) *
      Real.log (ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) /
        (ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B))) = ckMI μ A B ∅ := by
    have h : ∀ σ, ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) *
        Real.log (ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) /
          (ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B))) =
        (CKInfoB_N n q (A ∪ B))⁻¹ * (ckCyl μ (A ∪ B) σ *
          Real.log (ckCyl μ (A ∪ B) σ / (ckCyl μ A σ * ckCyl μ B σ))) := by
      intro σ
      rw [div_div_div_cancel_right₀ hN0]
      ring
    rw [Finset.sum_congr rfl (fun σ _ => h σ), ← Finset.mul_sum, e3, ← mul_assoc,
      inv_mul_cancel₀ hN0, one_mul]
  rw [hD] at hL1
  -- the covariance as an integral against the signed difference of the spread laws
  have hmain : ∑ τ, μ τ * F τ τ - ∑ τ, ∑ τ', μ τ * μ τ' * F τ τ' =
      ∑ σ, (ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) -
        ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B)) * F σ σ := by
    have h : ∀ σ, (ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) -
        ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B)) * F σ σ =
        (CKInfoB_N n q (A ∪ B))⁻¹ * (ckCyl μ (A ∪ B) σ * F σ σ) -
          (CKInfoB_N n q (A ∪ B))⁻¹ * (ckCyl μ A σ * ckCyl μ B σ * F σ σ) := by
      intro σ
      ring
    rw [Finset.sum_congr rfl (fun σ _ => h σ), Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, e1, e2, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hN0, one_mul, one_mul]
  rw [hmain]
  calc |∑ σ, (ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) -
        ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B)) * F σ σ|
      ≤ ∑ σ, |(ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) -
        ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B)) * F σ σ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ, |ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) -
        ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B)| * C := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hC σ σ) (abs_nonneg _)
    _ = C * ∑ σ, |ckCyl μ (A ∪ B) σ / CKInfoB_N n q (A ∪ B) -
        ckCyl μ A σ * ckCyl μ B σ / CKInfoB_N n q (A ∪ B)| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun σ _ => mul_comm _ _)
    _ ≤ C * (2 * Real.sqrt (ckMI μ A B ∅)) := mul_le_mul_of_nonneg_left hL1 hC0
    _ = 2 * C * Real.sqrt (ckMI μ A B ∅) := by ring

/-- Lemma 1.7(b): for `f_w : [q] → [0, b]`,
`|⟨∏_{w ∈ W} f_w(τ_w)⟩_μ - ∏_{w ∈ W} ⟨f_w(τ_w)⟩_μ| ≤ 2 b^{|W|} ∑_{w ∈ W} √I(τ_w; τ_{W ∖ w})`.
Proof by induction on `W`, using (a) and (E5). -/
theorem ck_prod_decorr {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (W : Finset (Fin n))
    (f : Fin n → Fin q → ℝ) {b : ℝ} (hf : ∀ w a, 0 ≤ f w a ∧ f w a ≤ b) :
    |∑ τ, μ τ * ∏ w ∈ W, f w (τ w) - ∏ w ∈ W, ∑ τ, μ τ * f w (τ w)| ≤
      2 * b ^ W.card * ∑ w ∈ W, Real.sqrt (ckMI μ {w} (W.erase w) ∅) := by
  induction W using Finset.induction_on with
  | empty => simp [hμ.2]
  | insert x W hx ih =>
    obtain ⟨τ₀⟩ : Nonempty (Fin n → Fin q) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have h1 := hμ.2
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
      exact zero_ne_one h1
    have hb0 : 0 ≤ b := le_trans (hf x (τ₀ x)).1 (hf x (τ₀ x)).2
    have hg0 : ∀ τ : Fin n → Fin q, 0 ≤ ∏ w ∈ W, f w (τ w) :=
      fun τ => Finset.prod_nonneg (fun w _ => (hf w (τ w)).1)
    have hgb : ∀ τ : Fin n → Fin q, ∏ w ∈ W, f w (τ w) ≤ b ^ W.card := by
      intro τ
      calc ∏ w ∈ W, f w (τ w) ≤ ∏ w ∈ W, b :=
            Finset.prod_le_prod (fun w _ => (hf w (τ w)).1) (fun w _ => (hf w (τ w)).2)
        _ = b ^ W.card := Finset.prod_const b
    have hcov := ck_cov_le hμ (A := {x}) (B := W) (Finset.disjoint_singleton_left.2 hx)
      (fun τ τ' => f x (τ x) * ∏ w ∈ W, f w (τ' w))
      (fun τ₁ τ₂ τ₁' τ₂' h1 h2 => by
        rw [h1 x (Finset.mem_singleton_self x)]
        congr 1
        exact Finset.prod_congr rfl (fun w hw => by rw [h2 w hw]))
      (C := b ^ W.card * b)
      (fun τ τ' => by
        rw [abs_of_nonneg (mul_nonneg (hf x (τ x)).1 (hg0 τ')), mul_comm (b ^ W.card) b]
        exact mul_le_mul (hf x (τ x)).2 (hgb τ') (hg0 τ') hb0)
    have hprod : ∑ τ, ∑ τ', μ τ * μ τ' * (f x (τ x) * ∏ w ∈ W, f w (τ' w)) =
        (∑ τ, μ τ * f x (τ x)) * ∑ τ, μ τ * ∏ w ∈ W, f w (τ w) := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun τ' _ => ?_))
      ring
    rw [hprod, ← mul_assoc] at hcov
    have hmx0 : 0 ≤ ∑ τ, μ τ * f x (τ x) :=
      Finset.sum_nonneg (fun τ _ => mul_nonneg (hμ.1 τ) (hf x (τ x)).1)
    have hmxb : ∑ τ, μ τ * f x (τ x) ≤ b := by
      calc ∑ τ, μ τ * f x (τ x) ≤ ∑ τ, μ τ * b :=
            Finset.sum_le_sum (fun τ _ => mul_le_mul_of_nonneg_left (hf x (τ x)).2 (hμ.1 τ))
        _ = b := by rw [← Finset.sum_mul, hμ.2, one_mul]
    have hIW : ∑ w ∈ W, Real.sqrt (ckMI μ {w} (W.erase w) ∅) ≤
        ∑ w ∈ W, Real.sqrt (ckMI μ {w} ((insert x W).erase w) ∅) :=
      Finset.sum_le_sum (fun w _ => Real.sqrt_le_sqrt
        (ck_MI_mono hμ {w} (Finset.erase_subset_erase w (Finset.subset_insert x W)) ∅))
    have hstep := CKInfoB_step hcov ih hmx0 hmxb hIW (by positivity)
    simp_rw [Finset.prod_insert hx]
    rw [Finset.card_insert_of_notMem hx, Finset.sum_insert hx, Finset.erase_insert hx, pow_succ]
    simp only [mul_assoc] at hstep ⊢
    exact hstep

/-- Lemma 1.7(c): for `v ≠ w`, `|⟨M(τ_v, τ_w)⟩_μ - μ_vᵀ M μ_w| ≤ 2 m₊ √I(τ_v; τ_w)`. -/
theorem ck_pair_decorr {n q : ℕ} {t : ℝ} (hp : CKPar q t) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) {v w : Fin n} (hvw : v ≠ w) :
    |∑ τ, μ τ * rsM q t (τ v) (τ w) - betheE q t (ckMarg μ v) (ckMarg μ w)| ≤
      2 * ckMp t * Real.sqrt (ckMI μ {v} {w} ∅) := by
  have hdisj : Disjoint ({v} : Finset (Fin n)) {w} := Finset.disjoint_singleton.2 hvw
  have hM : ∀ a b : Fin q, |rsM q t a b| ≤ ckMp t := by
    intro a b
    have h1 := ck_rsM_mem hp a b
    have h2 := (ck_const_bounds hp).1
    rw [abs_of_pos (lt_of_lt_of_le h2 h1.1)]
    exact h1.2
  have hcov := ck_cov_le hμ hdisj (fun τ τ' => rsM q t (τ v) (τ' w))
    (fun τ₁ τ₂ τ₁' τ₂' h1 h2 => by
      rw [h1 v (Finset.mem_singleton_self v), h2 w (Finset.mem_singleton_self w)])
    (C := ckMp t) (fun τ τ' => hM (τ v) (τ' w))
  -- sums of functions of one coordinate are sums against the marginal
  have hmarg : ∀ (u : Fin n) (h : Fin q → ℝ), ∑ τ, μ τ * h (τ u) = ∑ a, ckMarg μ u a * h a := by
    intro u h
    rw [← Finset.sum_fiberwise Finset.univ (fun τ => τ u) (fun τ => μ τ * h (τ u))]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold ckMarg
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun τ hτ => ?_)
    rw [(Finset.mem_filter.1 hτ).2]
  have hE : ∑ τ, ∑ τ', μ τ * μ τ' * rsM q t (τ v) (τ' w) =
      betheE q t (ckMarg μ v) (ckMarg μ w) := by
    have h1 : ∀ τ : Fin n → Fin q, ∑ τ', μ τ * μ τ' * rsM q t (τ v) (τ' w) =
        μ τ * betheMvec q t (ckMarg μ w) (τ v) := by
      intro τ
      have h2 := hmarg w (fun b => rsM q t (τ v) b)
      unfold betheMvec
      calc ∑ τ', μ τ * μ τ' * rsM q t (τ v) (τ' w)
          = μ τ * ∑ τ', μ τ' * rsM q t (τ v) (τ' w) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun τ' _ => by ring)
        _ = μ τ * ∑ b, rsM q t (τ v) b * ckMarg μ w b := by
            rw [h2]
            congr 1
            exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
    rw [Finset.sum_congr rfl (fun τ _ => h1 τ), hmarg v (fun a => betheMvec q t (ckMarg μ w) a)]
    rfl
  rw [hE] at hcov
  exact hcov

end

end ERZeroFreeness
