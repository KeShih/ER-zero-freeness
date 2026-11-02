/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.VBSignCount
import ERZeroFreeness.Bonferroni
import ERZeroFreeness.Poisson

/-! # `VBCycleMoments`: part of Theorem 1.5 (`thm:ising-applications`), zero-freeness

Proof plans for the statements of this module: `docs/ising-vb/blueprint.md`, section
"Module `VBCycleMoments`" (and Appendix A for proofs already checked).  Frozen statements carry their
blueprint item numbers in the comments. -/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### VF0: helpers

For a general exponent vector `k : Fin r → ℕ` and a sign pattern `s`, the summand of
`sgExp_prod_sgDescFactorial` is `F(Φ) = [∀ i, Φ i injective] p^{|UΦ|} π_s(Φ)`, where `π_s(Φ)` is the
proportion of sign vectors under which the cycles of `Φ` carry the signs `s`.  Lifting to
cyclic sequences (`CycMom.sum_lift`), the vertex-disjoint families give
`(n)_L p^L 2^{-K}` (`card_sign_pattern`), and the others at most `CycMom.Rem`. -/

/-- The proportion `π_s(Φ)` of sign vectors under which the cycles `Φ i x` have signs `s i x`. -/
private def VBCycleMoments_pr {n r : ℕ} {k : Fin r → ℕ} (s : (i : Fin r) → Fin (k i) → Bool)
    (Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i) : ℝ :=
  ((Finset.univ.filter fun J : Sym2 (Fin n) → Bool =>
      ∀ i x, cycSign J (Φ i x) = boolSign (s i x)).card : ℝ) /
    2 ^ Fintype.card (Sym2 (Fin n))

private lemma VBCycleMoments_pr_nonneg {n r : ℕ} {k : Fin r → ℕ}
    (s : (i : Fin r) → Fin (k i) → Bool) (Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i) :
    0 ≤ VBCycleMoments_pr s Φ := by
  unfold VBCycleMoments_pr
  positivity

private lemma VBCycleMoments_pr_le_one {n r : ℕ} {k : Fin r → ℕ}
    (s : (i : Fin r) → Fin (k i) → Bool) (Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i) :
    VBCycleMoments_pr s Φ ≤ 1 := by
  unfold VBCycleMoments_pr
  rw [div_le_one (by positivity)]
  have h1 := Finset.card_filter_le (Finset.univ : Finset (Sym2 (Fin n) → Bool))
    (fun J => ∀ i x, cycSign J (Φ i x) = boolSign (s i x))
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at h1
  exact_mod_cast h1

/-- On vertex-disjoint families the cycle signs are independent fair coins. -/
private lemma VBCycleMoments_pr_flat {n r : ℕ} {k : Fin r → ℕ}
    (s : (i : Fin r) → Fin (k i) → Bool) (Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i)
    (h : Function.Injective (CycMom.flat Ψ)) :
    VBCycleMoments_pr s (CycMom.mkΨ Ψ) = ((2 : ℝ) ^ (∑ i, k i))⁻¹ := by
  have hE : ∀ ix : (Σ i : Fin r, Fin (k i)), ((CycMom.mkΨ Ψ ix.1 ix.2).edges).Nonempty := by
    intro ix
    change (CycSeq.edges (Ψ ix.1 ix.2)).Nonempty
    simp [CycSeq.edges, Finset.univ_nonempty]
  have key : ∀ z w : CycMom.Idx r k, CycMom.flat Ψ z = CycMom.flat Ψ w →
      (⟨z.1, z.2.1⟩ : Σ i : Fin r, Fin (k i)) = ⟨w.1, w.2.1⟩ := by
    intro z w hzw
    rw [h hzw]
  have hdisj : Pairwise fun ix jy : (Σ i : Fin r, Fin (k i)) =>
      Disjoint (CycMom.mkΨ Ψ ix.1 ix.2).edges (CycMom.mkΨ Ψ jy.1 jy.2).edges := by
    intro ix jy hne
    rw [Finset.disjoint_left]
    intro e he he'
    change e ∈ CycSeq.edges (Ψ ix.1 ix.2) at he
    change e ∈ CycSeq.edges (Ψ jy.1 jy.2) at he'
    simp only [CycSeq.edges, Finset.mem_image, Finset.mem_univ, true_and] at he he'
    obtain ⟨u, rfl⟩ := he
    obtain ⟨v, hv⟩ := he'
    apply hne
    rw [Sym2.eq_iff] at hv
    rcases hv with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (key ⟨jy.1, (jy.2, v)⟩ ⟨ix.1, (ix.2, u)⟩ h1).symm
    · exact (key ⟨jy.1, (jy.2, v)⟩ ⟨ix.1, (ix.2, u + 1)⟩ h1).symm
  have hc := card_sign_pattern (α := Sym2 (Fin n))
    (fun ix : (Σ i : Fin r, Fin (k i)) => (CycMom.mkΨ Ψ ix.1 ix.2).edges) hE hdisj
    (fun ix => s ix.1 ix.2)
  have hι : Fintype.card (Σ i : Fin r, Fin (k i)) = ∑ i, k i := by
    simp [Fintype.card_sigma]
  rw [hι] at hc
  set c := (Finset.univ.filter fun J : Sym2 (Fin n) → Bool =>
    ∀ i x, cycSign J (CycMom.mkΨ Ψ i x) = boolSign (s i x)).card with hcdef
  have hc2 : c * 2 ^ (∑ i, k i) = 2 ^ Fintype.card (Sym2 (Fin n)) := by
    rw [hcdef]
    convert hc using 3
    ext J
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sigma.forall]
    rfl
  unfold VBCycleMoments_pr
  rw [← hcdef]
  have hc' : (c : ℝ) * 2 ^ (∑ i, k i) = 2 ^ Fintype.card (Sym2 (Fin n)) := by
    exact_mod_cast hc2
  rw [← hc']
  have h2 : (2 : ℝ) ^ (∑ i, k i) ≠ 0 := by positivity
  have hc0 : (c : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hc'
    exact (pow_ne_zero _ two_ne_zero) hc'.symm
  field_simp

/-- The summand `F(Φ) = [∀ i, Φ i injective] p^{|UΦ|} π_s(Φ)` of
`sgExp_prod_sgDescFactorial`. -/
private def VBCycleMoments_F {n r : ℕ} {k : Fin r → ℕ} (p : ℝ)
    (s : (i : Fin r) → Fin (k i) → Bool) (Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i) : ℝ :=
  if ∀ i, Function.Injective (Φ i) then p ^ (CycMom.UΦ Φ).card * VBCycleMoments_pr s Φ else 0

/-- The contribution of the families of cyclic sequences that are not vertex-disjoint. -/
private def VBCycleMoments_R (n : ℕ) (p : ℝ) (r : ℕ) (k : Fin r → ℕ)
    (s : (i : Fin r) → Fin (k i) → Bool) : ℝ :=
  ∑ Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i,
    if Function.Injective (CycMom.flat Ψ) then 0 else VBCycleMoments_F p s (CycMom.mkΨ Ψ)

private lemma VBCycleMoments_R_nonneg (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (r : ℕ) (k : Fin r → ℕ)
    (s : (i : Fin r) → Fin (k i) → Bool) : 0 ≤ VBCycleMoments_R n p r k s := by
  unfold VBCycleMoments_R
  refine Finset.sum_nonneg fun Ψ _ => ?_
  unfold VBCycleMoments_F
  have h0 := VBCycleMoments_pr_nonneg s (CycMom.mkΨ Ψ)
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (pow_nonneg hp _) h0
  · exact le_rfl

private lemma VBCycleMoments_R_le (n : ℕ) {p : ℝ} (hp : 0 ≤ p) (r : ℕ) (k : Fin r → ℕ)
    (s : (i : Fin r) → Fin (k i) → Bool) : VBCycleMoments_R n p r k s ≤ CycMom.Rem n p r k := by
  unfold VBCycleMoments_R CycMom.Rem
  refine Finset.sum_le_sum fun Ψ _ => ?_
  unfold VBCycleMoments_F
  have h1 := VBCycleMoments_pr_le_one s (CycMom.mkΨ Ψ)
  by_cases hf : Function.Injective (CycMom.flat Ψ)
  · rw [if_pos hf, if_neg (fun h => h.1 hf)]
  · rw [if_neg hf]
    by_cases hi : ∀ i, Function.Injective (CycMom.mkΨ Ψ i)
    · rw [if_pos hi, if_pos ⟨hf, hi⟩]
      exact mul_le_of_le_one_right (pow_nonneg hp _) h1
    · rw [if_neg hi, if_neg (fun h => hi h.2)]

/-- `M · ∑_Φ F(Φ) = (n)_L p^L 2^{-K} + R` with `M = ∏_i (2(i+3))^{k_i}`. -/
private lemma VBCycleMoments_main (n : ℕ) (p : ℝ) (r : ℕ) (k : Fin r → ℕ)
    (s : (i : Fin r) → Fin (k i) → Bool) :
    (∏ i : Fin r, (2 * ((i : ℝ) + 3)) ^ k i) *
        ∑ Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i, VBCycleMoments_F p s Φ =
      (n.descFactorial (Fintype.card (CycMom.Idx r k)) : ℝ) * p ^ Fintype.card (CycMom.Idx r k) *
        ((2 : ℝ) ^ (∑ i, k i))⁻¹ + VBCycleMoments_R n p r k s := by
  rw [← CycMom.sum_lift (V := Fin n) (r := r) (k := k) (VBCycleMoments_F p s)]
  have hsplit : ∀ Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i,
      VBCycleMoments_F p s (CycMom.mkΨ Ψ) =
        (if Function.Injective (CycMom.flat Ψ) then
          p ^ Fintype.card (CycMom.Idx r k) * ((2 : ℝ) ^ (∑ i, k i))⁻¹ else 0) +
        (if Function.Injective (CycMom.flat Ψ) then 0
          else VBCycleMoments_F p s (CycMom.mkΨ Ψ)) := by
    intro Ψ
    by_cases h : Function.Injective (CycMom.flat Ψ)
    · rw [if_pos h, if_pos h, add_zero, VBCycleMoments_F,
        if_pos (CycMom.mkΨ_injective_of_flat Ψ h), CycMom.card_UΦ_of_flat Ψ h,
        VBCycleMoments_pr_flat s Ψ h]
    · rw [if_neg h, if_neg h, zero_add]
  have hcard : (Finset.univ.filter fun Ψ : (i : Fin r) → Fin (k i) → CycSeq (Fin n) i =>
      Function.Injective (CycMom.flat Ψ)).card =
        n.descFactorial (Fintype.card (CycMom.Idx r k)) := by
    have h := CycMom.card_filter_flat_injective (V := Fin n) r k
    rw [Fintype.card_fin] at h
    convert h
  rw [Finset.sum_congr rfl (fun Ψ _ => hsplit Ψ), Finset.sum_add_distrib, Finset.sum_ite,
    Finset.sum_const_zero, add_zero, Finset.sum_const, hcard, nsmul_eq_mul]
  unfold VBCycleMoments_R
  ring

/-- The general form of VF0: `∑_Φ F(Φ) → 2^{-K} ∏_i λ_i^{k_i}` for any sign pattern `s`. -/
private lemma VBCycleMoments_tendsto {d : ℝ} (hd : 0 < d) (r : ℕ) (k : Fin r → ℕ)
    (s : (i : Fin r) → Fin (k i) → Bool) :
    Tendsto (fun n : ℕ => ∑ Φ : (i : Fin r) → Fin (k i) → Cyc (Fin n) i,
        VBCycleMoments_F (d / n) s Φ)
      atTop (𝓝 ((∏ i : Fin r, cycleMean d i ^ k i) * ((2 : ℝ) ^ (∑ i, k i))⁻¹)) := by
  set L := Fintype.card (CycMom.Idx r k) with hL
  set M : ℝ := ∏ i : Fin r, (2 * ((i : ℝ) + 3)) ^ k i with hM
  set T : ℝ := ((2 : ℝ) ^ (∑ i, k i))⁻¹ with hT
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (by positivity)
  rw [CycMom.prod_cycleMean_pow]
  have hA := CycMom.tendsto_descFactorial_mul_pow d L
  have hR : Tendsto (fun n : ℕ => VBCycleMoments_R n (d / n) r k s) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun n : ℕ => d * ((L : ℝ) ^ L * Real.exp d) / n)
    · filter_upwards with n
      exact VBCycleMoments_R_nonneg n (by positivity) r k s
    · filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈d⌉₊] with n hn hnd
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hnd)
      have hp0 : 0 ≤ d / n := by positivity
      have hp1 : d / n ≤ 1 := (div_le_one hn0).2 hdn
      calc VBCycleMoments_R n (d / n) r k s ≤ CycMom.Rem n (d / n) r k :=
            VBCycleMoments_R_le n hp0 r k s
        _ ≤ d / n * ((L : ℝ) ^ L * (d / n + 1) ^ n) := CycMom.Rem_le hp0 hp1 r k
        _ ≤ d / n * ((L : ℝ) ^ L * Real.exp d) := by
            gcongr
            exact CycMom.one_add_div_pow_le_exp hd.le (by omega)
        _ = _ := by ring
    · exact tendsto_const_div_atTop_nhds_zero_nat _
  have hlim := ((hA.mul_const T).add hR).const_mul M⁻¹
  rw [show M⁻¹ * (d ^ L + 0) * T = M⁻¹ * (d ^ L * T + 0) by ring]
  refine hlim.congr fun n => ?_
  rw [← VBCycleMoments_main n (d / n) r k s, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]

-- [VF0] joint factorial moments of `(C^+_ℓ, C^-_ℓ)` converge to those of independent
-- `Pois(d^ℓ/(4ℓ))` (general exponents `a, b`; the analytic core of VF1).
theorem tendsto_sgExp_prod_descFactorial {d : ℝ} (hd : 0 < d) (r : ℕ) (a b : Fin r → ℕ) :
    Tendsto (fun n : ℕ => sgExp n (d / n) fun G J =>
        ∏ i : Fin r, ((sgCycleCount G J i true).descFactorial (a i) : ℝ) *
          ((sgCycleCount G J i false).descFactorial (b i) : ℝ))
      atTop (𝓝 (∏ i : Fin r, (cycleMean d i / 2) ^ (a i + b i))) := by
  have h := VBCycleMoments_tendsto hd r (fun i => a i + b i) (fun i x => decide (x.1 < a i))
  have hlim : ∏ i : Fin r, (cycleMean d i / 2) ^ (a i + b i) =
      (∏ i : Fin r, cycleMean d i ^ (a i + b i)) * ((2 : ℝ) ^ (∑ i, (a i + b i)))⁻¹ := by
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_pow, div_eq_mul_inv]
  rw [hlim]
  refine h.congr fun n => ?_
  rw [sgExp_prod_sgDescFactorial]
  rfl

-- [VF1] the same in the `Fin (r + r)` layout of `sgCycleCounts` (input of `Bonferroni`).
theorem tendsto_sgExp_sgCycle_descFactorial {d : ℝ} (hd : 0 < d) (r : ℕ)
    (k : Fin (r + r) → ℕ) :
    Tendsto (fun n : ℕ => sgExp n (d / n)
        fun G J => ∏ i, ((sgCycleCounts r G J i).descFactorial (k i) : ℝ))
      atTop (𝓝 (∏ i, sgCycleMeans d r i ^ k i)) := by
  have h1 : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (J : Sym2 (Fin n) → Bool),
      ∏ i, ((sgCycleCounts r G J i).descFactorial (k i) : ℝ) =
        ∏ i : Fin r, ((sgCycleCount G J i true).descFactorial (k (Fin.castAdd r i)) : ℝ) *
          ((sgCycleCount G J i false).descFactorial (k (Fin.natAdd r i)) : ℝ) := by
    intro n G J
    rw [Fin.prod_univ_add, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sgCycleCounts, Fin.append_left, Fin.append_right]
  have h2 : ∏ i, sgCycleMeans d r i ^ k i =
      ∏ i : Fin r, (cycleMean d i / 2) ^ (k (Fin.castAdd r i) + k (Fin.natAdd r i)) := by
    rw [Fin.prod_univ_add, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sgCycleMeans, Fin.append_left, Fin.append_right, pow_add]
  simp_rw [h1]
  rw [h2]
  exact tendsto_sgExp_prod_descFactorial hd r (fun i => k (Fin.castAdd r i))
    (fun i => k (Fin.natAdd r i))

/-- For `n ≥ d` the signed weights are nonnegative. -/
private lemma VBCycleMoments_weight_nonneg {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, ∀ GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool),
      0 ≤ sgWeight n (d / n) GJ.1 GJ.2 := by
  filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn GJ
  have hdn : d ≤ (n : ℝ) := (Nat.le_ceil d).trans (by exact_mod_cast hn)
  obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
  exact sgWeight_nonneg h0 h1 GJ.1 GJ.2

/-- The signed Poisson means are nonnegative. -/
private lemma VBCycleMoments_means_nonneg {d : ℝ} (hd : 0 ≤ d) (r : ℕ) :
    ∀ i : Fin (r + r), 0 ≤ sgCycleMeans d r i := by
  have h : ∀ i : Fin r, 0 ≤ cycleMean d i / 2 := fun i => by
    unfold cycleMean
    positivity
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [sgCycleMeans, Fin.append_left]
    exact h i
  · rw [sgCycleMeans, Fin.append_right]
    exact h i

-- [VF2] `(C^+_ℓ, C^-_ℓ)_{3 ≤ ℓ ≤ r+2} → (P^+_ℓ, P^-_ℓ)` in law (mass functions on `ℕ^{r+r}`).
theorem sgCycleCounts_tendsto_poisson {d : ℝ} (hd : 0 < d) (r : ℕ) (x : Fin (r + r) → ℕ) :
    Tendsto (fun n : ℕ => sgProb n (d / n) {GJ | sgCycleCounts r GJ.1 GJ.2 = x}) atTop
      (𝓝 (poisProd (sgCycleMeans d r) x)) := by
  have h := tendsto_prob_eq_of_factorial_moments
    (Ω := fun n => SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))
    (fun n GJ => sgWeight n (d / n) GJ.1 GJ.2) (VBCycleMoments_weight_nonneg hd)
    (fun n GJ => sgCycleCounts r GJ.1 GJ.2) (VBCycleMoments_means_nonneg hd.le r)
    (fun k => by
      simpa only [sgExp_eq_sum] using tendsto_sgExp_sgCycle_descFactorial hd r k) x
  refine h.congr fun n => ?_
  rw [sgProb_eq_sum]
  refine Finset.sum_congr rfl fun GJ _ => ?_
  by_cases hx : sgCycleCounts r GJ.1 GJ.2 = x <;> simp [hx]

-- [VF3] the limsup form used by the transfer.
theorem eventually_sgProb_sgCycleCounts_mem_le {d : ℝ} (hd : 0 < d) (r : ℕ)
    (B : Set (Fin (r + r) → ℕ)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, sgProb n (d / n) {GJ | sgCycleCounts r GJ.1 GJ.2 ∈ B} ≤
      poisProb (sgCycleMeans d r) B + η := by
  have htot : Tendsto (fun n : ℕ => ∑ GJ : SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool),
      sgWeight n (d / n) GJ.1 GJ.2) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr fun n => ?_
    rw [Fintype.sum_prod_type, sum_sgWeight]
  have hconv := fun x => sgCycleCounts_tendsto_poisson hd r x
  have h := eventually_sum_mem_le (Ω := fun n => SimpleGraph (Fin n) × (Sym2 (Fin n) → Bool))
    (fun n GJ => sgWeight n (d / n) GJ.1 GJ.2) (VBCycleMoments_weight_nonneg hd) htot
    (fun n GJ => sgCycleCounts r GJ.1 GJ.2) (VBCycleMoments_means_nonneg hd.le r)
    (fun x => (hconv x).congr fun n => by
      rw [sgProb_eq_sum]
      refine Finset.sum_congr rfl fun GJ _ => ?_
      by_cases hx : sgCycleCounts r GJ.1 GJ.2 = x <;> simp [hx]) B hη
  refine h.mono fun n hn => ?_
  rw [sgProb_eq_sum]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun GJ _ => ?_) hn
  by_cases hx : sgCycleCounts r GJ.1 GJ.2 ∈ B <;> simp [hx]

end

end ERZeroFreeness
