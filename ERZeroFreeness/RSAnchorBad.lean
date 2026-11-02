/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSAnchorHolder
import ERZeroFreeness.RSCount

/-!
# Appendix C, Lemma C.7, Steps 3–4: correlated pairs and `eq:rs-bad`

At a real anchor `x` (`t = t(x)`, `F = F_G(x)`, `μ_G(σ) = q^{-n} w_G(σ)/F`) and with
`𝒞 = {(σ,τ) : ‖R_{σ,τ} - αβᵀ‖_F² ≥ η²/4}`:

* `rs_corr_mass` (end of Step 3): there is `c₀ > 0` (depending on `q, d, Δ, η` only) such that for
  every `x ∈ (0,1)` satisfying the upper half of `eq:rs-input` at density `d + Δ`, some `c_x > 0`
  with `c_x ≥ c₀/ℓ²` when `x ≤ 1/2` satisfies, for large `n`,
  `E_{𝖯_d}[F Pr_{μ_G^{⊗2}}[𝒞]] ≤ e^{-c_x n}` (with `c_x = hλψ_x/8`, as in the paper);
* `rs_bad` (**`eq:rs-bad`**, `x ∈ (0,1)`): `E_{𝖯_d} Y ≤ e^{-γ_x n}` for large `n`, with
  `γ_x ∈ (0,1]` and `γ_x ≥ c₁/ℓ²` for `x ≤ 1/2`, `c₁ > 0` uniform in `x`;
* `rs_bad_one` (**`eq:rs-bad`**, `x = 1`): the same bound with some `γ₁ ∈ (0,1]`; there `F ≡ 1`,
  `μ_G` is uniform and `E Y` is the probability of `‖R_{σ,τ} - R̄‖_F ≥ η` for independent
  uniform `σ, τ`.

## Proof

The proofs follow Steps 3–4 and the case `x = 1` of the paper's proof of Lemma C.7, with two
changes: AM–GM replaces Cauchy–Schwarz at the end of Step 3, and the counting bounds
`rs_card_devSq_le`, `rs_card_ovDev_le` replace Hoeffding's inequality.
* `rs_corr_mass`: with `λ_x = min(1/3, ψ_x/(2C_t))` and `h_x = min(1/ℓ, λ_xψ_x/(2C'_⋆ℓ²))`, the last
  two terms of the bracket in `rs_J_id` are each `≤ λ_xψ_x n/2`, and eventually
  `f̄_n ≤ λ_xψ_x n/2` (`rs_fbar_eventually_le`); hence `Ξ ≤ e^{-h_xλ_xψ_x n/4}` (`h_x ≤ 1`).  Then
  the pointwise AM–GM `1 ≤ (c e^{κ_Δ(σ)} + c⁻¹ e^{-κ_Δ(σ)})/2` gives
  `E[F Pr[𝒞]] ≤ (cΞ + c⁻¹ E_{𝖯_d}[q^{-n} ∑_σ w_G(σ) e^{-κ_Δ(σ)}])/2` and the last expectation is
  `E_σ e^{κ_d - κ_Δ} = E_σ e^{κ_{d-Δ}} ≤ 1` (`rs_one_tilt_pt`, `Δ ≤ d`, `t ≤ 0`); take
  `c = e^{h_xλ_xψ_x n/8}`, so `c_x = h_xλ_xψ_x/8`.  For `x ≤ 1/2`, `|t| ≥ 1/(2q-1)`
  (`rs_tRe_le_half`) gives `ψ_x ≥ ψ_0`, `λ_x ≥ λ_0`, `h_x ≥ h_0/ℓ²` (`ℓ ≥ 1`).
* `rs_bad`: `‖R - R̄‖_F² ≤ 2‖R - αβᵀ‖_F² + 4‖α - u‖² + 4‖β - u‖²` (squared triangle inequality,
  `∑ β² ≤ 1`), so `‖R - R̄‖_F² ≥ η²` forces `(σ,τ) ∈ 𝒞` or `‖α - u‖² ≥ η²/16` or `‖β - u‖² ≥ η²/16`;
  hence `Y ≤ F Pr[𝒞] + 2 q^{-n} ∑_{‖α(σ)-u‖² ≥ η²/16} w_G(σ)`.  Take expectations with
  `rs_corr_mass`, `rs_marginal` and `rs_card_devSq_le` (rate `r`), and set `γ_x = min(c_x, r)/2`.
* `rs_bad_one`: `tRe q 1 = 0`, so `rsM = 1`, `w ≡ 1`, `F ≡ 1`, `Y = q^{-2n} #{‖R - R̄‖_F² ≥ η²}`;
  `rs_card_ovDev_le` and `rs_poisPiExp_const`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSAnchorBadAux

/-! ### Pointwise facts at a real anchor -/

theorem rsab_rsW_nonneg {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (N : RSGraph n) (σ : Fin n → Fin q) : 0 ≤ rsW q (tRe q x) N σ :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (hx0.le.trans (rs_rsM_mem hq hx0.le hx1 _ _).1) _

theorem rsab_rsF_pos {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (N : RSGraph n) : 0 < rsF q (tRe q x) N :=
  lt_of_lt_of_le (pow_pos hx0 _) (rs_rsF_bounds hq hx0 hx1 N).1

theorem rsab_sum_rsW {q n : ℕ} (hq : 1 ≤ q) (t : ℝ) (N : RSGraph n) :
    ∑ σ : Fin n → Fin q, rsW q t N σ = (q : ℝ) ^ n * rsF q t N := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  unfold rsF
  field_simp

/-- `ℓ = log(e/x) ≥ 1` for `x ∈ (0,1]`. -/
theorem rsab_rsEll_ge_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 ≤ rsEll x := by
  unfold rsEll
  rw [Real.log_div (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
  have := Real.log_nonpos hx0.le hx1
  linarith

/-- `κ_s(σ) ≤ 0` for `s ≥ 0`, `t ≤ 0`. -/
theorem rsab_rsKappa_nonpos {q n : ℕ} (hq : 1 ≤ q) {s t : ℝ} (hs : 0 ≤ s) (ht : t ≤ 0)
    (σ : Fin n → Fin q) : rsKappa q n s t σ ≤ 0 := by
  unfold rsKappa
  have h := TwoReplicaAux.sum_aa_nonneg (by omega : q ≠ 0) σ
  simp_rw [← rs_rsA_cast_eq_aa] at h
  have h1 : t * ∑ u, ∑ v, ((rsA q (σ u) (σ v) : ℤ) : ℝ) ≤ 0 := by nlinarith
  have h2 : 0 ≤ s / (2 * n) := by positivity
  nlinarith

/-- A pair sum `q^{-2n} ∑_{S} w(σ) w(τ) g / F` with weights `g ∈ [0,1]` lies in `[0, F]`. -/
theorem rsab_pair_sum_le_F {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (N : RSGraph n) (S : Finset ((Fin n → Fin q) × (Fin n → Fin q)))
    (g : (Fin n → Fin q) × (Fin n → Fin q) → ℝ) (hg0 : ∀ st, 0 ≤ g st) (hg1 : ∀ st, g st ≤ 1) :
    0 ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ st ∈ S,
        rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 * g st / rsF q (tRe q x) N ∧
    (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ st ∈ S,
        rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 * g st / rsF q (tRe q x) N ≤
      rsF q (tRe q x) N := by
  have hw := rsab_rsW_nonneg hq hx0 hx1 N
  have hF := rsab_rsF_pos hq hx0 hx1 N
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ : ((q : ℝ) ^ n) ≠ 0 := pow_ne_zero _ hq0
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun st _ =>
      div_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hg0 _)) hF.le)
  · calc _ ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ st : (Fin n → Fin q) × (Fin n → Fin q),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ st ∈ S, rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 * g st /
                rsF q (tRe q x) N ≤
              ∑ st ∈ S, rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N :=
                Finset.sum_le_sum fun st _ => div_le_div_of_nonneg_right
                  (mul_le_of_le_one_right (mul_nonneg (hw _) (hw _)) (hg1 st)) hF.le
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
                (fun st _ _ => div_nonneg (mul_nonneg (hw _) (hw _)) hF.le)
      _ = rsF q (tRe q x) N := by
          rw [← Finset.sum_div, Fintype.sum_prod_type, ← Finset.sum_mul_sum,
            rsab_sum_rsW (by omega)]
          field_simp

/-- Pointwise AM–GM: `1 ≤ (c e^κ + c⁻¹ e^{-κ})/2`. -/
theorem rsab_one_le_amgm {c : ℝ} (hc : 0 < c) (κ : ℝ) :
    1 ≤ (c * Real.exp κ + c⁻¹ * Real.exp (-κ)) / 2 := by
  have ha : 0 < c * Real.exp κ := mul_pos hc (Real.exp_pos κ)
  have hinv : c⁻¹ * Real.exp (-κ) = (c * Real.exp κ)⁻¹ := by rw [Real.exp_neg, mul_inv]
  rw [hinv]
  set a := c * Real.exp κ
  have key : a + a⁻¹ - 2 = (a - 1) ^ 2 / a := by field_simp; ring
  have : 0 ≤ (a - 1) ^ 2 / a := by positivity
  linarith

/-- **AM–GM instead of Cauchy–Schwarz** (end of Step 3): for every `c > 0`,
`E_{𝖯_d}[F Pr_{μ_G^{⊗2}}[𝒞]] ≤ (c Ξ + c⁻¹)/2` with
`Ξ = E_{𝖯_d}[F ∑_{(σ,τ) ∈ 𝒞} μ_G(σ) μ_G(τ) e^{κ_Δ(σ)}]`, using
`E_{𝖯_d}[q^{-n} ∑_σ w_G(σ) e^{-κ_Δ(σ)}] = E_σ e^{κ_{d-Δ}(σ)} ≤ 1`. -/
theorem rsab_corr_amgm {q n : ℕ} (hq : 3 ≤ q) {x d Δ η : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hd : 0 ≤ d) (hΔ : 0 ≤ Δ) (hΔd : Δ ≤ d) {c : ℝ} (hc : 0 < c) :
    rsExp n d (fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) ≤
      (c * rsExp n d (fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 *
              Real.exp (rsKappa q n Δ (tRe q x) st.1) / rsF q (tRe q x) N) + c⁻¹) / 2 := by
  set t := tRe q x with ht
  set S := Finset.univ.filter
    (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2) with hS
  have hmean : ∀ i, 0 ≤ rsMean n d i := fun i => by unfold rsMean; positivity
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ : ((q : ℝ) ^ n) ≠ 0 := pow_ne_zero _ hq0
  have htn : t ≤ 0 := rs_tRe_nonpos (by omega) hx0.le hx1
  have hκ : ∀ σ : Fin n → Fin q, rsKappa q n Δ t σ ≤ 0 :=
    fun σ => rsab_rsKappa_nonpos (by omega) hΔ htn σ
  set f₁ : RSGraph n → ℝ := fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
    ∑ st ∈ S, rsW q t N st.1 * rsW q t N st.2 / rsF q t N with hf₁
  set f₂ : RSGraph n → ℝ := fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
    ∑ st ∈ S, rsW q t N st.1 * rsW q t N st.2 * Real.exp (rsKappa q n Δ t st.1) /
      rsF q t N with hf₂
  set f₃ : RSGraph n → ℝ := fun N => ((q : ℝ) ^ n)⁻¹ *
    ∑ σ, rsW q t N σ * Real.exp (-rsKappa q n Δ t σ) with hf₃
  -- bounds by `F`
  have hb₁ : ∀ N, |f₁ N| ≤ 1 * (3 / 2 : ℝ) ^ (∑ i, N i) := by
    intro N
    have h := rsab_pair_sum_le_F hq hx0 hx1 N S (fun _ => 1) (fun _ => zero_le_one)
      (fun _ => le_rfl)
    simp only [mul_one] at h
    simp only [hf₁]
    rw [abs_of_nonneg h.1, one_mul]
    exact h.2.trans (rs_rsF_bounds hq hx0 hx1 N).2
  have hb₂ : ∀ N, |f₂ N| ≤ 1 * (3 / 2 : ℝ) ^ (∑ i, N i) := by
    intro N
    have h := rsab_pair_sum_le_F hq hx0 hx1 N S (fun st => Real.exp (rsKappa q n Δ t st.1))
      (fun _ => (Real.exp_pos _).le) (fun st => Real.exp_le_one_iff.2 (hκ st.1))
    simp only [hf₂]
    rw [abs_of_nonneg h.1, one_mul]
    exact h.2.trans (rs_rsF_bounds hq hx0 hx1 N).2
  have hs₁ : Summable fun N => poisPi (rsMean n d) N * f₁ N :=
    rs_summable_poisPi_of_abs_le hmean (by norm_num) hb₁
  have hs₂ : Summable fun N => poisPi (rsMean n d) N * f₂ N :=
    rs_summable_poisPi_of_abs_le hmean (by norm_num) hb₂
  -- the third term
  have hcp : ∀ σ : Fin n → Fin q, ∀ i, 0 ≤ cpMean (fun a b => d * rsM q t a b) σ i :=
    fun σ i => div_nonneg (mul_nonneg hd (hx0.le.trans (rs_rsM_mem hq hx0.le hx1 _ _).1))
      (by positivity)
  have hws : ∀ σ : Fin n → Fin q, HasSum (fun N => poisPi (rsMean n d) N * rsW q t N σ)
      (Real.exp (rsKappa q n d t σ)) := by
    intro σ
    have h := (rs_hasSum_poisPi (hcp σ)).mul_left (Real.exp (rsKappa q n d t σ))
    rw [mul_one] at h
    exact h.congr_fun fun N => rs_one_tilt_pt d t σ N
  have hV : HasSum (fun N => poisPi (rsMean n d) N * f₃ N) (((q : ℝ) ^ n)⁻¹ *
      ∑ σ, Real.exp (rsKappa q n d t σ) * Real.exp (-rsKappa q n Δ t σ)) := by
    have h := (hasSum_sum (s := Finset.univ) fun σ _ =>
      (hws σ).mul_right (Real.exp (-rsKappa q n Δ t σ))).mul_left (((q : ℝ) ^ n)⁻¹)
    refine h.congr_fun fun N => ?_
    simp only [hf₃, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have hV1 : ((q : ℝ) ^ n)⁻¹ *
      ∑ σ, Real.exp (rsKappa q n d t σ) * Real.exp (-rsKappa q n Δ t σ) ≤ 1 := by
    have h1 : ∀ σ : Fin n → Fin q,
        Real.exp (rsKappa q n d t σ) * Real.exp (-rsKappa q n Δ t σ) ≤ 1 := by
      intro σ
      rw [← Real.exp_add, Real.exp_le_one_iff]
      have e : rsKappa q n d t σ + -rsKappa q n Δ t σ = rsKappa q n (d - Δ) t σ := by
        unfold rsKappa; ring
      rw [e]
      exact rsab_rsKappa_nonpos (by omega) (by linarith) htn σ
    calc ((q : ℝ) ^ n)⁻¹ *
          ∑ σ, Real.exp (rsKappa q n d t σ) * Real.exp (-rsKappa q n Δ t σ) ≤
        ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => h1 σ) (by positivity)
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
            Finset.prod_const, nsmul_eq_mul, Nat.cast_pow, mul_one, ne_eq, hQ, not_false_eq_true,
            inv_mul_cancel₀]
  -- pointwise AM–GM
  have hpt : ∀ N, f₁ N ≤ (c * f₂ N + c⁻¹ * f₃ N) / 2 := by
    intro N
    have hwN := rsab_rsW_nonneg hq hx0 hx1 N
    have hF := rsab_rsF_pos hq hx0 hx1 N
    have hF0 : rsF q t N ≠ 0 := hF.ne'
    have step1 : f₁ N ≤ (c * f₂ N + c⁻¹ * ((((q : ℝ) ^ n)⁻¹) ^ 2 *
        ∑ st ∈ S, rsW q t N st.1 * rsW q t N st.2 * Real.exp (-rsKappa q n Δ t st.1) /
          rsF q t N)) / 2 := by
      have e : (c * f₂ N + c⁻¹ * ((((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ S, rsW q t N st.1 * rsW q t N st.2 * Real.exp (-rsKappa q n Δ t st.1) /
            rsF q t N)) / 2 = (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ S, rsW q t N st.1 * rsW q t N st.2 / rsF q t N *
            ((c * Real.exp (rsKappa q n Δ t st.1) + c⁻¹ * Real.exp (-rsKappa q n Δ t st.1)) /
              2) := by
        simp only [hf₂, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun st _ => ?_
        field_simp
      rw [e]
      simp only [hf₁]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine Finset.sum_le_sum fun st _ => ?_
      exact le_mul_of_one_le_right (div_nonneg (mul_nonneg (hwN _) (hwN _)) hF.le)
        (rsab_one_le_amgm hc _)
    have step2 : (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ st ∈ S, rsW q t N st.1 * rsW q t N st.2 *
        Real.exp (-rsKappa q n Δ t st.1) / rsF q t N ≤ f₃ N := by
      calc _ ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ st : (Fin n → Fin q) × (Fin n → Fin q),
            rsW q t N st.1 * rsW q t N st.2 * Real.exp (-rsKappa q n Δ t st.1) / rsF q t N := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun st _ _ => div_nonneg (mul_nonneg (mul_nonneg (hwN _) (hwN _))
                (Real.exp_pos _).le) hF.le)
        _ = f₃ N := by
            have e : ∑ st : (Fin n → Fin q) × (Fin n → Fin q),
                rsW q t N st.1 * rsW q t N st.2 * Real.exp (-rsKappa q n Δ t st.1) / rsF q t N =
                (∑ σ, rsW q t N σ * Real.exp (-rsKappa q n Δ t σ)) * (∑ τ, rsW q t N τ) /
                  rsF q t N := by
              rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_div]
              refine Finset.sum_congr rfl fun σ _ => ?_
              rw [Finset.sum_div]
              refine Finset.sum_congr rfl fun τ _ => ?_
              ring
            rw [e, rsab_sum_rsW (by omega)]
            simp only [hf₃]
            field_simp
    have hc' : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    have := mul_le_mul_of_nonneg_left step2 hc'
    linarith
  -- conclude
  have hH : HasSum (fun N => poisPi (rsMean n d) N * ((c * f₂ N + c⁻¹ * f₃ N) / 2))
      ((c * ∑' N, poisPi (rsMean n d) N * f₂ N + c⁻¹ * (((q : ℝ) ^ n)⁻¹ *
        ∑ σ, Real.exp (rsKappa q n d t σ) * Real.exp (-rsKappa q n Δ t σ))) / 2) := by
    have := ((hs₂.hasSum.mul_left c).add (hV.mul_left c⁻¹)).div_const 2
    refine this.congr_fun fun N => ?_
    ring
  show ∑' N, poisPi (rsMean n d) N * f₁ N ≤ (c * ∑' N, poisPi (rsMean n d) N * f₂ N + c⁻¹) / 2
  calc ∑' N, poisPi (rsMean n d) N * f₁ N ≤
        ∑' N, poisPi (rsMean n d) N * ((c * f₂ N + c⁻¹ * f₃ N) / 2) :=
        Summable.tsum_le_tsum (fun N => mul_le_mul_of_nonneg_left (hpt N)
          (rs_poisPi_nonneg hmean N)) hs₁ hH.summable
    _ = _ := hH.tsum_eq
    _ ≤ _ := by
      have hc' : 0 < c⁻¹ := inv_pos.2 hc
      have := mul_le_mul_of_nonneg_left hV1 hc'.le
      linarith

/-- `F Pr_{μ_G^{⊗2}}[𝒞]` is `𝖯_d`-summable (it lies in `[0, F]`). -/
theorem rsab_corr_summable {q n : ℕ} (hq : 3 ≤ q) {x d η : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hd : 0 ≤ d) :
    Summable fun N => poisPi (rsMean n d) N * ((((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) := by
  have hmean : ∀ i, 0 ≤ rsMean n d i := fun i => by unfold rsMean; positivity
  refine rs_summable_poisPi_of_abs_le hmean (by norm_num : (0 : ℝ) ≤ 3 / 2) (A := 1)
    fun N => ?_
  have h := rsab_pair_sum_le_F hq hx0 hx1 N (Finset.univ.filter
    (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2))
    (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
  simp only [mul_one] at h
  rw [abs_of_nonneg h.1, one_mul]
  exact h.2.trans (rs_rsF_bounds hq hx0 hx1 N).2

/-! ### Step 4: splitting the pairs outside the window -/

/-- `∑_b β_b² ≤ 1` for the colour proportions `β = α(τ)`. -/
theorem rsab_sum_colorFrac_sq_le {n q : ℕ} (τ : Fin n → Fin q) : ∑ b, colorFrac τ b ^ 2 ≤ 1 := by
  have h0 : ∀ b, 0 ≤ colorFrac τ b := fun b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h1 : ∀ b, colorFrac τ b ≤ 1 := by
    intro b
    unfold colorFrac
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [CharP.cast_eq_zero, div_zero, zero_le_one]
    · rw [div_le_one (by exact_mod_cast hn)]
      have : fiberCard τ b ≤ n := by
        unfold fiberCard
        exact (Finset.card_le_univ _).trans (Fintype.card_fin n).le
      exact_mod_cast this
  have hsum : ∑ b, colorFrac τ b ≤ 1 := by
    unfold colorFrac
    rw [← Finset.sum_div]
    have hfc : ∑ b, (fiberCard τ b : ℝ) = n := by
      have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin n)))
        (t := (Finset.univ : Finset (Fin q))) (f := τ)
        (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have h' : ∑ b, fiberCard τ b = n := by
        unfold fiberCard
        convert this.symm
      exact_mod_cast h'
    rw [hfc]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp only [CharP.cast_eq_zero, div_zero, zero_le_one]
    · rw [div_self (by exact_mod_cast hn.ne')]
  calc ∑ b, colorFrac τ b ^ 2 ≤ ∑ b, colorFrac τ b :=
        Finset.sum_le_sum fun b _ => by nlinarith [h0 b, h1 b]
    _ ≤ 1 := hsum

/-- `‖R - R̄‖_F² ≤ 2‖R - αβᵀ‖_F² + 4‖α - u‖² + 4‖β - u‖²`. -/
theorem rsab_ovDev_le {n q : ℕ} (hq : 1 ≤ q) (σ τ : Fin n → Fin q) :
    rsOvDev σ τ ≤ 2 * rsCorrDev σ τ + 4 * rsDevSq σ + 4 * rsDevSq τ := by
  have hβ := rsab_sum_colorFrac_sq_le τ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : ∀ a b, (overlap σ τ a b - 1 / (q : ℝ) ^ 2) ^ 2 ≤
      2 * (overlap σ τ a b - colorFrac σ a * colorFrac τ b) ^ 2 +
        2 * (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2 := by
    intro a b
    nlinarith [sq_nonneg (overlap σ τ a b - colorFrac σ a * colorFrac τ b -
      (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2))]
  have h2 : ∀ a b, (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2 ≤
      2 * (colorFrac σ a - 1 / q) ^ 2 * colorFrac τ b ^ 2 +
        2 * (1 / (q : ℝ)) ^ 2 * (colorFrac τ b - 1 / q) ^ 2 := by
    intro a b
    have e : colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2 =
        (colorFrac σ a - 1 / q) * colorFrac τ b + (1 / q) * (colorFrac τ b - 1 / q) := by
      field_simp; ring
    rw [e]
    nlinarith [sq_nonneg ((colorFrac σ a - 1 / q) * colorFrac τ b -
      (1 / q) * (colorFrac τ b - 1 / q))]
  have hD : 0 ≤ rsDevSq τ := Finset.sum_nonneg fun b _ => sq_nonneg _
  have hrow : ∀ a, ∑ b, (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2 ≤
      2 * (colorFrac σ a - 1 / q) ^ 2 + 2 * (1 / (q : ℝ)) ^ 2 * rsDevSq τ := by
    intro a
    calc ∑ b, (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2 ≤
          ∑ b, (2 * (colorFrac σ a - 1 / q) ^ 2 * colorFrac τ b ^ 2 +
            2 * (1 / (q : ℝ)) ^ 2 * (colorFrac τ b - 1 / q) ^ 2) :=
          Finset.sum_le_sum fun b _ => h2 a b
      _ = 2 * (colorFrac σ a - 1 / q) ^ 2 * ∑ b, colorFrac τ b ^ 2 +
            2 * (1 / (q : ℝ)) ^ 2 * rsDevSq τ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; rfl
      _ ≤ 2 * (colorFrac σ a - 1 / q) ^ 2 + 2 * (1 / (q : ℝ)) ^ 2 * rsDevSq τ := by
          have : 0 ≤ 2 * (colorFrac σ a - 1 / q) ^ 2 := by positivity
          nlinarith
  have hall : ∑ a, ∑ b, (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2 ≤
      2 * rsDevSq σ + 2 * rsDevSq τ := by
    calc _ ≤ ∑ a : Fin q, (2 * (colorFrac σ a - 1 / q) ^ 2 +
            2 * (1 / (q : ℝ)) ^ 2 * rsDevSq τ) := Finset.sum_le_sum fun a _ => hrow a
      _ = 2 * rsDevSq σ + (q : ℝ) * (2 * (1 / (q : ℝ)) ^ 2 * rsDevSq τ) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rfl
      _ ≤ 2 * rsDevSq σ + 2 * rsDevSq τ := by
          have e : (q : ℝ) * (2 * (1 / (q : ℝ)) ^ 2 * rsDevSq τ) = 2 / q * rsDevSq τ := by
            field_simp
          rw [e]
          have : 2 / (q : ℝ) ≤ 2 := by
            rw [div_le_iff₀ hq0]
            have : (1 : ℝ) ≤ q := by exact_mod_cast hq
            linarith
          nlinarith
  calc rsOvDev σ τ ≤ ∑ a, ∑ b, (2 * (overlap σ τ a b - colorFrac σ a * colorFrac τ b) ^ 2 +
        2 * (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h1 a b
    _ = 2 * rsCorrDev σ τ +
          2 * ∑ a, ∑ b, (colorFrac σ a * colorFrac τ b - 1 / (q : ℝ) ^ 2) ^ 2 := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rfl
    _ ≤ _ := by linarith [hall]

/-- `Y = q^{-2n} ∑_{‖R - R̄‖_F² ≥ η²} w(σ) w(τ) / F`. -/
theorem rsab_rsY_eq_sum {q n : ℕ} (η t : ℝ) (N : RSGraph n) :
    rsY q η t N = (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ∑ st ∈ Finset.univ.filter
          (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 ≤ rsOvDev st.1 st.2),
        rsW q t N st.1 * rsW q t N st.2 / rsF q t N := by
  have hF2 : rsF q t N ^ 2 = (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ∑ y : (Fin n → Fin q) × (Fin n → Fin q), rsW q t N y.1 * rsW q t N y.2 := by
    unfold rsF
    rw [Fintype.sum_prod_type, mul_pow, sq (∑ σ : Fin n → Fin q, rsW q t N σ),
      Finset.sum_mul_sum]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset ((Fin n → Fin q) × (Fin n → Fin q)))
    (fun st => rsOvDev st.1 st.2 < η ^ 2) (fun y => rsW q t N y.1 * rsW q t N y.2)
  have hfilt : (Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
      ¬ rsOvDev st.1 st.2 < η ^ 2) =
      Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
        η ^ 2 ≤ rsOvDev st.1 st.2 := Finset.filter_congr fun st _ => not_lt
  rw [hfilt] at hsplit
  unfold rsY rsHR rsWindow
  rw [hF2, ← Finset.sum_div, ← hsplit]
  ring

/-- `Y ≤ F Pr[𝒞] + 2 q^{-n} ∑_{‖α(σ) - u‖² ≥ η²/16} w(σ)`. -/
theorem rsab_rsY_le {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (η : ℝ)
    (N : RSGraph n) :
    rsY q η (tRe q x) N ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N +
        2 * (((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin n → Fin q => η ^ 2 / 16 ≤ rsDevSq σ), rsW q (tRe q x) N σ) := by
  have hw := rsab_rsW_nonneg hq hx0 hx1 N
  have hF := rsab_rsF_pos hq hx0 hx1 N
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hQ : ((q : ℝ) ^ n) ≠ 0 := pow_ne_zero _ hq0
  rw [rsab_rsY_eq_sum]
  set g : (Fin n → Fin q) × (Fin n → Fin q) → ℝ := fun st =>
    rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N with hg
  have hg0 : ∀ st, 0 ≤ g st := fun st => div_nonneg (mul_nonneg (hw _) (hw _)) hF.le
  set M := Finset.univ.filter (fun σ : Fin n → Fin q => η ^ 2 / 16 ≤ rsDevSq σ) with hM
  have key : ∑ st ∈ Finset.univ.filter
        (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 ≤ rsOvDev st.1 st.2), g st ≤
      ∑ st ∈ Finset.univ.filter
        (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2), g st +
      ∑ st ∈ M ×ˢ (Finset.univ : Finset (Fin n → Fin q)), g st +
      ∑ st ∈ (Finset.univ : Finset (Fin n → Fin q)) ×ˢ M, g st := by
    have hp1 : M ×ˢ (Finset.univ : Finset (Fin n → Fin q)) = Finset.univ.filter
        (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 16 ≤ rsDevSq st.1) := by
      ext st
      simp only [hM, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    have hp2 : (Finset.univ : Finset (Fin n → Fin q)) ×ˢ M = Finset.univ.filter
        (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 16 ≤ rsDevSq st.2) := by
      ext st
      simp only [hM, Finset.mem_product, Finset.mem_univ, Finset.mem_filter, true_and]
    rw [hp1, hp2, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun st _ => ?_
    have hov := rsab_ovDev_le (by omega : 1 ≤ q) st.1 st.2
    have hgs := hg0 st
    by_cases h1 : η ^ 2 ≤ rsOvDev st.1 st.2
    · rw [if_pos h1]
      by_cases h2 : η ^ 2 / 4 ≤ rsCorrDev st.1 st.2
      · rw [if_pos h2]; split_ifs <;> linarith
      · by_cases h3 : η ^ 2 / 16 ≤ rsDevSq st.1
        · rw [if_neg h2, if_pos h3]; split_ifs <;> linarith
        · by_cases h4 : η ^ 2 / 16 ≤ rsDevSq st.2
          · rw [if_neg h2, if_neg h3, if_pos h4]; linarith
          · exfalso
            linarith [not_le.1 h2, not_le.1 h3, not_le.1 h4]
    · rw [if_neg h1]
      split_ifs <;> linarith
  have hm1 : ∑ st ∈ M ×ˢ (Finset.univ : Finset (Fin n → Fin q)), g st =
      (q : ℝ) ^ n * ∑ σ ∈ M, rsW q (tRe q x) N σ := by
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hg]
    rw [← Finset.sum_div, ← Finset.mul_sum, rsab_sum_rsW (by omega)]
    field_simp
  have hm2 : ∑ st ∈ (Finset.univ : Finset (Fin n → Fin q)) ×ˢ M, g st =
      (q : ℝ) ^ n * ∑ τ ∈ M, rsW q (tRe q x) N τ := by
    rw [Finset.sum_product_right, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [hg]
    rw [← Finset.sum_div, ← Finset.sum_mul, rsab_sum_rsW (by omega)]
    field_simp
  rw [hm1, hm2] at key
  have key2 := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ (((q : ℝ) ^ n)⁻¹) ^ 2)
  calc _ ≤ _ := key2
    _ = _ := by field_simp; ring

/-! ### The anchor `x = 1` (`t = 0`) -/

theorem rsab_rsW_zero {q n : ℕ} (N : RSGraph n) (σ : Fin n → Fin q) : rsW q (0 : ℝ) N σ = 1 := by
  simp only [rsW, rsM, zero_mul, add_zero, one_pow, Finset.prod_const_one]

theorem rsab_rsF_zero {q n : ℕ} (hq : 1 ≤ q) (N : RSGraph n) : rsF q (0 : ℝ) N = 1 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  simp only [rsF, rsab_rsW_zero, Finset.sum_const, Finset.card_univ, Fintype.card_pi,
    Fintype.card_fin, Finset.prod_const, nsmul_eq_mul, Nat.cast_pow, mul_one, ne_eq,
    pow_eq_zero_iff', hq0, false_and, not_false_eq_true, inv_mul_cancel₀]

theorem rsab_rsY_zero {q n : ℕ} (hq : 1 ≤ q) (η : ℝ) (N : RSGraph n) :
    rsY q η (0 : ℝ) N = (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ((Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
          η ^ 2 ≤ rsOvDev st.1 st.2).card : ℝ) := by
  rw [rsab_rsY_eq_sum]
  simp only [rsab_rsW_zero, rsab_rsF_zero hq, mul_one, div_one, Finset.sum_const, nsmul_eq_mul]

/-! ### Step 3: the choice of `λ` and `h` -/

/-- The choice `λ = min(1/3, ψ/(2C_t))`, `h = min(1/ℓ, λψ/(2C'ℓ²))` and its properties. -/
theorem rsab_rate_choice {ψ Ct Cp ℓ : ℝ} (hψ : 0 < ψ) (hCt : 0 < Ct) (hCp : 0 < Cp) (hℓ : 1 ≤ ℓ) :
    ∃ lam h : ℝ, 0 < lam ∧ lam ≤ 1 / 3 ∧ 0 < h ∧ h ≤ 1 ∧ h * ℓ ≤ 1 ∧
      Cp * h * ℓ ^ 2 ≤ lam * ψ / 2 ∧ Ct * lam ^ 2 ≤ lam * ψ / 2 ∧
      ∀ ψ₀ lam₀ h₀ : ℝ, 0 < ψ₀ → ψ₀ ≤ ψ → lam₀ = min (1 / 3) (ψ₀ / (2 * Ct)) →
        h₀ = min 1 (lam₀ * ψ₀ / (2 * Cp)) → h₀ * lam₀ * ψ₀ / ℓ ^ 2 ≤ h * lam * ψ := by
  have hℓ0 : 0 < ℓ := by linarith
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  obtain ⟨lam, hlam⟩ : ∃ v : ℝ, v = min (1 / 3) (ψ / (2 * Ct)) := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlam]; exact lt_min (by norm_num) (div_pos hψ (by linarith))
  have hlam1 : lam ≤ 1 / 3 := by rw [hlam]; exact min_le_left _ _
  have hlam2 : lam ≤ ψ / (2 * Ct) := by rw [hlam]; exact min_le_right _ _
  obtain ⟨h, hh⟩ : ∃ v : ℝ, v = min (1 / ℓ) (lam * ψ / (2 * Cp * ℓ ^ 2)) := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; exact lt_min (by positivity) (by positivity)
  have hh1 : h ≤ 1 / ℓ := by rw [hh]; exact min_le_left _ _
  have hh2 : h ≤ lam * ψ / (2 * Cp * ℓ ^ 2) := by rw [hh]; exact min_le_right _ _
  refine ⟨lam, h, hlam0, hlam1, hh0, ?_, ?_, ?_, ?_, ?_⟩
  · have : 1 / ℓ ≤ 1 := by rw [div_le_one hℓ0]; exact hℓ
    linarith
  · have := mul_le_mul_of_nonneg_right hh1 hℓ0.le
    rwa [one_div_mul_cancel hℓ0.ne'] at this
  · have := mul_le_mul_of_nonneg_left hh2 (by positivity : 0 ≤ Cp * ℓ ^ 2)
    calc Cp * h * ℓ ^ 2 = Cp * ℓ ^ 2 * h := by ring
      _ ≤ Cp * ℓ ^ 2 * (lam * ψ / (2 * Cp * ℓ ^ 2)) := this
      _ = lam * ψ / 2 := by field_simp
  · have := mul_le_mul_of_nonneg_left hlam2 (by positivity : 0 ≤ Ct * lam)
    calc Ct * lam ^ 2 = Ct * lam * lam := by ring
      _ ≤ Ct * lam * (ψ / (2 * Ct)) := this
      _ = lam * ψ / 2 := by field_simp
  · intro ψ₀ lam₀ h₀ hψ₀ hψψ hlam₀ hh₀
    have hlam₀0 : 0 < lam₀ := by
      rw [hlam₀]; exact lt_min (by norm_num) (div_pos hψ₀ (by linarith))
    have hlamlam : lam₀ ≤ lam := by
      rw [hlam₀, hlam]
      exact min_le_min le_rfl (div_le_div_of_nonneg_right hψψ (by linarith))
    have hh₀0 : 0 < h₀ := by
      rw [hh₀]; exact lt_min one_pos (by positivity)
    have hhh : h₀ / ℓ ^ 2 ≤ h := by
      rw [hh]
      refine le_min ?_ ?_
      · calc h₀ / ℓ ^ 2 ≤ 1 / ℓ ^ 2 :=
              div_le_div_of_nonneg_right (by rw [hh₀]; exact min_le_left _ _) hℓ2.le
          _ ≤ 1 / ℓ := one_div_le_one_div_of_le hℓ0 (by nlinarith)
      · calc h₀ / ℓ ^ 2 ≤ lam₀ * ψ₀ / (2 * Cp) / ℓ ^ 2 :=
              div_le_div_of_nonneg_right (by rw [hh₀]; exact min_le_right _ _) hℓ2.le
          _ ≤ lam * ψ / (2 * Cp) / ℓ ^ 2 := by
              apply div_le_div_of_nonneg_right _ hℓ2.le
              apply div_le_div_of_nonneg_right _ (by linarith)
              exact mul_le_mul hlamlam hψψ hψ₀.le hlam0.le
          _ = lam * ψ / (2 * Cp * ℓ ^ 2) := by rw [div_div]
    calc h₀ * lam₀ * ψ₀ / ℓ ^ 2 = h₀ / ℓ ^ 2 * lam₀ * ψ₀ := by ring
      _ ≤ h * lam * ψ := by
          apply mul_le_mul _ hψψ hψ₀.le (by positivity)
          exact mul_le_mul hhh hlamlam hlam₀0.le hh0.le

end RSAnchorBadAux

open RSAnchorBadAux

/-- **Lemma C.7, end of Step 3.** Correlated pairs carry exponentially small `F`-weighted mass. -/
theorem rs_corr_mass {q : ℕ} (hq : 3 ≤ q) {d Δ η : ℝ} (hd : 0 < d) (hΔ : 0 < Δ) (hΔd : Δ ≤ d)
    (hη : 0 < η) :
    ∃ c₀ > 0, ∀ x : ℝ, 0 < x → x < 1 →
      (∀ ε > 0, ∀ᶠ n : ℕ in atTop, rsExp n (d + Δ)
        (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) ≤ ε * n) →
      ∃ c > 0, (x ≤ 1 / 2 → c₀ / rsEll x ^ 2 ≤ c) ∧
        ∀ᶠ n : ℕ in atTop, rsExp n d (fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) ≤
          Real.exp (-(c * n)) := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h2q : (0 : ℝ) < 2 * (q : ℝ) - 1 := by linarith
  have hCp : (0 : ℝ) < 1 + 3 / 2 * (d + Δ) + 9 / 4 * (d + Δ) ^ 2 := by positivity
  have hCt : (0 : ℝ) < 9 / 2 * Δ := by positivity
  obtain ⟨u, hu⟩ : ∃ v : ℝ, v = 1 / (2 * (q : ℝ) - 1) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; exact div_pos one_pos h2q
  obtain ⟨ψ₀, hψ₀⟩ : ∃ v : ℝ, v = Δ * u ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16 := ⟨_, rfl⟩
  have hψ₀0 : 0 < ψ₀ := by rw [hψ₀]; positivity
  obtain ⟨lam₀, hlam₀⟩ : ∃ v : ℝ, v = min (1 / 3) (ψ₀ / (2 * (9 / 2 * Δ))) := ⟨_, rfl⟩
  have hlam₀0 : 0 < lam₀ := by
    rw [hlam₀]; exact lt_min (by norm_num) (div_pos hψ₀0 (by linarith))
  obtain ⟨h₀, hh₀⟩ : ∃ v : ℝ,
      v = min 1 (lam₀ * ψ₀ / (2 * (1 + 3 / 2 * (d + Δ) + 9 / 4 * (d + Δ) ^ 2))) := ⟨_, rfl⟩
  have hh₀0 : 0 < h₀ := by rw [hh₀]; exact lt_min one_pos (by positivity)
  refine ⟨h₀ * lam₀ * ψ₀ / 8, by positivity, fun x hx0 hx1 hfe => ?_⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ v : ℝ, v = rsEll x := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; exact rsab_rsEll_ge_one hx0 hx1.le
  have htneg : tRe q x < 0 := rs_tRe_neg (by omega) hx0.le hx1
  have ht2 : 0 < tRe q x ^ 2 := by nlinarith
  obtain ⟨ψ, hψ⟩ : ∃ v : ℝ, v = Δ * tRe q x ^ 2 * (q : ℝ) ^ 2 * η ^ 2 / 16 := ⟨_, rfl⟩
  have hψ0 : 0 < ψ := by rw [hψ]; positivity
  obtain ⟨lam, h, hlam0, hlam1, hh0, hh1, hhl, hCph, hCtl, hlow⟩ :=
    rsab_rate_choice hψ0 hCt hCp hℓ1
  refine ⟨h * lam * ψ / 8, by positivity, ?_, ?_⟩
  · -- the rate for `x ≤ 1/2`
    intro hx12
    have htle := rs_tRe_le_half (by omega : 2 ≤ q) hx0.le hx12
    have hut : u ^ 2 ≤ tRe q x ^ 2 := by
      have h1 : u ≤ -tRe q x := by
        have : -1 / (2 * (q : ℝ) - 1) = -u := by rw [hu]; ring
        linarith
      nlinarith
    have hψψ : ψ₀ ≤ ψ := by
      have e : ψ - ψ₀ = Δ * (q : ℝ) ^ 2 * η ^ 2 / 16 * (tRe q x ^ 2 - u ^ 2) := by
        rw [hψ, hψ₀]; ring
      have : 0 ≤ Δ * (q : ℝ) ^ 2 * η ^ 2 / 16 * (tRe q x ^ 2 - u ^ 2) :=
        mul_nonneg (by positivity) (by linarith)
      linarith
    have := hlow ψ₀ lam₀ h₀ hψ₀0 hψψ hlam₀ hh₀
    rw [← hℓ]
    calc h₀ * lam₀ * ψ₀ / 8 / ℓ ^ 2 = h₀ * lam₀ * ψ₀ / ℓ ^ 2 / 8 := by ring
      _ ≤ h * lam * ψ / 8 := by linarith
  · -- the eventual bound
    have hfb := rs_fbar_eventually_le hq hx0 hx1.le (by positivity : 0 ≤ d + Δ) hfe
      (lam * ψ / 2) (by positivity)
    filter_upwards [hfb, Filter.eventually_gt_atTop 0] with n hfbn hn
    obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : ℝ, Ξ = rsExp n d (fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 *
              Real.exp (rsKappa q n Δ (tRe q x) st.1) / rsF q (tRe q x) N) := ⟨_, rfl⟩
    have hhl' : h * rsEll x ≤ 1 := by rw [← hℓ]; exact hhl
    have hJ := rs_J_id (η := η) hq hx0 hx1.le hd.le hΔ.le hn hlam0.le hlam1 hh0 hhl'
    rw [← hΞ, ← hψ, ← hℓ] at hJ
    obtain ⟨B, hB⟩ : ∃ v : ℝ, v = rsFbar q n (d + Δ) (tRe q x) +
        (1 + 3 / 2 * (d + Δ) + 9 / 4 * (d + Δ) ^ 2) * h * ℓ ^ 2 * n +
        9 / 2 * Δ * lam ^ 2 * n := ⟨_, rfl⟩
    rw [← hB] at hJ
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hBle : B ≤ 3 / 2 * (lam * ψ) * n := by
      have e1 := mul_le_mul_of_nonneg_right hCph hn'
      have e2 := mul_le_mul_of_nonneg_right hCtl hn'
      rw [hB]
      linarith
    have hXi : Ξ ≤ Real.exp (-(h * lam * ψ * n / 4)) := by
      have hA := Real.exp_pos (2 * (lam * h / (1 + h)) * ψ * n)
      have h1 : Ξ ≤ Real.exp (h / (1 + h) * B - 2 * (lam * h / (1 + h)) * ψ * n) := by
        rw [Real.exp_sub, le_div_iff₀ hA]
        linarith [hJ]
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have e : h / (1 + h) * B - 2 * (lam * h / (1 + h)) * ψ * n =
          h / (1 + h) * (B - 2 * (lam * ψ) * n) := by ring
      rw [e]
      have hk : h / 2 ≤ h / (1 + h) :=
        div_le_div_of_nonneg_left hh0.le (by linarith) (by linarith)
      have hlpn : 0 ≤ lam * ψ * n := by positivity
      calc h / (1 + h) * (B - 2 * (lam * ψ) * n) ≤ h / 2 * (B - 2 * (lam * ψ) * n) :=
            mul_le_mul_of_nonpos_right hk (by linarith)
        _ ≤ h / 2 * (-(lam * ψ * n / 2)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = -(h * lam * ψ * n / 4) := by ring
    have hamgm := rsab_corr_amgm (η := η) (n := n) hq hx0 hx1.le hd.le hΔ.le hΔd
      (Real.exp_pos (h * lam * ψ * n / 8))
    rw [← hΞ] at hamgm
    have hc8 := Real.exp_pos (h * lam * ψ * n / 8)
    calc _ ≤ _ := hamgm
      _ ≤ (Real.exp (h * lam * ψ * n / 8) * Real.exp (-(h * lam * ψ * n / 4)) +
            (Real.exp (h * lam * ψ * n / 8))⁻¹) / 2 := by
          have := mul_le_mul_of_nonneg_left hXi hc8.le
          linarith
      _ = Real.exp (-(h * lam * ψ / 8 * n)) := by
          rw [← Real.exp_add, ← Real.exp_neg]
          have e1 : h * lam * ψ * n / 8 + -(h * lam * ψ * n / 4) = -(h * lam * ψ / 8 * n) := by
            ring
          have e2 : -(h * lam * ψ * n / 8) = -(h * lam * ψ / 8 * n) := by ring
          rw [e1, e2]
          ring

/-- **`eq:rs-bad` for anchors `x ∈ (0,1)`** (Lemma C.7, Step 4). -/
theorem rs_bad {q : ℕ} (hq : 3 ≤ q) {d Δ η : ℝ} (hd : 0 < d) (hΔ : 0 < Δ) (hΔd : Δ ≤ d)
    (hη : 0 < η) :
    ∃ c₁ > 0, ∀ x : ℝ, 0 < x → x < 1 →
      (∀ ε > 0, ∀ᶠ n : ℕ in atTop, rsExp n (d + Δ)
        (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) ≤ ε * n) →
      ∃ γ > 0, γ ≤ 1 ∧ (x ≤ 1 / 2 → c₁ / rsEll x ^ 2 ≤ γ) ∧
        ∀ᶠ n : ℕ in atTop, rsExp n d (rsY q η (tRe q x)) ≤ Real.exp (-(γ * n)) := by
  obtain ⟨c₀, hc₀, hcorr⟩ := rs_corr_mass hq hd hΔ hΔd hη
  obtain ⟨r, hr, hr1, K, hK, hcard⟩ :=
    rs_card_devSq_le (by omega : 2 ≤ q) (show (0 : ℝ) < η ^ 2 / 16 by positivity)
  refine ⟨min c₀ r / 2, by positivity, fun x hx0 hx1 hfe => ?_⟩
  obtain ⟨c, hc, hclow, hcev⟩ := hcorr x hx0 hx1 hfe
  obtain ⟨γ, hγ⟩ : ∃ v : ℝ, v = min c r / 2 := ⟨_, rfl⟩
  have hγ0 : 0 < γ := by rw [hγ]; positivity
  have hγc : 2 * γ ≤ c := by have := min_le_left c r; linarith
  have hγr : 2 * γ ≤ r := by have := min_le_right c r; linarith
  refine ⟨γ, hγ0, by linarith, ?_, ?_⟩
  · intro hx12
    have hℓ1 := rsab_rsEll_ge_one hx0 hx1.le
    have hℓ2 : 1 ≤ rsEll x ^ 2 := by nlinarith
    have hc' := hclow hx12
    have h1 : min c₀ r / rsEll x ^ 2 ≤ min c r := by
      apply le_min
      · calc min c₀ r / rsEll x ^ 2 ≤ c₀ / rsEll x ^ 2 :=
              div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
          _ ≤ c := hc'
      · calc min c₀ r / rsEll x ^ 2 ≤ r / rsEll x ^ 2 :=
              div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
          _ ≤ r := div_le_self hr.le hℓ2
    calc min c₀ r / 2 / rsEll x ^ 2 = min c₀ r / rsEll x ^ 2 / 2 := by ring
      _ ≤ γ := by rw [hγ]; linarith
  · filter_upwards [hcev, Filter.eventually_ge_atTop (⌈2 * K / γ⌉₊ + 1)] with n hcn hn
    have hn0 : 0 < n := by omega
    have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmean : ∀ i, 0 ≤ rsMean n d i := fun i => by unfold rsMean; positivity
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hQ : (0 : ℝ) < (q : ℝ) ^ n := pow_pos hq0 n
    obtain ⟨hsm, hEm⟩ := rs_marginal hq hd.le hx0.le hx1.le
      (Finset.univ.filter (fun σ : Fin n → Fin q => η ^ 2 / 16 ≤ rsDevSq σ))
    have hsY : Summable fun N => poisPi (rsMean n d) N * rsY q η (tRe q x) N := by
      refine rs_summable_poisPi_of_abs_le hmean (by norm_num : (0 : ℝ) ≤ 3 / 2) (A := 1)
        fun N => ?_
      have hY := rs_rsY_bounds hq hx0 hx1.le η N
      rw [abs_of_nonneg hY.1, one_mul]
      exact hY.2.trans (rs_rsF_bounds hq hx0 hx1.le N).2
    have hsC := rsab_corr_summable (η := η) hq hx0 hx1.le hd.le (n := n)
    have hE : rsExp n d (rsY q η (tRe q x)) ≤
        rsExp n d (fun N => (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ st ∈ Finset.univ.filter
              (fun st : (Fin n → Fin q) × (Fin n → Fin q) => η ^ 2 / 4 ≤ rsCorrDev st.1 st.2),
            rsW q (tRe q x) N st.1 * rsW q (tRe q x) N st.2 / rsF q (tRe q x) N) +
        2 * rsExp n d (fun N => ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin n → Fin q => η ^ 2 / 16 ≤ rsDevSq σ), rsW q (tRe q x) N σ) := by
      unfold rsExp
      rw [← rs_poisPiExp_const_mul, ← rs_poisPiExp_add hsC]
      · refine rs_poisPiExp_mono hmean hsY ?_ fun N => rsab_rsY_le hq hx0 hx1.le η N
        refine (hsC.add (hsm.mul_left 2)).congr fun N => ?_
        ring
      · refine (hsm.mul_left 2).congr fun N => ?_
        ring
    have hEm' : rsExp n d (fun N => ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ Finset.univ.filter
          (fun σ : Fin n → Fin q => η ^ 2 / 16 ≤ rsDevSq σ), rsW q (tRe q x) N σ) ≤
        K * Real.exp (-(r * n)) := by
      refine hEm.trans ?_
      rw [div_le_iff₀ hQ]
      calc _ ≤ K * (q : ℝ) ^ n * Real.exp (-(r * n)) := hcard n hn0
        _ = K * Real.exp (-(r * n)) * (q : ℝ) ^ n := by ring
    have hγn : 2 * K ≤ γ * n := by
      have h1 := Nat.le_ceil (2 * K / γ)
      have h2 : ((⌈2 * K / γ⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
      push_cast at h2
      have h3 : 2 * K / γ ≤ n := by linarith
      rw [div_le_iff₀ hγ0] at h3
      linarith
    have hexp : 1 + 2 * K ≤ Real.exp (γ * n) := by
      have := Real.add_one_le_exp (γ * n); linarith
    have e1 : Real.exp (-(c * n)) ≤ Real.exp (-(γ * n)) * Real.exp (-(γ * n)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have e2 : Real.exp (-(r * n)) ≤ Real.exp (-(γ * n)) * Real.exp (-(γ * n)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith
    have hpos : 0 ≤ Real.exp (-(γ * n)) * Real.exp (-(γ * n)) := by positivity
    calc rsExp n d (rsY q η (tRe q x)) ≤ Real.exp (-(c * n)) + 2 * (K * Real.exp (-(r * n))) := by
          linarith
      _ ≤ (1 + 2 * K) * (Real.exp (-(γ * n)) * Real.exp (-(γ * n))) := by
          have := mul_le_mul_of_nonneg_left e2 hK
          nlinarith
      _ ≤ Real.exp (γ * n) * (Real.exp (-(γ * n)) * Real.exp (-(γ * n))) :=
          mul_le_mul_of_nonneg_right hexp hpos
      _ = Real.exp (-(γ * n)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring

/-- **`eq:rs-bad` at the anchor `x = 1`.** -/
theorem rs_bad_one {q : ℕ} (hq : 3 ≤ q) {d η : ℝ} (hd : 0 ≤ d) (hη : 0 < η) :
    ∃ γ > 0, γ ≤ 1 ∧
      ∀ᶠ n : ℕ in atTop, rsExp n d (rsY q η (tRe q 1)) ≤ Real.exp (-(γ * n)) := by
  obtain ⟨r, hr, hr1, K, hK, hcard⟩ := rs_card_ovDev_le (by omega : 2 ≤ q) (pow_pos hη 2)
  refine ⟨r / 2, by positivity, by linarith, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨⌈2 * K / r⌉₊ + 1, fun n hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := pow_pos hq0 n
  have hmean : ∀ i, 0 ≤ rsMean n d i := fun i => by unfold rsMean; positivity
  have hY : rsY q η (tRe q 1) = fun _ : RSGraph n => (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ((Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
          η ^ 2 ≤ rsOvDev st.1 st.2).card : ℝ) := by
    funext N
    rw [rs_tRe_one]
    exact rsab_rsY_zero (by omega) η N
  rw [hY]
  unfold rsExp
  rw [rs_poisPiExp_const hmean]
  have hc := hcard n hn0
  have h1 : (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ((Finset.univ.filter fun st : (Fin n → Fin q) × (Fin n → Fin q) =>
          η ^ 2 ≤ rsOvDev st.1 st.2).card : ℝ) ≤ K * Real.exp (-(r * n)) := by
    calc _ ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * (K * (q : ℝ) ^ (2 * n) * Real.exp (-(r * n))) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
      _ = K * Real.exp (-(r * n)) := by
          rw [pow_mul', inv_pow]
          field_simp
  have hnK : 2 * K / r ≤ n := by
    have := Nat.le_ceil (2 * K / r)
    have h2 : ((⌈2 * K / r⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hKexp : K ≤ Real.exp (r / 2 * n) := by
    have := Real.add_one_le_exp (r / 2 * n)
    rw [div_le_iff₀ hr] at hnK
    nlinarith
  calc _ ≤ K * Real.exp (-(r * n)) := h1
    _ ≤ Real.exp (r / 2 * n) * Real.exp (-(r * n)) :=
        mul_le_mul_of_nonneg_right hKexp (Real.exp_pos _).le
    _ = Real.exp (-(r / 2 * n)) := by
        rw [← Real.exp_add]
        congr 1
        ring

end

end ERZeroFreeness
