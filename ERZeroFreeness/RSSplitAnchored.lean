/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSSplitMoments

/-!
# Appendix C, Lemma C.4, Step 1: the bound near an anchor (`eq:rs-anchored`)

Let `x ∈ (0,1]` be a real anchor, `t₀ = t(x)`, `ℓ = log(e/x)`, `F = F_G(x)`, `H`, `Y` as in
`app:rs-local`, and assume, as hypotheses:
* Lemma C.5(i): for all `n ≥ 1` and all complex `t` with `‖t‖ ≤ t_*`, `Re t ≤ t_*²`,
  `|E_{𝖯_d} H_G(t)| ≤ C₀` (with summability), and `|t₀| ≤ t_*`;
* Lemma C.7 at `x`: for large `n`, `E Y ≤ e^{-γn}` and
  `E[H 1_{F > e^{γn/4}}] ≤ C₁ e^{-c₂γ²n/ℓ²}`, with `C₁ > 0` and `γ, c₂ ∈ (0,1]`.

Put `ζ = min(1/4, c₂γ²/(18 d ℓ²))`.  Then (`rs_anchored`, **`eq:rs-anchored`**): for all large `n`
and every complex `t` with `‖t‖ ≤ t_*`, `Re t ≤ t_*²` and `|M_t(a,a')| ≤ e^ζ M_x(a,a')` for all
`a, a'`:  `E_{𝖯_d}[e^{dm/n} |F_G(t)|] ≤ e^{d²} √(2C₀ + 4)`.

## Proof

(Paper, `app:rs-split`, Step 1.)  Pointwise: `|w_t(σ)| ≤ e^{ζm} w_{t₀}(σ)`, hence
`|H_G(t)| ≤ e^{2ζm} H` and `||F_G(t)|² - H_G(t)| ≤ e^{2ζm}(F² - H)`
(`‖F_t‖² = q^{-2n} ∑_{σ,τ} Re(w_t(σ) conj w_t(τ))`, the window splits the double sum).  With
`Υ = max{1, e^{-γn/4} F}` (`0 ≤ 1 - 1/Υ ≤ 1_{F > e^{γn/4}}`, `1/Υ ≤ e^{γn/4}/F`):
`E |F_t|²/Υ ≤ C₀ + E[e^{2ζm} H 1_{F > e^{γn/4}}] + e^{γn/4} E[e^{2ζm} Y]`  (`eq:rs-complex`).
By `rs_tsum_mul_le_sqrt`, `Y ≤ F`, `rs_exp_edges_mul_rsF_le`, `rs_exp_edges_mul_rsHR_le`
(with `E H ≤ C₀` at `t₀` via `rs_rsH_ofReal`) and `e^{4ζ} - 1 ≤ 8ζ` (`ζ ≤ 1/4`):
`e^{γn/4} E[e^{2ζm} Y] ≤ e^{(γ/4 + 2dζ - γ/2)n} ≤ e^{-γn/8}` and
`E[e^{2ζm} H 1_{F > e^{γn/4}}] ≤ (C₀C₁)^{1/2} e^{(9dζ/2 - c₂γ²/(2ℓ²))n}`, both `≤ 1` for large `n`
because `2dζ ≤ γ/8` and `9dζ/2 ≤ c₂γ²/(4ℓ²)` (`γ ≤ 1 ≤ ℓ`, `c₂ ≤ 1`).  So `E|F_t|²/Υ ≤ C₀ + 2`.
For `n ≥ 2d`, `E[e^{2dm/n} Υ] ≤ E e^{2dm/n} + E[e^{2dm/n} F] ≤ 2e^{2d²}` (`rs_exp_edges_hasSum`,
`e^y - 1 ≤ 2y` on `[0,1]`), and Cauchy–Schwarz once more gives the claim.  Each integrand is
summable, either by a bound `A·c^m` (`rs_summable_poisPi_of_abs_le`, using `M_x ≤ 3/2`) or by
comparison with the exponential moments of `RSSplitMoments`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSAnchoredAux

/-- `ℓ = log(e/x) ≥ 1` for `x ∈ (0,1]`. -/
theorem rsEll_ge_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) : 1 ≤ rsEll x := by
  unfold rsEll
  rw [Real.log_div (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
  have : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  linarith

/-- `e^{χm} = (e^χ)^m`. -/
theorem exp_mul_cast (χ : ℝ) (m : ℕ) : Real.exp (χ * (m : ℝ)) = Real.exp χ ^ m := by
  rw [mul_comm, Real.exp_nat_mul]

/-- `e^y - 1 ≤ 2y` for `y ∈ [0,1]`. -/
theorem exp_sub_one_le_two_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp y - 1 ≤ 2 * y := by
  have h := Real.abs_exp_sub_one_le (x := y) (by rw [abs_of_nonneg hy0]; exact hy1)
  rw [abs_of_nonneg hy0] at h
  exact (le_abs_self _).trans h

/-- `|w_t(σ)| ≤ e^{ζ m} w_{t₀}(σ)` when `|M_t| ≤ e^ζ M_{t₀}` entrywise. -/
theorem norm_rsW_le {q n : ℕ} {t : ℂ} {t₀ ζ : ℝ}
    (hM : ∀ a b : Fin q, ‖rsM q t a b‖ ≤ Real.exp ζ * rsM q t₀ a b) (N : RSGraph n)
    (σ : Fin n → Fin q) :
    ‖rsW q t N σ‖ ≤ Real.exp (ζ * (rsEdges N : ℝ)) * rsW q t₀ N σ := by
  unfold rsW
  rw [norm_prod]
  simp only [norm_pow]
  calc ∏ uv : Fin n × Fin n, ‖rsM q t (σ uv.1) (σ uv.2)‖ ^ N uv
      ≤ ∏ uv : Fin n × Fin n, (Real.exp ζ * rsM q t₀ (σ uv.1) (σ uv.2)) ^ N uv :=
        Finset.prod_le_prod (fun _ _ => by positivity)
          (fun uv _ => pow_le_pow_left₀ (norm_nonneg _) (hM _ _) _)
    _ = Real.exp (ζ * (rsEdges N : ℝ)) *
          ∏ uv : Fin n × Fin n, rsM q t₀ (σ uv.1) (σ uv.2) ^ N uv := by
        rw [exp_mul_cast]
        simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        rfl

/-- `‖F_t‖² = q^{-2n} ∑_{σ,τ} Re(w_t(σ) conj w_t(τ))`. -/
theorem norm_sq_rsF {q n : ℕ} (t : ℂ) (N : RSGraph n) :
    ‖rsF q t N‖ ^ 2 = (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ∑ p : (Fin n → Fin q) × (Fin n → Fin q),
        (rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)).re := by
  have hF : rsF q t N = ((((q : ℝ) ^ n)⁻¹ : ℝ) : ℂ) * ∑ σ : Fin n → Fin q, rsW q t N σ := by
    unfold rsF; push_cast; rfl
  have h1 : ‖rsF q t N‖ ^ 2 = (rsF q t N * starRingEnd ℂ (rsF q t N)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have h2 : rsF q t N * starRingEnd ℂ (rsF q t N) =
      (((((q : ℝ) ^ n)⁻¹) ^ 2 : ℝ) : ℂ) * ∑ p : (Fin n → Fin q) × (Fin n → Fin q),
        rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2) := by
    rw [hF, map_mul, Complex.conj_ofReal, map_sum, Fintype.sum_prod_type, Complex.ofReal_pow]
    rw [show ∀ (c A B : ℂ), c * A * (c * B) = c ^ 2 * (A * B) from fun c A B => by ring]
    rw [Finset.sum_mul_sum]
  rw [h1, h2, Complex.re_ofReal_mul, Complex.re_sum]

/-- Termwise comparison of a sub-sum of `Re(w_t(σ) conj w_t(τ))` with the real weights. -/
theorem abs_sum_re_le {q n : ℕ} {t : ℂ} {t₀ ζ : ℝ} (hM0 : ∀ a b : Fin q, 0 ≤ rsM q t₀ a b)
    (hM : ∀ a b : Fin q, ‖rsM q t a b‖ ≤ Real.exp ζ * rsM q t₀ a b) (N : RSGraph n)
    (S : Finset ((Fin n → Fin q) × (Fin n → Fin q))) :
    |∑ p ∈ S, (rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)).re| ≤
      Real.exp (2 * ζ * (rsEdges N : ℝ)) * ∑ p ∈ S, rsW q t₀ N p.1 * rsW q t₀ N p.2 := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  have hw0 : ∀ σ, 0 ≤ rsW q t₀ N σ := fun σ =>
    Finset.prod_nonneg fun uv _ => pow_nonneg (hM0 _ _) _
  have he := Real.exp_pos (ζ * (rsEdges N : ℝ))
  calc |(rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)).re|
      ≤ ‖rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)‖ := Complex.abs_re_le_norm _
    _ = ‖rsW q t N p.1‖ * ‖rsW q t N p.2‖ := by rw [norm_mul, Complex.norm_conj]
    _ ≤ (Real.exp (ζ * (rsEdges N : ℝ)) * rsW q t₀ N p.1) *
          (Real.exp (ζ * (rsEdges N : ℝ)) * rsW q t₀ N p.2) :=
        mul_le_mul (norm_rsW_le hM N _) (norm_rsW_le hM N _) (norm_nonneg _)
          (mul_nonneg he.le (hw0 _))
    _ = Real.exp (2 * ζ * (rsEdges N : ℝ)) * (rsW q t₀ N p.1 * rsW q t₀ N p.2) := by
        rw [show 2 * ζ * (rsEdges N : ℝ) = ζ * rsEdges N + ζ * rsEdges N by ring, Real.exp_add]
        ring

/-- `|H_G(t)| ≤ e^{2ζm} H` and `| |F_G(t)|² - H_G(t) | ≤ e^{2ζm} (F² - H)`. -/
theorem rsH_bounds {q n : ℕ} {η : ℝ} {t : ℂ} {t₀ ζ : ℝ} (hM0 : ∀ a b : Fin q, 0 ≤ rsM q t₀ a b)
    (hM : ∀ a b : Fin q, ‖rsM q t a b‖ ≤ Real.exp ζ * rsM q t₀ a b) (N : RSGraph n) :
    |rsH q η t N| ≤ Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η t₀ N ∧
      |‖rsF q t N‖ ^ 2 - rsH q η t N| ≤
        Real.exp (2 * ζ * (rsEdges N : ℝ)) * (rsF q t₀ N ^ 2 - rsHR q η t₀ N) := by
  have hc0 : 0 ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 := sq_nonneg _
  have hF2 : rsF q t₀ N ^ 2 = (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ∑ p : (Fin n → Fin q) × (Fin n → Fin q), rsW q t₀ N p.1 * rsW q t₀ N p.2 := by
    unfold rsF
    rw [Fintype.sum_prod_type, mul_pow, sq (∑ σ : Fin n → Fin q, rsW q t₀ N σ),
      Finset.sum_mul_sum]
  constructor
  · unfold rsH rsHR
    rw [abs_mul, abs_of_nonneg hc0]
    calc (((q : ℝ) ^ n)⁻¹) ^ 2 *
          |∑ p ∈ rsWindow q n η, (rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)).re|
        ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
            ∑ p ∈ rsWindow q n η, rsW q t₀ N p.1 * rsW q t₀ N p.2) :=
          mul_le_mul_of_nonneg_left (abs_sum_re_le hM0 hM N _) hc0
      _ = _ := by ring
  · have e1 : ‖rsF q t N‖ ^ 2 - rsH q η t N = (((q : ℝ) ^ n)⁻¹) ^ 2 *
        ∑ p ∈ (rsWindow q n η)ᶜ, (rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)).re := by
      rw [norm_sq_rsF, ← Finset.sum_add_sum_compl (rsWindow q n η)]
      unfold rsH
      ring
    have e2 : rsF q t₀ N ^ 2 - rsHR q η t₀ N = (((q : ℝ) ^ n)⁻¹) ^ 2 *
        ∑ p ∈ (rsWindow q n η)ᶜ, rsW q t₀ N p.1 * rsW q t₀ N p.2 := by
      rw [hF2, ← Finset.sum_add_sum_compl (rsWindow q n η)]
      unfold rsHR
      ring
    rw [e1, e2, abs_mul, abs_of_nonneg hc0]
    calc (((q : ℝ) ^ n)⁻¹) ^ 2 *
          |∑ p ∈ (rsWindow q n η)ᶜ, (rsW q t N p.1 * starRingEnd ℂ (rsW q t N p.2)).re|
        ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
            ∑ p ∈ (rsWindow q n η)ᶜ, rsW q t₀ N p.1 * rsW q t₀ N p.2) :=
          mul_le_mul_of_nonneg_left (abs_sum_re_le hM0 hM N _) hc0
      _ = _ := by ring

/-- The pointwise form of `eq:rs-complex`:
`|F_t|²/Υ ≤ H_t + e^{2ζm} H 1_{F > K} + K e^{2ζm} Y` with `Υ = max(1, F/K)`. -/
theorem pointwise_main {Fs Ht F H E K I : ℝ} (hF : 0 < F) (hHF : H ≤ F ^ 2)
    (hE : 0 ≤ E) (hK : 0 < K) (hI : I = if K < F then 1 else 0)
    (h1 : |Ht| ≤ E * H) (h2 : |Fs - Ht| ≤ E * (F ^ 2 - H)) :
    Fs / max 1 (K⁻¹ * F) ≤ Ht + E * H * I + K * (E * ((F ^ 2 - H) / F)) := by
  have hU1 : 1 ≤ max 1 (K⁻¹ * F) := le_max_left _ _
  have hU0 : 0 < max 1 (K⁻¹ * F) := lt_of_lt_of_le one_pos hU1
  have hFU : F / max 1 (K⁻¹ * F) ≤ K := by
    rw [div_le_iff₀ hU0]
    have h : K⁻¹ * F ≤ max 1 (K⁻¹ * F) := le_max_right _ _
    calc F = K * (K⁻¹ * F) := by field_simp
      _ ≤ K * max 1 (K⁻¹ * F) := mul_le_mul_of_nonneg_left h hK.le
  have hYn : 0 ≤ E * ((F ^ 2 - H) / F) := mul_nonneg hE (div_nonneg (by linarith) hF.le)
  have hY : (Fs - Ht) / max 1 (K⁻¹ * F) ≤ K * (E * ((F ^ 2 - H) / F)) := by
    calc (Fs - Ht) / max 1 (K⁻¹ * F) ≤ |Fs - Ht| / max 1 (K⁻¹ * F) :=
          div_le_div_of_nonneg_right (le_abs_self _) hU0.le
      _ ≤ E * (F ^ 2 - H) / max 1 (K⁻¹ * F) := div_le_div_of_nonneg_right h2 hU0.le
      _ = (E * ((F ^ 2 - H) / F)) * (F / max 1 (K⁻¹ * F)) := by
          field_simp
      _ ≤ (E * ((F ^ 2 - H) / F)) * K := mul_le_mul_of_nonneg_left hFU hYn
      _ = K * (E * ((F ^ 2 - H) / F)) := by ring
  have hHt : Ht / max 1 (K⁻¹ * F) ≤ Ht + E * H * I := by
    by_cases hKF : K < F
    · rw [hI, if_pos hKF, mul_one]
      have hinv1 : 1 / max 1 (K⁻¹ * F) ≤ 1 := by rw [div_le_one hU0]; exact hU1
      have hinv0 : 0 < 1 / max 1 (K⁻¹ * F) := by positivity
      have e : Ht / max 1 (K⁻¹ * F) - Ht = -(Ht * (1 - 1 / max 1 (K⁻¹ * F))) := by
        field_simp
        ring
      have : Ht / max 1 (K⁻¹ * F) - Ht ≤ |Ht| := by
        rw [e]
        calc -(Ht * (1 - 1 / max 1 (K⁻¹ * F))) ≤ |Ht * (1 - 1 / max 1 (K⁻¹ * F))| := neg_le_abs _
          _ = |Ht| * (1 - 1 / max 1 (K⁻¹ * F)) := by
              rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1 - 1 / max 1 (K⁻¹ * F) by linarith)]
          _ ≤ |Ht| := mul_le_of_le_one_right (abs_nonneg _) (by linarith)
      linarith
    · rw [hI, if_neg hKF, mul_zero, add_zero]
      have hU' : max 1 (K⁻¹ * F) = 1 := by
        apply max_eq_left
        have hKF' : F ≤ K := not_lt.mp hKF
        rw [inv_mul_le_iff₀ hK]
        linarith
      rw [hU', div_one]
  calc Fs / max 1 (K⁻¹ * F) = Ht / max 1 (K⁻¹ * F) + (Fs - Ht) / max 1 (K⁻¹ * F) := by ring
    _ ≤ _ := by linarith


/-- `(e^a)² = e^{2a}`. -/
theorem exp_sq (a : ℝ) : Real.exp a ^ 2 = Real.exp (2 * a) := by
  rw [sq, ← Real.exp_add]; ring_nf

/-- The edge means `d/(2n)` are nonnegative. -/
theorem rsMean_nonneg {n : ℕ} {d : ℝ} (hd : 0 ≤ d) (uv : Fin n × Fin n) : 0 ≤ rsMean n d uv := by
  unfold rsMean; positivity

/-- Cauchy–Schwarz for `rsExp`. -/
theorem rsExp_mul_le_sqrt {n : ℕ} {d : ℝ} (hd : 0 ≤ d) {f g : RSGraph n → ℝ}
    (hf : ∀ N, 0 ≤ f N) (hg : ∀ N, 0 ≤ g N)
    (hf2 : Summable fun N => poisPi (rsMean n d) N * f N ^ 2)
    (hg2 : Summable fun N => poisPi (rsMean n d) N * g N ^ 2) :
    rsExp n d (fun N => f N * g N) ≤
      Real.sqrt (rsExp n d fun N => f N ^ 2) * Real.sqrt (rsExp n d fun N => g N ^ 2) :=
  rs_tsum_mul_le_sqrt (fun N => rs_poisPi_nonneg (rsMean_nonneg hd) N) hf hg hf2 hg2

/-- For `K, A ≥ 0`: `K √X √Y ≤ 1` when `X ≤ A`, `Y ≤ B` and `K² A B ≤ 1`. -/
theorem mul_sqrt_mul_sqrt_le_one {K X Y A B : ℝ} (hK : 0 ≤ K) (hA : 0 ≤ A) (hX : X ≤ A)
    (hY : Y ≤ B) (h : K ^ 2 * (A * B) ≤ 1) : K * (Real.sqrt X * Real.sqrt Y) ≤ 1 := by
  calc K * (Real.sqrt X * Real.sqrt Y) ≤ K * (Real.sqrt A * Real.sqrt B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (Real.sqrt_le_sqrt hX) (Real.sqrt_le_sqrt hY)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hK
    _ = Real.sqrt (K ^ 2 * (A * B)) := by
        rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_mul hA, Real.sqrt_sq hK]
    _ ≤ 1 := Real.sqrt_le_one.mpr h

/-- `K E[e^{2ζm} Y] ≤ 1` (with summability) whenever `E Y ≤ B` and
`K² e^{(e^{4ζ} - 1)dn/2} B ≤ 1` (Cauchy–Schwarz, `Y ≤ F`, `rs_exp_edges_mul_rsF_le`); it is
applied with `K = e^{γn/4}`. -/
theorem bound_Y_term {q n : ℕ} (hq : 3 ≤ q) {d η x ζ K B : ℝ} (hd : 0 ≤ d) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (hK : 0 ≤ K)
    (hY : rsExp n d (rsY q η (tRe q x)) ≤ B)
    (hsmall : K ^ 2 * (Real.exp ((Real.exp (4 * ζ) - 1) * d * n / 2) * B) ≤ 1) :
    Summable (fun N => poisPi (rsMean n d) N *
        (K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N))) ∧
      rsExp n d (fun N => K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N)) ≤ 1 := by
  have hlam := rsMean_nonneg (n := n) hd
  have hYb := fun N : RSGraph n => rs_rsY_bounds hq hx0 hx1 η N
  have hFb := fun N : RSGraph n => rs_rsF_bounds hq hx0 hx1 N
  have hF4 := rs_exp_edges_mul_rsF_le (n := n) hq hd hx0.le hx1 (4 * ζ)
  have hF1 := (rs_poisson_first_moment (n := n) hq hd hx0.le hx1).1
  have e4 : ∀ N : RSGraph n,
      Real.exp (2 * ζ * (rsEdges N : ℝ)) ^ 2 = Real.exp (4 * ζ * (rsEdges N : ℝ)) := by
    intro N; rw [exp_sq]; ring_nf
  have hf2 : Summable fun N => poisPi (rsMean n d) N *
      (Real.exp (2 * ζ * (rsEdges N : ℝ)) * Real.sqrt (rsY q η (tRe q x) N)) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N) (sq_nonneg _))
      (fun N => ?_) hF4.1
    refine mul_le_mul_of_nonneg_left ?_ (rs_poisPi_nonneg hlam N)
    rw [mul_pow, Real.sq_sqrt (hYb N).1, e4]
    exact mul_le_mul_of_nonneg_left (hYb N).2 (Real.exp_pos _).le
  have hg2 : Summable fun N => poisPi (rsMean n d) N * Real.sqrt (rsY q η (tRe q x) N) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N) (sq_nonneg _))
      (fun N => ?_) hF1
    refine mul_le_mul_of_nonneg_left ?_ (rs_poisPi_nonneg hlam N)
    rw [Real.sq_sqrt (hYb N).1]
    exact (hYb N).2
  have hS : Summable (fun N => poisPi (rsMean n d) N *
      (K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N))) := by
    refine rs_summable_poisPi_of_abs_le hlam (A := K) (c := Real.exp (2 * ζ) * (3 / 2))
      (by positivity) (fun N => ?_)
    show _ ≤ K * (Real.exp (2 * ζ) * (3 / 2)) ^ rsEdges N
    rw [mul_pow, ← exp_mul_cast, abs_of_nonneg (mul_nonneg hK (mul_nonneg (Real.exp_pos _).le
      (hYb N).1))]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) hK
    exact (hYb N).2.trans (hFb N).2
  refine ⟨hS, ?_⟩
  have e1 : rsExp n d (fun N => K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N)) =
      K * rsExp n d (fun N => (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
        Real.sqrt (rsY q η (tRe q x) N)) * Real.sqrt (rsY q η (tRe q x) N)) := by
    unfold rsExp
    rw [← rs_poisPiExp_const_mul]
    congr 1
    funext N
    rw [mul_assoc (Real.exp _), Real.mul_self_sqrt (hYb N).1]
  rw [e1]
  have hCS := rsExp_mul_le_sqrt hd (fun N => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    (fun N => Real.sqrt_nonneg _) hf2 hg2
  have hX : rsExp n d (fun N => (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
      Real.sqrt (rsY q η (tRe q x) N)) ^ 2) ≤ Real.exp ((Real.exp (4 * ζ) - 1) * d * n / 2) := by
    refine le_trans ?_ hF4.2
    refine rs_poisPiExp_mono hlam hf2 hF4.1 fun N => ?_
    rw [mul_pow, Real.sq_sqrt (hYb N).1, e4]
    exact mul_le_mul_of_nonneg_left (hYb N).2 (Real.exp_pos _).le
  have hYY : rsExp n d (fun N => Real.sqrt (rsY q η (tRe q x) N) ^ 2) ≤ B := by
    refine le_trans (le_of_eq ?_) hY
    unfold rsExp poisPiExp
    exact tsum_congr fun N => by dsimp only; rw [Real.sq_sqrt (hYb N).1]
  calc K * rsExp n d _ ≤ K * (Real.sqrt _ * Real.sqrt _) := mul_le_mul_of_nonneg_left hCS hK
    _ ≤ 1 := mul_sqrt_mul_sqrt_le_one hK (Real.exp_pos _).le hX hYY hsmall

/-- The indicator of `{K < f}` as an `if`. -/
theorem indicator_eq_ite {n : ℕ} (K : ℝ) (f : RSGraph n → ℝ) (N : RSGraph n) :
    {N' : RSGraph n | K < f N'}.indicator (fun _ => (1 : ℝ)) N = if K < f N then 1 else 0 := by
  by_cases h : K < f N
  · rw [Set.indicator_of_mem (show N ∈ {N' : RSGraph n | K < f N'} from h), if_pos h]
  · rw [Set.indicator_of_notMem (show N ∉ {N' : RSGraph n | K < f N'} from h), if_neg h]

/-- `E[e^{2ζm} H 1_{F > K}] ≤ 1` (with summability) whenever `E H ≤ C₀`,
`E[H 1_{F > K}] ≤ B` and `e^{9(e^{4ζ} - 1)dn/8} C₀ B ≤ 1` (Cauchy–Schwarz and
`rs_exp_edges_mul_rsHR_le`). -/
theorem bound_H_term {q n : ℕ} (hq : 3 ≤ q) {d η x ζ C₀ K B : ℝ} (hd : 0 ≤ d) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (hζ0 : 0 ≤ ζ) (hC₀ : 0 ≤ C₀)
    (hEH : rsExp n d (rsHR q η (tRe q x)) ≤ C₀)
    (hHI : rsExp n d (fun N => rsHR q η (tRe q x) N *
        {N' : RSGraph n | K < rsF q (tRe q x) N'}.indicator (fun _ => (1 : ℝ)) N) ≤ B)
    (hsmall : Real.exp (9 * (Real.exp (4 * ζ) - 1) * d * n / 8) * C₀ * B ≤ 1) :
    Summable (fun N => poisPi (rsMean n d) N *
        (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) ∧
      rsExp n d (fun N => Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) ≤ 1 := by
  have hlam := rsMean_nonneg (n := n) hd
  have hHb := fun N : RSGraph n => rs_rsHR_bounds hq hx0.le hx1 η N
  have hFb := fun N : RSGraph n => rs_rsF_bounds hq hx0 hx1 N
  have hH4 := rs_exp_edges_mul_rsHR_le (n := n) (η := η) hq hd hx0.le hx1
    (show 0 ≤ 4 * ζ by linarith)
  have hI : ∀ N : RSGraph n, 0 ≤ (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) ∧
      (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) ≤ 1 := by
    intro N; split_ifs <;> norm_num
  have hHI0 : ∀ N : RSGraph n,
      0 ≤ rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) :=
    fun N => mul_nonneg (hHb N).1 (hI N).1
  have hHI1 : ∀ N : RSGraph n,
      rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) ≤
        rsHR q η (tRe q x) N :=
    fun N => mul_le_of_le_one_right (hHb N).1 (hI N).2
  have e4 : ∀ N : RSGraph n,
      Real.exp (2 * ζ * (rsEdges N : ℝ)) ^ 2 = Real.exp (4 * ζ * (rsEdges N : ℝ)) := by
    intro N; rw [exp_sq]; ring_nf
  have hf2pt : ∀ N : RSGraph n, (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
      Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) ^ 2 ≤
        Real.exp (4 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N := by
    intro N
    rw [mul_pow, Real.sq_sqrt (hHI0 N), e4]
    exact mul_le_mul_of_nonneg_left (hHI1 N) (Real.exp_pos _).le
  have hf2 : Summable fun N => poisPi (rsMean n d) N *
      (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
        Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) ^ 2 :=
    Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N) (sq_nonneg _))
      (fun N => mul_le_mul_of_nonneg_left (hf2pt N) (rs_poisPi_nonneg hlam N)) hH4.1
  have hg2pt : ∀ N : RSGraph n,
      Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) ^ 2 ≤
        Real.exp (4 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N := by
    intro N
    rw [Real.sq_sqrt (hHI0 N)]
    refine (hHI1 N).trans ?_
    have h1 : 1 ≤ Real.exp (4 * ζ * (rsEdges N : ℝ)) := Real.one_le_exp (by positivity)
    nlinarith [(hHb N).1]
  have hg2 : Summable fun N => poisPi (rsMean n d) N *
      Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) ^ 2 :=
    Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N) (sq_nonneg _))
      (fun N => mul_le_mul_of_nonneg_left (hg2pt N) (rs_poisPi_nonneg hlam N)) hH4.1
  have hS : Summable (fun N => poisPi (rsMean n d) N *
      (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
        (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) := by
    refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hH4.1
    · exact mul_nonneg (rs_poisPi_nonneg hlam N)
        (by rw [mul_assoc]; exact mul_nonneg (Real.exp_pos _).le (hHI0 N))
    · refine mul_le_mul_of_nonneg_left ?_ (rs_poisPi_nonneg hlam N)
      rw [mul_assoc]
      refine mul_le_mul (Real.exp_le_exp.mpr ?_) (hHI1 N) (hHI0 N) (Real.exp_pos _).le
      have : (0 : ℝ) ≤ ζ * (rsEdges N : ℝ) := by positivity
      linarith
  refine ⟨hS, ?_⟩
  have e1 : rsExp n d (fun N => Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
        (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) =
      rsExp n d (fun N => (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
        Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) *
        Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) := by
    unfold rsExp poisPiExp
    refine tsum_congr fun N => ?_
    dsimp only
    rw [mul_assoc (Real.exp _) (Real.sqrt _), Real.mul_self_sqrt (hHI0 N), mul_assoc]
  rw [e1]
  have hCS := rsExp_mul_le_sqrt hd (fun N => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    (fun N => Real.sqrt_nonneg _) hf2 hg2
  have hX : rsExp n d (fun N => (Real.exp (2 * ζ * (rsEdges N : ℝ)) *
      Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) ^ 2) ≤
        Real.exp (9 * (Real.exp (4 * ζ) - 1) * d * n / 8) * C₀ := by
    refine le_trans (rs_poisPiExp_mono hlam hf2 hH4.1 hf2pt) (hH4.2.trans ?_)
    exact mul_le_mul_of_nonneg_left hEH (Real.exp_pos _).le
  have hYY : rsExp n d (fun N =>
      Real.sqrt (rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) ^ 2) ≤
        B := by
    refine le_trans (le_of_eq ?_) hHI
    unfold rsExp poisPiExp
    refine tsum_congr fun N => ?_
    dsimp only
    rw [Real.sq_sqrt (hHI0 N), indicator_eq_ite]
  have := mul_sqrt_mul_sqrt_le_one zero_le_one
    (mul_nonneg (Real.exp_pos _).le hC₀) hX hYY (by rw [one_pow, one_mul]; exact hsmall)
  rw [one_mul] at this
  exact hCS.trans this

/-- `E[e^{2dm/n} Υ] ≤ 2 e^{2d²}` for `n ≥ 2d`, `Υ = max(1, F/K)`, `K ≥ 1`. -/
theorem bound_Ups {q n : ℕ} (hq : 3 ≤ q) {d x K : ℝ} (hd : 0 < d) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hK : 1 ≤ K) (hn : 0 < n) (hn2d : 2 * d ≤ n) :
    Summable (fun N => poisPi (rsMean n d) N *
        (Real.exp (2 * d / n * (rsEdges N : ℝ)) * max 1 (K⁻¹ * rsF q (tRe q x) N))) ∧
      rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ)) *
        max 1 (K⁻¹ * rsF q (tRe q x) N)) ≤ 2 * Real.exp (2 * d ^ 2) := by
  have hlam := rsMean_nonneg (n := n) hd.le
  have h1 := rs_exp_edges_hasSum (n := n) hd.le (2 * d / n)
  have h2 := rs_exp_edges_mul_rsF_le (n := n) hq hd.le hx0.le hx1 (2 * d / n)
  have hFb := fun N : RSGraph n => rs_rsF_bounds hq hx0 hx1 N
  have hpt : ∀ N : RSGraph n, Real.exp (2 * d / n * (rsEdges N : ℝ)) *
      max 1 (K⁻¹ * rsF q (tRe q x) N) ≤ Real.exp (2 * d / n * (rsEdges N : ℝ)) +
        Real.exp (2 * d / n * (rsEdges N : ℝ)) * rsF q (tRe q x) N := by
    intro N
    have hF0 : 0 ≤ rsF q (tRe q x) N := (pow_nonneg hx0.le _).trans (hFb N).1
    have hKF : K⁻¹ * rsF q (tRe q x) N ≤ rsF q (tRe q x) N :=
      mul_le_of_le_one_left hF0 (inv_le_one_of_one_le₀ hK)
    have : max 1 (K⁻¹ * rsF q (tRe q x) N) ≤ 1 + rsF q (tRe q x) N :=
      max_le (by linarith) (by linarith)
    calc _ ≤ Real.exp (2 * d / n * (rsEdges N : ℝ)) * (1 + rsF q (tRe q x) N) :=
          mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
      _ = _ := by ring
  have hsum : Summable (fun N => poisPi (rsMean n d) N *
      (Real.exp (2 * d / n * (rsEdges N : ℝ)) +
        Real.exp (2 * d / n * (rsEdges N : ℝ)) * rsF q (tRe q x) N)) :=
    (h1.summable.add h2.1).congr fun N => by ring
  have hS : Summable (fun N => poisPi (rsMean n d) N *
      (Real.exp (2 * d / n * (rsEdges N : ℝ)) * max 1 (K⁻¹ * rsF q (tRe q x) N))) :=
    Summable.of_nonneg_of_le (fun N => mul_nonneg (rs_poisPi_nonneg hlam N)
      (mul_nonneg (Real.exp_pos _).le (le_trans zero_le_one (le_max_left _ _))))
      (fun N => mul_le_mul_of_nonneg_left (hpt N) (rs_poisPi_nonneg hlam N)) hsum
  refine ⟨hS, ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hχ0 : 0 ≤ 2 * d / n := by positivity
  have hχ1 : 2 * d / n ≤ 1 := by rw [div_le_one hn']; exact hn2d
  have hexp : Real.exp ((Real.exp (2 * d / n) - 1) * d * n / 2) ≤ Real.exp (2 * d ^ 2) := by
    apply Real.exp_le_exp.mpr
    have h3 := exp_sub_one_le_two_mul hχ0 hχ1
    have h4 : 0 ≤ d * n := by positivity
    calc (Real.exp (2 * d / n) - 1) * d * n / 2 = (Real.exp (2 * d / n) - 1) * (d * n) / 2 := by
          ring
      _ ≤ (2 * (2 * d / n)) * (d * n) / 2 := by
          have := mul_le_mul_of_nonneg_right h3 h4
          linarith
      _ = 2 * d ^ 2 := by field_simp
  have e1 : rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ))) =
      Real.exp ((Real.exp (2 * d / n) - 1) * d * n / 2) := h1.tsum_eq
  calc rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ)) *
        max 1 (K⁻¹ * rsF q (tRe q x) N))
      ≤ rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ)) +
        Real.exp (2 * d / n * (rsEdges N : ℝ)) * rsF q (tRe q x) N) :=
        rs_poisPiExp_mono hlam hS hsum hpt
    _ = rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ))) +
        rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ)) * rsF q (tRe q x) N) :=
        rs_poisPiExp_add h1.summable h2.1
    _ ≤ Real.exp (2 * d ^ 2) + Real.exp (2 * d ^ 2) := by
        rw [e1]
        exact add_le_add hexp (h2.2.trans hexp)
    _ = 2 * Real.exp (2 * d ^ 2) := by ring

/-- **`eq:rs-complex`**: `E[|F_t|²/Υ] ≤ C₀ + 2`, given the two error terms are `≤ 1`. -/
theorem bound_FU {q n : ℕ} (hq : 3 ≤ q) {d η x ζ C₀ K : ℝ} {t : ℂ} (hd : 0 ≤ d) (hx0 : 0 < x)
    (hx1 : x ≤ 1) (hK : 0 < K)
    (hM : ∀ a b : Fin q, ‖rsM q t a b‖ ≤ Real.exp ζ * rsM q (tRe q x) a b)
    (hHt : Summable (fun N => poisPi (rsMean n d) N * rsH q η t N))
    (hHt' : rsExp n d (rsH q η t) ≤ C₀)
    (hHterm : Summable (fun N => poisPi (rsMean n d) N *
        (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) ∧
      rsExp n d (fun N => Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) ≤ 1)
    (hYterm : Summable (fun N => poisPi (rsMean n d) N *
        (K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N))) ∧
      rsExp n d (fun N => K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N)) ≤ 1) :
    Summable (fun N => poisPi (rsMean n d) N *
        (‖rsF q t N‖ ^ 2 / max 1 (K⁻¹ * rsF q (tRe q x) N))) ∧
      rsExp n d (fun N => ‖rsF q t N‖ ^ 2 / max 1 (K⁻¹ * rsF q (tRe q x) N)) ≤ C₀ + 2 := by
  have hlam := rsMean_nonneg (n := n) hd
  have hM0 : ∀ a b : Fin q, 0 ≤ rsM q (tRe q x) a b :=
    fun a b => hx0.le.trans (rs_rsM_mem hq hx0.le hx1 a b).1
  have hFb := fun N : RSGraph n => rs_rsF_bounds hq hx0 hx1 N
  have hHb := fun N : RSGraph n => rs_rsHR_bounds hq hx0.le hx1 η N
  have hB := fun N : RSGraph n => rsH_bounds (η := η) hM0 hM N
  have hpt : ∀ N : RSGraph n, ‖rsF q t N‖ ^ 2 / max 1 (K⁻¹ * rsF q (tRe q x) N) ≤
      rsH q η t N + Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) +
        K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N) := by
    intro N
    have hF : 0 < rsF q (tRe q x) N := lt_of_lt_of_le (pow_pos hx0 _) (hFb N).1
    exact pointwise_main hF (hHb N).2 (Real.exp_pos _).le hK rfl (hB N).1 (hB N).2
  have hS : Summable (fun N => poisPi (rsMean n d) N *
      (‖rsF q t N‖ ^ 2 / max 1 (K⁻¹ * rsF q (tRe q x) N))) := by
    refine rs_summable_poisPi_of_abs_le hlam (A := 1) (c := Real.exp (2 * ζ) * (9 / 4))
      (by positivity) (fun N => ?_)
    show _ ≤ 1 * (Real.exp (2 * ζ) * (9 / 4)) ^ rsEdges N
    have hU1 : 1 ≤ max 1 (K⁻¹ * rsF q (tRe q x) N) := le_max_left _ _
    have hFs : ‖rsF q t N‖ ^ 2 ≤ Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsF q (tRe q x) N ^ 2 := by
      calc ‖rsF q t N‖ ^ 2 = (‖rsF q t N‖ ^ 2 - rsH q η t N) + rsH q η t N := by ring
        _ ≤ |‖rsF q t N‖ ^ 2 - rsH q η t N| + |rsH q η t N| :=
            add_le_add (le_abs_self _) (le_abs_self _)
        _ ≤ Real.exp (2 * ζ * (rsEdges N : ℝ)) *
              (rsF q (tRe q x) N ^ 2 - rsHR q η (tRe q x) N) +
            Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N :=
            add_le_add (hB N).2 (hB N).1
        _ = _ := by ring
    have hF2 : rsF q (tRe q x) N ^ 2 ≤ ((9 : ℝ) / 4) ^ rsEdges N := by
      have h0 : 0 ≤ rsF q (tRe q x) N := (pow_nonneg hx0.le _).trans (hFb N).1
      calc rsF q (tRe q x) N ^ 2 ≤ ((3 / 2 : ℝ) ^ rsEdges N) ^ 2 :=
            pow_le_pow_left₀ h0 (hFb N).2 2
        _ = ((9 : ℝ) / 4) ^ rsEdges N := by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith)), one_mul, mul_pow, ← exp_mul_cast]
    calc ‖rsF q t N‖ ^ 2 / max 1 (K⁻¹ * rsF q (tRe q x) N) ≤ ‖rsF q t N‖ ^ 2 :=
          div_le_self (sq_nonneg _) hU1
      _ ≤ Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsF q (tRe q x) N ^ 2 := hFs
      _ ≤ Real.exp (2 * ζ * (rsEdges N : ℝ)) * ((9 : ℝ) / 4) ^ rsEdges N :=
          mul_le_mul_of_nonneg_left hF2 (Real.exp_pos _).le
  have hs12 : Summable (fun N => poisPi (rsMean n d) N *
      (rsH q η t N + Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0))) :=
    (hHt.add hHterm.1).congr fun N => by ring
  have hs123 : Summable (fun N => poisPi (rsMean n d) N *
      (rsH q η t N + Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsHR q η (tRe q x) N *
          (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) +
        K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N))) :=
    (hs12.add hYterm.1).congr fun N => by ring
  refine ⟨hS, ?_⟩
  calc rsExp n d (fun N => ‖rsF q t N‖ ^ 2 / max 1 (K⁻¹ * rsF q (tRe q x) N))
      ≤ rsExp n d (fun N => rsH q η t N + Real.exp (2 * ζ * (rsEdges N : ℝ)) *
          rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0) +
        K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N)) :=
        rs_poisPiExp_mono hlam hS hs123 hpt
    _ = rsExp n d (rsH q η t) + rsExp n d (fun N => Real.exp (2 * ζ * (rsEdges N : ℝ)) *
          rsHR q η (tRe q x) N * (if K < rsF q (tRe q x) N then (1 : ℝ) else 0)) +
        rsExp n d (fun N => K * (Real.exp (2 * ζ * (rsEdges N : ℝ)) * rsY q η (tRe q x) N)) := by
        unfold rsExp
        rw [rs_poisPiExp_add hs12 hYterm.1, rs_poisPiExp_add hHt hHterm.1]
    _ ≤ C₀ + 1 + 1 := add_le_add (add_le_add hHt' hHterm.2) hYterm.2
    _ = C₀ + 2 := by ring

end RSAnchoredAux

/-- **`eq:rs-anchored`** (Lemma C.4, Step 1).  At a real anchor `x ∈ (0,1]` with `|t(x)| ≤ t_*`,
given Lemma C.5(i) (`hloc`) and the estimates of Lemma C.7 at `x` (`hanc`): for all large `n` and
every complex `t` with `‖t‖ ≤ t_*`, `Re t ≤ t_*²` and `|M_t| ≤ e^ζ M_x` entrywise, where
`ζ = min(1/4, c₂γ²/(18dℓ²))`, we have `E_{𝖯_d}[e^{dm/n} |F_G(t)|] ≤ e^{d²} √(2C₀ + 4)`. -/
theorem rs_anchored {q : ℕ} (hq : 3 ≤ q) {d η tstar C₀ C₁ c₂ γ x : ℝ} (hd : 0 < d)
    (hC₁ : 0 < C₁) (hc₂0 : 0 < c₂) (hc₂1 : c₂ ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hx0 : 0 < x) (hx1 : x ≤ 1) (htx : |tRe q x| ≤ tstar)
    (hloc : ∀ n : ℕ, 0 < n → ∀ t : ℂ, ‖t‖ ≤ tstar → t.re ≤ tstar ^ 2 →
      Summable (fun N => poisPi (rsMean n d) N * rsH q η t N) ∧
        |rsExp n d (rsH q η t)| ≤ C₀)
    (hanc : ∀ᶠ n : ℕ in atTop,
      rsExp n d (rsY q η (tRe q x)) ≤ Real.exp (-(γ * n)) ∧
      rsExp n d (fun N => rsHR q η (tRe q x) N *
        {N' : RSGraph n | Real.exp (γ * n / 4) < rsF q (tRe q x) N'}.indicator
          (fun _ => (1 : ℝ)) N) ≤
        C₁ * Real.exp (-(c₂ * γ ^ 2 * n / rsEll x ^ 2))) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℂ, ‖t‖ ≤ tstar → t.re ≤ tstar ^ 2 →
      (∀ a b : Fin q, ‖rsM q t a b‖ ≤
        Real.exp (min (1 / 4) (c₂ * γ ^ 2 / (18 * d * rsEll x ^ 2))) * rsM q (tRe q x) a b) →
      rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) ≤
        Real.exp (d ^ 2) * Real.sqrt (2 * C₀ + 4) := by
  have hℓ : 1 ≤ rsEll x := RSAnchoredAux.rsEll_ge_one hx0 hx1
  have hℓ0 : 0 < rsEll x := lt_of_lt_of_le one_pos hℓ
  have hℓ2 : 1 ≤ rsEll x ^ 2 := one_le_pow₀ hℓ
  -- the comparison exponent `ζ`
  obtain ⟨ζ, hζdef⟩ : ∃ ζ, ζ = min (1 / 4) (c₂ * γ ^ 2 / (18 * d * rsEll x ^ 2)) := ⟨_, rfl⟩
  rw [← hζdef]
  have hζ0 : 0 ≤ ζ := hζdef ▸ le_min (by norm_num) (by positivity)
  have hζ1 : ζ ≤ 1 / 4 := hζdef ▸ min_le_left _ _
  have hζ2 : 18 * d * rsEll x ^ 2 * ζ ≤ c₂ * γ ^ 2 := by
    have h : ζ ≤ c₂ * γ ^ 2 / (18 * d * rsEll x ^ 2) := hζdef ▸ min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have h4ζ : Real.exp (4 * ζ) - 1 ≤ 8 * ζ := by
    have := RSAnchoredAux.exp_sub_one_le_two_mul (y := 4 * ζ) (by linarith) (by linarith)
    linarith
  -- `8ζd ≤ γ` and `9ζd ≤ κ := c₂γ²/(2ℓ²)`
  have hζγ : 8 * ζ * d ≤ γ := by
    have hγ2 : γ ^ 2 ≤ γ := by nlinarith
    have hc₂γ : c₂ * γ ^ 2 ≤ γ := by nlinarith [sq_nonneg γ]
    have hdζ : 0 ≤ d * ζ := by positivity
    have : 18 * d * ζ ≤ 18 * d * rsEll x ^ 2 * ζ := by nlinarith
    nlinarith
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = c₂ * γ ^ 2 / (2 * rsEll x ^ 2) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := hκ ▸ by positivity
  have hζκ : 9 * ζ * d ≤ κ := by
    rw [hκ, le_div_iff₀ (by positivity)]
    nlinarith
  have hκ2 : ∀ r : ℝ, c₂ * γ ^ 2 * r / rsEll x ^ 2 = 2 * (κ * r) := by
    intro r; rw [hκ]; field_simp
  -- the real anchor lies in the domain of Lemma C.5(i); hence `C₀ ≥ 0`
  have htx_norm : ‖((tRe q x : ℝ) : ℂ)‖ ≤ tstar := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact htx
  have htx_re : ((tRe q x : ℝ) : ℂ).re ≤ tstar ^ 2 := by
    rw [Complex.ofReal_re]
    exact (rs_tRe_nonpos (by omega) hx0.le hx1).trans (sq_nonneg _)
  have hC₀ : 0 ≤ C₀ := (abs_nonneg _).trans (hloc 1 one_pos _ htx_norm htx_re).2
  have hC₀C₁ : 0 ≤ C₀ * C₁ := mul_nonneg hC₀ hC₁.le
  -- the thresholds on `n`
  have hev1 : ∀ᶠ n : ℕ in atTop, 2 * d ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev2 : ∀ᶠ n : ℕ in atTop, C₀ * C₁ / κ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hanc, hev1, hev2] with n hn hn2d hnbig
  obtain ⟨hY, hHI⟩ := hn
  intro t ht1 ht2 hM
  have hn' : (0 : ℝ) < n := by linarith
  have hn0 : 0 < n := by exact_mod_cast hn'
  have hK1 : 1 ≤ Real.exp (γ * n / 4) := Real.one_le_exp (by positivity)
  have hK0 : 0 < Real.exp (γ * n / 4) := Real.exp_pos _
  -- `E H ≤ C₀` (Lemma C.5(i) at the anchor)
  have hEH : rsExp n d (rsHR q η (tRe q x)) ≤ C₀ := by
    have h := (hloc n hn0 _ htx_norm htx_re).2
    have e : rsExp n d (rsH q η ((tRe q x : ℝ) : ℂ)) = rsExp n d (rsHR q η (tRe q x)) := by
      unfold rsExp poisPiExp
      exact tsum_congr fun N => by rw [rs_rsH_ofReal]
    rw [e] at h
    exact (le_abs_self _).trans h
  -- the two error terms of `eq:rs-complex` are at most `1`
  have hsmallH : Real.exp (9 * (Real.exp (4 * ζ) - 1) * d * n / 8) * C₀ *
      (C₁ * Real.exp (-(c₂ * γ ^ 2 * n / rsEll x ^ 2))) ≤ 1 := by
    have hdn : 0 ≤ d * n := by positivity
    have ha : 9 * (Real.exp (4 * ζ) - 1) * d * n / 8 ≤ κ * n := by
      have h1 := mul_le_mul_of_nonneg_right h4ζ hdn
      have h2 := mul_le_mul_of_nonneg_right hζκ hn'.le
      nlinarith
    have hκn : C₀ * C₁ ≤ κ * n := by
      rw [div_le_iff₀ hκ0] at hnbig; linarith
    have hexp : C₀ * C₁ ≤ Real.exp (κ * n) := by
      have := Real.add_one_le_exp (κ * n); linarith
    calc Real.exp (9 * (Real.exp (4 * ζ) - 1) * d * n / 8) * C₀ *
          (C₁ * Real.exp (-(c₂ * γ ^ 2 * n / rsEll x ^ 2)))
        = C₀ * C₁ * (Real.exp (9 * (Real.exp (4 * ζ) - 1) * d * n / 8) *
            Real.exp (-(2 * (κ * n)))) := by rw [hκ2]; ring
      _ ≤ Real.exp (κ * n) * (Real.exp (κ * n) * Real.exp (-(2 * (κ * n)))) :=
          mul_le_mul hexp (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ha)
            (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le
      _ = 1 := by
          rw [← Real.exp_add, ← Real.exp_add,
            show κ * n + (κ * n + -(2 * (κ * n))) = 0 by ring, Real.exp_zero]
  have hsmallY : Real.exp (γ * n / 4) ^ 2 *
      (Real.exp ((Real.exp (4 * ζ) - 1) * d * n / 2) * Real.exp (-(γ * n))) ≤ 1 := by
    rw [RSAnchoredAux.exp_sq, ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
    have hdn : 0 ≤ d * n := by positivity
    have h1 := mul_le_mul_of_nonneg_right h4ζ hdn
    have h2 := mul_le_mul_of_nonneg_right hζγ hn'.le
    nlinarith
  have hHterm := RSAnchoredAux.bound_H_term (n := n) hq hd.le hx0 hx1 hζ0 hC₀ hEH hHI hsmallH
  have hYterm := RSAnchoredAux.bound_Y_term (n := n) (ζ := ζ) hq hd.le hx0 hx1 hK0.le hY hsmallY
  have hloc_t := hloc n hn0 t ht1 ht2
  have hFU := RSAnchoredAux.bound_FU (n := n) hq hd.le hx0 hx1 hK0 hM hloc_t.1
    ((le_abs_self _).trans hloc_t.2) hHterm hYterm
  have hUps := RSAnchoredAux.bound_Ups (n := n) hq hd hx0 hx1 hK1 hn0 hn2d
  -- the final Cauchy–Schwarz with the weight `Υ`
  have hU0 : ∀ N : RSGraph n, 0 < max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N) :=
    fun N => lt_of_lt_of_le one_pos (le_max_left _ _)
  have ef : ∀ N : RSGraph n, (Real.exp (d * (rsEdges N : ℝ) / n) *
      Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) ^ 2 =
      Real.exp (2 * d / n * (rsEdges N : ℝ)) *
        max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N) := by
    intro N
    rw [mul_pow, Real.sq_sqrt (hU0 N).le, RSAnchoredAux.exp_sq]
    congr 2
    ring
  have eg : ∀ N : RSGraph n, (‖rsF q t N‖ /
      Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) ^ 2 =
      ‖rsF q t N‖ ^ 2 / max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N) := by
    intro N
    rw [div_pow, Real.sq_sqrt (hU0 N).le]
  have efg : ∀ N : RSGraph n, Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖ =
      (Real.exp (d * (rsEdges N : ℝ) / n) *
        Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) *
      (‖rsF q t N‖ / Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) := by
    intro N
    have : Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N)) ≠ 0 :=
      (Real.sqrt_pos.mpr (hU0 N)).ne'
    field_simp
  have hf2 : Summable fun N => poisPi (rsMean n d) N * (Real.exp (d * (rsEdges N : ℝ) / n) *
      Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) ^ 2 :=
    hUps.1.congr fun N => by rw [ef N]
  have hg2 : Summable fun N => poisPi (rsMean n d) N * (‖rsF q t N‖ /
      Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) ^ 2 :=
    hFU.1.congr fun N => by rw [eg N]
  have hCS := RSAnchoredAux.rsExp_mul_le_sqrt hd.le
    (fun N => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    (fun N => div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hf2 hg2
  have e1 : rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) =
      rsExp n d (fun N => (Real.exp (d * (rsEdges N : ℝ) / n) *
        Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) *
      (‖rsF q t N‖ / Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N)))) := by
    unfold rsExp poisPiExp
    exact tsum_congr fun N => by dsimp only; rw [efg N]
  have e2 : rsExp n d (fun N => (Real.exp (d * (rsEdges N : ℝ) / n) *
      Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) ^ 2) =
      rsExp n d (fun N => Real.exp (2 * d / n * (rsEdges N : ℝ)) *
        max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N)) := by
    unfold rsExp poisPiExp
    exact tsum_congr fun N => by dsimp only; rw [ef N]
  have e3 : rsExp n d (fun N => (‖rsF q t N‖ /
      Real.sqrt (max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N))) ^ 2) =
      rsExp n d (fun N => ‖rsF q t N‖ ^ 2 /
        max 1 ((Real.exp (γ * n / 4))⁻¹ * rsF q (tRe q x) N)) := by
    unfold rsExp poisPiExp
    exact tsum_congr fun N => by dsimp only; rw [eg N]
  have hfinal : Real.sqrt (2 * Real.exp (2 * d ^ 2)) * Real.sqrt (C₀ + 2) =
      Real.exp (d ^ 2) * Real.sqrt (2 * C₀ + 4) := by
    rw [← Real.sqrt_mul (by positivity),
      show 2 * Real.exp (2 * d ^ 2) * (C₀ + 2) = Real.exp (d ^ 2) ^ 2 * (2 * C₀ + 4) by
        rw [RSAnchoredAux.exp_sq]; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le]
  rw [e1]
  refine hCS.trans ?_
  rw [e2, e3, ← hfinal]
  exact mul_le_mul (Real.sqrt_le_sqrt hUps.2) (Real.sqrt_le_sqrt hFU.2) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)


end

end ERZeroFreeness
