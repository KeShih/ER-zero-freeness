/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSTilt
import ERZeroFreeness.Multinomial
import ERZeroFreeness.SecondMoment

/-!
# Appendix C: local pair sums (`app:rs-local`, Lemma C.5 `lem:rs-local`)

* `rs_exists_params`: the parameters of `eq:rs-parameters` (`t_*`, `η`, with `θ_* < 1`) exist;
* `rs_entropy_window` (**`eq:rs-entropy`**): on the window,
  `D(R‖R̄) ≥ q²/(2(1 + q²η)) ‖R - R̄‖_F²`;
* `rs_local_sum` (**`eq:rs-local`**): the windowed exponential pair sums are bounded uniformly in
  `n ≥ 1`, in `t` with `|t| ≤ t_*`, `Re t ≤ t_*²` and in the exponent `p' ∈ [0, p]`;
* `rs_local_i` (**Lemma C.5(i)**): `|E_{𝖯_d} H_G(t)| ≤ C₀`;
* `rs_local_ii` (**Lemma C.5(ii)**): at real anchors, `E_{𝖯_d}[H 1_ℰ] ≤ C₁ Pr_𝖰[ℰ]^{1 - 1/p}`.

**Deviation from the paper.**  The paper's constants `C₀ = (1-θ_*)^{-(q²-1)}` and
`C₁ = (1-pθ_*)^{-(q²-1)/p}` come from Agrawal's sharp multinomial bound; here
`exists_sum_exp_empKL_le` (`thm:multinomial-moment` with a constant uniform in `n`) gives *some*
constants, uniform in `n`, `t` and the anchor, which is all that Appendix C uses.  The
`t`-conditions are closed (`‖t‖ ≤ t_*`, `Re t ≤ t_*²`) and the anchors may include `x = 0`
(`t = -1/(q-1)`); `p ≥ 1` is any exponent with `p θ_* < 1` (the paper's `p = 2/(1+θ_*)` is one).

## Proof

* `eq:rs-entropy`: write `empKL` of the pair map `v ↦ (σ_v, τ_v)` as
  `∑_c [R_c log(R_c/c₀) - R_c + c₀]` (`c₀ = q⁻²`, `∑ R = 1`) and use, cell by cell,
  `(r - c)²/(2M) ≤ r log(r/c) - r + c` for `0 ≤ r, c ≤ M`, `c > 0` (cases `r ≤ c` via
  `Real.self_lt_sinh_iff`, `r > c` via `Real.hasSum_pow_div_log_of_abs_lt_one`), with
  `M = q⁻² + η` (on the window `|R_c - q⁻²| < η`).
* `eq:rs-local`: by `TwoReplicaAux.sum_re_le` and `TwoReplicaAux.sum_overlap_sq`,
  `Re(n φ_t(R)) ≤ (dn/2) t_*² q² ‖R - R̄‖_F² ≤ θ_* n D(R‖R̄)` on the window; drop the window, use
  `SecondMomentAux.sum_sum_pair_eq` to pass to maps `Fin n → Fin q × Fin q`, and apply
  `exists_sum_exp_empKL_le` with `θ = p θ_*` and `k = q²`.
* (i): `rs_two_tilt`, `Complex.hasSum_re`, `hasSum_sum` over the window; `|Re e^w| ≤ e^{Re w}`; the
  bound with `p' = 1`.
* (ii): `rs_pair_tilt_pt` with `Φ = 1_ℰ` gives
  `E[H 1_ℰ] = q^{-2n} ∑_{window} e^{n φ_x(R)} 𝖯^{σ,τ}_d(ℰ)`; finite weighted Hölder
  (`Real.inner_le_weight_mul_Lp_of_nonneg`) with exponents `p`, `p/(p-1)`, `𝖯^{σ,τ}_d(ℰ) ≤ 1`,
  `rs_local_sum` with `p' = p`, and the reindexing `(Fin n → [q]²) ≃ (Fin n → [q])²`
  (`SecondMomentAux.sum_sum_pair_eq`) identifying `rsQProb` with the average of `𝖯^{σ,τ}_d(ℰ)`.
* Parameters: choose `t_* ∈ (s_*, 1)` with `d t_*² < 1`, then `η` small.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSLocalAux

theorem kl_term_ge {c r M : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hcM : c ≤ M) (hrM : r ≤ M) :
    (r - c) ^ 2 / (2 * M) ≤ r * Real.log (r / c) - r + c := by
  have hM : 0 < M := lt_of_lt_of_le hc hcM
  rcases hr.eq_or_lt with h0 | hpos
  · subst h0
    rw [div_le_iff₀ (by positivity)]
    simp only [zero_mul, sub_zero, zero_sub, zero_add, neg_sq]
    nlinarith
  rcases le_or_gt r c with hrc | hrc
  · have key : (r - c) ^ 2 / (2 * c) ≤ r * Real.log (r / c) - r + c := by
      have hy : 0 < r / c := div_pos hpos hc
      have hlog : (r / c - (r / c)⁻¹) / 2 ≤ Real.log (r / c) := by
        rcases eq_or_lt_of_le (show r / c ≤ 1 from (div_le_one hc).2 hrc) with h1 | h1
        · rw [h1]; simp
        · have hx : 1 < (r / c)⁻¹ := (one_lt_inv₀ hy).2 h1
          have h := Real.self_lt_sinh_iff.mpr (Real.log_pos hx)
          rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (by positivity), inv_inv,
            Real.log_inv] at h
          linarith
      have e1 : r * ((r / c - (r / c)⁻¹) / 2) = (r ^ 2 - c ^ 2) / (2 * c) := by
        field_simp
      have h2 : r * ((r / c - (r / c)⁻¹) / 2) ≤ r * Real.log (r / c) :=
        mul_le_mul_of_nonneg_left hlog hr
      have e3 : (r - c) ^ 2 / (2 * c) = (r ^ 2 - c ^ 2) / (2 * c) - r + c := by
        field_simp
        ring
      linarith
    calc (r - c) ^ 2 / (2 * M) ≤ (r - c) ^ 2 / (2 * c) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      _ ≤ _ := key
  · have key : (r - c) ^ 2 / (2 * r) ≤ r * Real.log (r / c) - r + c := by
      set x := 1 - c / r with hx
      have hcr : c / r < 1 := (div_lt_one hpos).2 hrc
      have hx0 : 0 ≤ x := by rw [hx]; linarith
      have hx1 : x < 1 := by rw [hx]; have : 0 < c / r := div_pos hc hpos; linarith
      have hs := Real.hasSum_pow_div_log_of_abs_lt_one
        (show |x| < 1 by rw [abs_of_nonneg hx0]; exact hx1)
      have hle := sum_le_hasSum (Finset.range 2) (fun i _ => by positivity) hs
      norm_num [Finset.sum_range_succ] at hle
      have h1x : 1 - x = c / r := by rw [hx]; ring
      rw [h1x] at hle
      have hlog : Real.log (r / c) = -Real.log (c / r) := by
        rw [← Real.log_inv, inv_div]
      have hmain : r * (x + x ^ 2 / 2) ≤ r * Real.log (r / c) := by
        rw [hlog]; exact mul_le_mul_of_nonneg_left hle hr
      have e1 : r * x = r - c := by rw [hx]; field_simp
      have e2 : (r - c) ^ 2 / (2 * r) = r * x ^ 2 / 2 := by
        rw [← e1]; field_simp
      have e3 : r * (x + x ^ 2 / 2) = r * x + r * x ^ 2 / 2 := by ring
      linarith
    calc (r - c) ^ 2 / (2 * M) ≤ (r - c) ^ 2 / (2 * r) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
      _ ≤ _ := key

theorem sum_fiberCard' {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι → κ) :
    ∑ c : κ, fiberCard f c = Fintype.card ι := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset ι))
    (t := (Finset.univ : Finset κ)) (f := f) (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at this
  exact this.symm

/-- `‖R - R̄‖_F² = ∑_{a,b} R_{ab}² - q⁻²` (the entries of `R` sum to one). -/
theorem ovDev_eq {n q : ℕ} (hq : 1 ≤ q) (hn : 0 < n) (σ τ : Fin n → Fin q) :
    rsOvDev σ τ = ∑ a, ∑ b, overlap σ τ a b ^ 2 - 1 / (q : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hsum : ∑ a, ∑ b, overlap σ τ a b = 1 := by
    have h := sum_fiberCard' (fun v => (σ v, τ v))
    rw [Fintype.sum_prod_type, Fintype.card_fin] at h
    simp only [overlap, ← Finset.sum_div]
    rw [div_eq_one_iff_eq hnpos.ne']
    exact_mod_cast h
  unfold rsOvDev
  have e : ∀ a b, (overlap σ τ a b - 1 / (q : ℝ) ^ 2) ^ 2 =
      overlap σ τ a b ^ 2 - 2 / (q : ℝ) ^ 2 * overlap σ τ a b + 1 / (q : ℝ) ^ 4 := by
    intro a b; field_simp; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The real part of `n φ^d_{t,t̄}(R)`: `Re(n φ) ≤ (dn/2) T² q² ‖R - R̄‖_F²` for `‖t‖ ≤ T`,
`Re t ≤ T²`. -/
theorem re_rsPairExpo_le {n q : ℕ} (hq : 2 ≤ q) (hn : 0 < n) {d T : ℝ} (hd : 0 ≤ d) {t : ℂ}
    (ht : ‖t‖ ≤ T) (htre : t.re ≤ T ^ 2) (σ τ : Fin n → Fin q) :
    (rsPairExpo q n d t σ τ).re ≤ d * n / 2 * T ^ 2 * (q : ℝ) ^ 2 * rsOvDev σ τ := by
  have h1 := TwoReplicaAux.sum_re_le hq σ τ ht htre
  have hre : (rsPairExpo q n d t σ τ).re = d / (2 * n) * ∑ u, ∑ v,
      ((1 + t * edgeA q σ s(u, v)) * (starRingEnd ℂ) (1 + t * edgeA q τ s(u, v)) - 1).re := by
    unfold rsPairExpo
    rw [Complex.re_ofReal_mul]
    simp only [Complex.re_sum, rs_edgeA_eq]
    rfl
  rw [hre]
  have hdn : 0 ≤ d / (2 * n) := by positivity
  have h2 := mul_le_mul_of_nonneg_left h1 hdn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : (q : ℝ) ^ 2 * ∑ c, ((fiberCard (fun v => (σ v, τ v)) c : ℕ) : ℝ) ^ 2 - (n : ℝ) ^ 2
      = (n : ℝ) ^ 2 * ((q : ℝ) ^ 2 * rsOvDev σ τ) := by
    have hs := TwoReplicaAux.sum_overlap_sq σ τ
    rw [ovDev_eq (by omega) hn σ τ, hs]
    have hq' : (q : ℝ) ≠ 0 := by
      have : (2 : ℝ) ≤ q := by exact_mod_cast hq
      positivity
    field_simp
  rw [h3] at h2
  calc _ ≤ d / (2 * n) * (T ^ 2 * ((n : ℝ) ^ 2 * ((q : ℝ) ^ 2 * rsOvDev σ τ))) := h2
    _ = _ := by field_simp

/-- At a real `t`, `n φ^s_{t,t̄}(R) = n φ^s_{x,x}(R)` is real. -/
theorem rsPairExpo_ofReal {n q : ℕ} (s t : ℝ) (σ τ : Fin n → Fin q) :
    rsPairExpo q n s (t : ℂ) σ τ = ((rsPairExpoR q n s t σ τ : ℝ) : ℂ) := by
  have hM : ∀ a b : Fin q, rsM q (t : ℂ) a b = ((rsM q t a b : ℝ) : ℂ) := by
    intro a b; unfold rsM; push_cast; rfl
  unfold rsPairExpo rsPairExpoR
  simp only [hM, Complex.conj_ofReal]
  push_cast
  rfl

/-- The entries of `M_t` are nonnegative for `t ∈ [-1/(q-1), 1]`. -/
theorem rsM_nonneg {q : ℕ} (hq : 2 ≤ q) {t : ℝ} (ht0 : -1 / ((q : ℝ) - 1) ≤ t) (ht1 : t ≤ 1)
    (a b : Fin q) : 0 ≤ rsM q t a b := by
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  rw [rsM, rs_rsA_cast_eq_aa]
  unfold TwoReplicaAux.aa
  split_ifs
  · rw [div_le_iff₀ hq1] at ht0; linarith
  · linarith

theorem cpMean_rsPairK_nonneg {n q : ℕ} (hq : 2 ≤ q) {d t : ℝ} (hd : 0 ≤ d)
    (ht0 : -1 / ((q : ℝ) - 1) ≤ t) (ht1 : t ≤ 1) (ξ : Fin n → Fin q × Fin q)
    (e : Fin n × Fin n) : 0 ≤ cpMean (rsPairK q d t) ξ e := by
  unfold cpMean rsPairK
  exact div_nonneg (mul_nonneg (mul_nonneg hd (rsM_nonneg hq ht0 ht1 _ _))
    (rsM_nonneg hq ht0 ht1 _ _)) (by positivity)

/-- The probability of a set under a product Poisson law, as a convergent series. -/
theorem hasSum_poisPi_indicator {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    (E : Set (ι → ℕ)) :
    HasSum (fun N => poisPi lam N * E.indicator (fun _ => (1 : ℝ)) N)
      (poisPiExp lam (fun N => E.indicator (fun _ => (1 : ℝ)) N)) := by
  have hs := (rs_hasSum_poisPi hlam).summable
  have h : Summable (fun N => poisPi lam N * E.indicator (fun _ => (1 : ℝ)) N) := by
    refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hs
    · exact mul_nonneg (rs_poisPi_nonneg hlam N)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) N)
    · have h1 : E.indicator (fun _ => (1 : ℝ)) N ≤ 1 := by
        unfold Set.indicator; split_ifs <;> norm_num
      calc poisPi lam N * E.indicator (fun _ => (1 : ℝ)) N ≤ poisPi lam N * 1 :=
            mul_le_mul_of_nonneg_left h1 (rs_poisPi_nonneg hlam N)
        _ = poisPi lam N := mul_one _
  exact h.hasSum

theorem poisPiExp_indicator_nonneg {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (E : Set (ι → ℕ)) :
    0 ≤ poisPiExp lam (fun N => E.indicator (fun _ => (1 : ℝ)) N) :=
  tsum_nonneg fun N => mul_nonneg (rs_poisPi_nonneg hlam N)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) N)

theorem poisPiExp_indicator_le_one {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ i, 0 ≤ lam i) (E : Set (ι → ℕ)) :
    poisPiExp lam (fun N => E.indicator (fun _ => (1 : ℝ)) N) ≤ 1 := by
  have hs := rs_hasSum_poisPi hlam
  refine le_trans (Summable.tsum_le_tsum (fun N => ?_) (hasSum_poisPi_indicator hlam E).summable
    hs.summable) (le_of_eq hs.tsum_eq)
  have h1 : E.indicator (fun _ => (1 : ℝ)) N ≤ 1 := by
    unfold Set.indicator; split_ifs <;> norm_num
  calc poisPi lam N * E.indicator (fun _ => (1 : ℝ)) N ≤ poisPi lam N * 1 :=
        mul_le_mul_of_nonneg_left h1 (rs_poisPi_nonneg hlam N)
    _ = poisPi lam N := mul_one _

/-- `E_{𝖯_d}[w(σ) w(τ) 1_ℰ] = e^{n φ^d_{x,x}(R)} 𝖯^{σ,τ}_d(ℰ)`, as a convergent series. -/
theorem hasSum_pair_tilt_indicator {n q : ℕ} (hq : 2 ≤ q) {d t : ℝ} (hd : 0 ≤ d)
    (ht0 : -1 / ((q : ℝ) - 1) ≤ t) (ht1 : t ≤ 1) (σ τ : Fin n → Fin q) (E : Set (RSGraph n)) :
    HasSum (fun N => poisPi (rsMean n d) N *
        (rsW q t N σ * rsW q t N τ * E.indicator (fun _ => (1 : ℝ)) N))
      (Real.exp (rsPairExpoR q n d t σ τ) *
        poisPiExp (cpMean (rsPairK q d t) (fun v => (σ v, τ v)))
          (fun N => E.indicator (fun _ => (1 : ℝ)) N)) := by
  have h := (hasSum_poisPi_indicator (cpMean_rsPairK_nonneg hq hd ht0 ht1
    (fun v => (σ v, τ v))) E).mul_left (Real.exp (rsPairExpoR q n d t σ τ))
  refine h.congr_fun fun N => ?_
  rw [← mul_assoc, rs_pair_tilt_pt, mul_assoc]

end RSLocalAux

/-- **`eq:rs-parameters`.** Given `d > 0` and `s_* = |t(x_*)| ∈ [0, 1/(q-1)]` with `d s_*² < 1`,
there are `t_* ∈ (s_*, 1)` with `d t_*² < 1` and `η ∈ (0,1]` with `θ_* = d t_*²(1 + q²η) < 1`. -/
theorem rs_exists_params {q : ℕ} (hq : 3 ≤ q) {d sstar : ℝ} (hd : 0 < d) (hs0 : 0 ≤ sstar)
    (hs1 : sstar ≤ 1 / ((q : ℝ) - 1)) (hds : d * sstar ^ 2 < 1) :
    ∃ tstar η : ℝ, sstar < tstar ∧ tstar < 1 ∧ d * tstar ^ 2 < 1 ∧ 0 < η ∧ η ≤ 1 ∧
      rsTheta q d tstar η < 1 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have ha1 : sstar < 1 := by
    have : 1 / ((q : ℝ) - 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  set a := sstar with ha
  set δ := min ((1 - a) / 2) ((1 - d * a ^ 2) / (2 * d * (2 * a + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (div_pos (by linarith) (by positivity))
  have hδ1 : δ ≤ (1 - a) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (1 - d * a ^ 2) / (2 * d * (2 * a + 1)) := min_le_right _ _
  set t := a + δ with ht
  have htd : d * t ^ 2 < 1 := by
    have h1 : t ^ 2 ≤ a ^ 2 + δ * (2 * a + 1) := by
      rw [ht]; nlinarith
    have h2 : d * (δ * (2 * a + 1)) ≤ (1 - d * a ^ 2) / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * d * (2 * a + 1))] at hδ2
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    nlinarith
  have hX : 0 ≤ d * t ^ 2 * (q : ℝ) ^ 2 := by positivity
  set e := (1 - d * t ^ 2) / (2 * (d * t ^ 2 * (q : ℝ) ^ 2 + 1)) with he
  have he0 : 0 < e := div_pos (by linarith) (by positivity)
  have hE : d * t ^ 2 * (q : ℝ) ^ 2 * e ≤ (1 - d * t ^ 2) / 2 := by
    rw [he, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨t, min 1 e, by linarith, by linarith, htd, lt_min one_pos he0, min_le_left _ _, ?_⟩
  unfold rsTheta
  have hm : min 1 e ≤ e := min_le_right _ _
  nlinarith [mul_le_mul_of_nonneg_left hm hX]

/-- **`eq:rs-entropy`.** If `‖R_{σ,τ} - R̄‖_F < η` then
`D(R_{σ,τ} ‖ R̄) ≥ q²/(2(1 + q²η)) ‖R_{σ,τ} - R̄‖_F²`, where `D(R‖R̄)` is the empirical relative
entropy of the pair map `v ↦ (σ_v, τ_v)` with respect to the uniform law on `[q]²`. -/
theorem rs_entropy_window {n q : ℕ} (hq : 1 ≤ q) (hn : 0 < n) {η : ℝ} (hη : 0 < η)
    (σ τ : Fin n → Fin q) (hw : rsOvDev σ τ < η ^ 2) :
    (q : ℝ) ^ 2 / (2 * (1 + (q : ℝ) ^ 2 * η)) * rsOvDev σ τ ≤ empKL (fun v => (σ v, τ v)) := by
  set f : Fin n → Fin q × Fin q := fun v => (σ v, τ v) with hf
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set c0 : ℝ := 1 / (q : ℝ) ^ 2 with hc0
  have hc0pos : 0 < c0 := by positivity
  set R : Fin q × Fin q → ℝ := fun c => (fiberCard f c : ℝ) / n with hR
  have hRnn : ∀ c, 0 ≤ R c := fun c => by positivity
  have hsumR : ∑ c, R c = 1 := by
    simp only [hR, ← Finset.sum_div]
    rw [← Nat.cast_sum, RSLocalAux.sum_fiberCard', Fintype.card_fin, div_self hnpos.ne']
  have hsumc0 : ∑ _c : Fin q × Fin q, c0 = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, hc0]
    push_cast
    field_simp
  have hdev : rsOvDev σ τ = ∑ c, (R c - c0) ^ 2 := by
    unfold rsOvDev overlap
    rw [Fintype.sum_prod_type]
  have hKL : empKL f = ∑ c, (R c * Real.log (R c / c0) - R c + c0) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsumR, hsumc0, sub_add_cancel]
    unfold empKL
    refine Finset.sum_congr rfl fun c _ => ?_
    have e : ((Fintype.card (Fin q × Fin q) : ℕ) : ℝ) * (fiberCard f c : ℝ) /
        (Fintype.card (Fin n) : ℝ) = R c / c0 := by
      simp only [Fintype.card_prod, Fintype.card_fin, hR, hc0]
      push_cast
      field_simp
    rw [e]
    simp only [Fintype.card_fin, hR]
  set M := c0 + η with hM
  have hterm : ∀ c, (R c - c0) ^ 2 / (2 * M) ≤ R c * Real.log (R c / c0) - R c + c0 := by
    intro c
    apply RSLocalAux.kl_term_ge hc0pos (hRnn c) (by rw [hM]; linarith)
    have h1 : (R c - c0) ^ 2 ≤ rsOvDev σ τ := by
      rw [hdev]
      exact Finset.single_le_sum (f := fun c => (R c - c0) ^ 2) (fun c _ => sq_nonneg _)
        (Finset.mem_univ c)
    have h2 : |R c - c0| < η := abs_lt_of_sq_lt_sq (lt_of_le_of_lt h1 hw) hη.le
    have h3 := le_abs_self (R c - c0)
    rw [hM]; linarith
  calc (q : ℝ) ^ 2 / (2 * (1 + (q : ℝ) ^ 2 * η)) * rsOvDev σ τ
      = ∑ c, (R c - c0) ^ 2 / (2 * M) := by
        rw [hdev, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hM, hc0]
        field_simp
    _ ≤ ∑ c, (R c * Real.log (R c / c0) - R c + c0) := Finset.sum_le_sum fun c _ => hterm c
    _ = empKL f := hKL.symm

/-- **`eq:rs-local`.** There is `C > 0` such that for all `n ≥ 1`, all complex `t` with
`‖t‖ ≤ t_*`, `Re t ≤ t_*²`, and all `p' ∈ [0, p]`:
`E_{σ,τ}[1_{‖R - R̄‖_F < η} e^{p' n Re φ^d_{t,t̄}(R)}] ≤ C`  (`d ≥ 0`, `η > 0`, `p θ_* < 1`). -/
theorem rs_local_sum {q : ℕ} (hq : 2 ≤ q) {d tstar η p : ℝ} (hd : 0 ≤ d) (hη : 0 < η)
    (hp : 0 ≤ p) (hpθ : p * rsTheta q d tstar η < 1) :
    ∃ C > 0, ∀ n : ℕ, 0 < n → ∀ t : ℂ, ‖t‖ ≤ tstar → t.re ≤ tstar ^ 2 →
      ∀ p' : ℝ, 0 ≤ p' → p' ≤ p →
        (((q : ℝ) ^ n)⁻¹) ^ 2 *
          ∑ x ∈ rsWindow q n η, Real.exp (p' * (rsPairExpo q n d t x.1 x.2).re) ≤ C := by
  have hθ0 : 0 ≤ rsTheta q d tstar η := by unfold rsTheta; positivity
  obtain ⟨C, hC⟩ := exists_sum_exp_empKL_le (mul_nonneg hp hθ0) hpθ (q ^ 2)
  refine ⟨max C 1, by positivity, fun n hn t ht htre p' hp'0 hp'p => ?_⟩
  have hqpos : (0 : ℝ) < q := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hpt : ∀ x ∈ rsWindow q n η, Real.exp (p' * (rsPairExpo q n d t x.1 x.2).re) ≤
      Real.exp (p * rsTheta q d tstar η * n * empKL (fun v => (x.1 v, x.2 v))) := by
    intro x hx
    rw [rsWindow, Finset.mem_filter] at hx
    apply Real.exp_le_exp.2
    have h1 := RSLocalAux.re_rsPairExpo_le hq hn hd ht htre x.1 x.2
    have h2 := rs_entropy_window (by omega) hn hη x.1 x.2 hx.2
    have hK := empKL_nonneg (fun v => (x.1 v, x.2 v))
    have h3 : (rsPairExpo q n d t x.1 x.2).re ≤
        rsTheta q d tstar η * n * empKL (fun v => (x.1 v, x.2 v)) := by
      have e : d * n / 2 * tstar ^ 2 * (q : ℝ) ^ 2 * rsOvDev x.1 x.2 =
          rsTheta q d tstar η * n *
            ((q : ℝ) ^ 2 / (2 * (1 + (q : ℝ) ^ 2 * η)) * rsOvDev x.1 x.2) := by
        have hq2 : (0 : ℝ) < 1 + (q : ℝ) ^ 2 * η := by positivity
        unfold rsTheta
        field_simp
      have hθn : 0 ≤ rsTheta q d tstar η * n := by positivity
      calc _ ≤ _ := h1
        _ = _ := e
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hθn
    calc p' * (rsPairExpo q n d t x.1 x.2).re
        ≤ p' * (rsTheta q d tstar η * n * empKL (fun v => (x.1 v, x.2 v))) :=
          mul_le_mul_of_nonneg_left h3 hp'0
      _ ≤ p * (rsTheta q d tstar η * n * empKL (fun v => (x.1 v, x.2 v))) := by
          apply mul_le_mul_of_nonneg_right hp'p; positivity
      _ = _ := by ring
  have hsum1 : ∑ x ∈ rsWindow q n η, Real.exp (p' * (rsPairExpo q n d t x.1 x.2).re) ≤
      ∑ x : (Fin n → Fin q) × (Fin n → Fin q), Real.exp (p * rsTheta q d tstar η * n *
        empKL (fun v => (x.1 v, x.2 v))) :=
    (Finset.sum_le_sum hpt).trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => (Real.exp_pos _).le))
  have hsum2 : ∑ x : (Fin n → Fin q) × (Fin n → Fin q), Real.exp (p * rsTheta q d tstar η * n *
      empKL (fun v => (x.1 v, x.2 v))) ≤ C * ((q : ℝ) ^ 2) ^ n := by
    rw [Fintype.sum_prod_type]
    calc ∑ σ : Fin n → Fin q, ∑ τ : Fin n → Fin q, Real.exp (p * rsTheta q d tstar η * n *
            empKL (fun v => (σ v, τ v)))
        = ∑ f : Fin n → Fin q × Fin q, Real.exp (p * rsTheta q d tstar η * n * empKL f) :=
          SecondMomentAux.sum_sum_pair_eq
            (fun f => Real.exp (p * rsTheta q d tstar η * n * empKL f))
      _ ≤ C * ((q : ℝ) ^ 2) ^ n := by
          have h := hC (Fin n) (Fin q × Fin q) (by simp [sq])
          convert h using 3 <;> simp
  calc (((q : ℝ) ^ n)⁻¹) ^ 2 *
        ∑ x ∈ rsWindow q n η, Real.exp (p' * (rsPairExpo q n d t x.1 x.2).re)
      ≤ (((q : ℝ) ^ n)⁻¹) ^ 2 * (C * ((q : ℝ) ^ 2) ^ n) :=
        mul_le_mul_of_nonneg_left (hsum1.trans hsum2) (by positivity)
    _ = C := by
        rw [← pow_mul, mul_comm 2 n, pow_mul]
        field_simp
    _ ≤ max C 1 := le_max_left _ _

/-- **Lemma C.5(i).** There is `C₀ > 0` such that for all `n ≥ 1` and all complex `t` with
`‖t‖ ≤ t_*`, `Re t ≤ t_*²`: `H_G(t)` is `𝖯_d`-summable and `|E_{𝖯_d} H_G(t)| ≤ C₀`. -/
theorem rs_local_i {q : ℕ} (hq : 2 ≤ q) {d tstar η : ℝ} (hd : 0 ≤ d) (hη : 0 < η)
    (hθ : rsTheta q d tstar η < 1) :
    ∃ C₀ > 0, ∀ n : ℕ, 0 < n → ∀ t : ℂ, ‖t‖ ≤ tstar → t.re ≤ tstar ^ 2 →
      Summable (fun N => poisPi (rsMean n d) N * rsH q η t N) ∧
        |rsExp n d (rsH q η t)| ≤ C₀ := by
  obtain ⟨C, hC0, hC⟩ := rs_local_sum (p := 1) hq hd hη zero_le_one (by rw [one_mul]; exact hθ)
  refine ⟨C, hC0, fun n hn t ht htre => ?_⟩
  set c := (((q : ℝ) ^ n)⁻¹) ^ 2 with hc
  have hx : ∀ x : (Fin n → Fin q) × (Fin n → Fin q), HasSum (fun N => poisPi (rsMean n d) N *
      (rsW q t N x.1 * starRingEnd ℂ (rsW q t N x.2)).re)
      (Complex.exp (rsPairExpo q n d t x.1 x.2)).re := by
    intro x
    simpa only [Complex.re_ofReal_mul] using Complex.hasSum_re (rs_two_tilt hd t x.1 x.2)
  have hH : HasSum (fun N => poisPi (rsMean n d) N * rsH q η t N)
      (c * ∑ x ∈ rsWindow q n η, (Complex.exp (rsPairExpo q n d t x.1 x.2)).re) := by
    have h := (hasSum_sum (s := rsWindow q n η) fun x _ => hx x).mul_left c
    refine h.congr_fun fun N => ?_
    simp only [rsH, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  refine ⟨hH.summable, ?_⟩
  rw [rsExp, poisPiExp, hH.tsum_eq]
  have hc0 : 0 ≤ c := by positivity
  calc |c * ∑ x ∈ rsWindow q n η, (Complex.exp (rsPairExpo q n d t x.1 x.2)).re|
      ≤ c * ∑ x ∈ rsWindow q n η, Real.exp (1 * (rsPairExpo q n d t x.1 x.2).re) := by
        rw [abs_mul, abs_of_nonneg hc0]
        apply mul_le_mul_of_nonneg_left _ hc0
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        rw [one_mul, ← Complex.norm_exp]
        exact Complex.abs_re_le_norm _
    _ ≤ C := hC n hn t ht htre 1 zero_le_one le_rfl

/-- **Lemma C.5(ii).** For `p ≥ 1` with `p θ_* < 1` there is `C₁ > 0` such that for all `n ≥ 1`,
every real anchor `t ∈ [-1/(q-1), 0]` with `|t| ≤ t_*` and every set `ℰ` of multigraphs:
`E_{𝖯_d}[H 1_ℰ] ≤ C₁ Pr_𝖰[ℰ]^{1 - 1/p}` (and the left side is a summable expectation). -/
theorem rs_local_ii {q : ℕ} (hq : 2 ≤ q) {d tstar η p : ℝ} (hd : 0 ≤ d) (hη : 0 < η)
    (hp : 1 ≤ p) (hpθ : p * rsTheta q d tstar η < 1) :
    ∃ C₁ > 0, ∀ n : ℕ, 0 < n → ∀ t : ℝ, -1 / ((q : ℝ) - 1) ≤ t → t ≤ 0 → |t| ≤ tstar →
      ∀ E : Set (RSGraph n),
        Summable (fun N => poisPi (rsMean n d) N *
          (rsHR q η t N * E.indicator (fun _ => (1 : ℝ)) N)) ∧
        rsExp n d (fun N => rsHR q η t N * E.indicator (fun _ => (1 : ℝ)) N) ≤
          C₁ * rsQProb q n d t E ^ (1 - p⁻¹) := by
  obtain ⟨C, hC0, hC⟩ := rs_local_sum hq hd hη (by linarith) hpθ
  refine ⟨C ^ p⁻¹, Real.rpow_pos_of_pos hC0 _, fun n hn t ht0 ht1 htT E => ?_⟩
  have ht1' : t ≤ 1 := by linarith
  set c := (((q : ℝ) ^ n)⁻¹) ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  set P : (Fin n → Fin q) × (Fin n → Fin q) → ℝ := fun x =>
    poisPiExp (cpMean (rsPairK q d t) (fun v => (x.1 v, x.2 v)))
      (fun N => E.indicator (fun _ => (1 : ℝ)) N) with hPdef
  have hP0 : ∀ x, 0 ≤ P x := fun x =>
    RSLocalAux.poisPiExp_indicator_nonneg (RSLocalAux.cpMean_rsPairK_nonneg hq hd ht0 ht1' _) E
  have hP1 : ∀ x, P x ≤ 1 := fun x =>
    RSLocalAux.poisPiExp_indicator_le_one (RSLocalAux.cpMean_rsPairK_nonneg hq hd ht0 ht1' _) E
  have hH : HasSum (fun N => poisPi (rsMean n d) N *
      (rsHR q η t N * E.indicator (fun _ => (1 : ℝ)) N))
      (c * ∑ x ∈ rsWindow q n η, Real.exp (rsPairExpoR q n d t x.1 x.2) * P x) := by
    have h := (hasSum_sum (s := rsWindow q n η) fun x _ =>
      RSLocalAux.hasSum_pair_tilt_indicator hq hd ht0 ht1' x.1 x.2 E).mul_left c
    refine h.congr_fun fun N => ?_
    simp only [rsHR, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  refine ⟨hH.summable, ?_⟩
  rw [rsExp, poisPiExp, hH.tsum_eq]
  -- the law `𝖰` as an average over pairs of colourings
  have hQ : rsQProb q n d t E = c * ∑ x : (Fin n → Fin q) × (Fin n → Fin q), P x := by
    unfold rsQProb cpExp
    have hprod : (∏ _v : Fin n, ((q : ℝ) ^ 2)⁻¹) = c := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hc, inv_pow, inv_pow, ← pow_mul,
        ← pow_mul, mul_comm]
    simp only [hprod]
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    congr 1
    exact (SecondMomentAux.sum_sum_pair_eq (fun ξ => poisPiExp (cpMean (rsPairK q d t) ξ)
      (fun N => E.indicator (fun _ => (1 : ℝ)) N))).symm
  -- weighted Hölder over the window
  set w : (Fin n → Fin q) × (Fin n → Fin q) → ℝ := fun x => c * P x with hw
  set f : (Fin n → Fin q) × (Fin n → Fin q) → ℝ :=
    fun x => Real.exp (rsPairExpoR q n d t x.1 x.2) with hf
  have hholder := Real.inner_le_weight_mul_Lp_of_nonneg (rsWindow q n η) hp w f
    (fun x => mul_nonneg hc0 (hP0 x)) (fun x => (Real.exp_pos _).le)
  have hL : c * ∑ x ∈ rsWindow q n η, Real.exp (rsPairExpoR q n d t x.1 x.2) * P x =
      ∑ x ∈ rsWindow q n η, w x * f x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [hw, hf]
    ring
  have hW : ∑ x ∈ rsWindow q n η, w x ≤ rsQProb q n d t E := by
    rw [hQ, Finset.mul_sum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun x _ _ => mul_nonneg hc0 (hP0 x))
  have hloc := hC n hn (t : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs]; exact htT)
    (by simp only [Complex.ofReal_re]; nlinarith [sq_nonneg tstar]) p (by linarith) le_rfl
  have hWf : ∑ x ∈ rsWindow q n η, w x * f x ^ p ≤ C := by
    calc ∑ x ∈ rsWindow q n η, w x * f x ^ p
        ≤ ∑ x ∈ rsWindow q n η, c * Real.exp (p * (rsPairExpo q n d (t : ℂ) x.1 x.2).re) := by
          refine Finset.sum_le_sum fun x _ => ?_
          simp only [hw, hf]
          rw [RSLocalAux.rsPairExpo_ofReal, Complex.ofReal_re, ← Real.exp_mul,
            mul_comm (rsPairExpoR _ _ _ _ _ _) p]
          have h1 := hP1 x
          have h2 : 0 ≤ Real.exp (p * rsPairExpoR q n d t x.1 x.2) := (Real.exp_pos _).le
          have h3 : 0 ≤ c * Real.exp (p * rsPairExpoR q n d t x.1 x.2) := mul_nonneg hc0 h2
          nlinarith
      _ = c * ∑ x ∈ rsWindow q n η, Real.exp (p * (rsPairExpo q n d (t : ℂ) x.1 x.2).re) := by
          rw [Finset.mul_sum]
      _ ≤ C := hloc
  have hWnn : 0 ≤ ∑ x ∈ rsWindow q n η, w x :=
    Finset.sum_nonneg fun x _ => mul_nonneg hc0 (hP0 x)
  have hWfnn : 0 ≤ ∑ x ∈ rsWindow q n η, w x * f x ^ p :=
    Finset.sum_nonneg fun x _ => mul_nonneg (mul_nonneg hc0 (hP0 x))
      (Real.rpow_nonneg (Real.exp_pos _).le _)
  have hQnn : 0 ≤ rsQProb q n d t E := le_trans hWnn hW
  have hp1 : 0 ≤ 1 - p⁻¹ := by
    have : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
    linarith
  calc c * ∑ x ∈ rsWindow q n η, Real.exp (rsPairExpoR q n d t x.1 x.2) * P x
      = ∑ x ∈ rsWindow q n η, w x * f x := hL
    _ ≤ (∑ x ∈ rsWindow q n η, w x) ^ (1 - p⁻¹) *
          (∑ x ∈ rsWindow q n η, w x * f x ^ p) ^ p⁻¹ := hholder
    _ ≤ rsQProb q n d t E ^ (1 - p⁻¹) * C ^ p⁻¹ :=
        mul_le_mul (Real.rpow_le_rpow hWnn hW hp1)
          (Real.rpow_le_rpow hWfnn hWf (inv_nonneg.2 (by linarith)))
          (Real.rpow_nonneg hWfnn _) (Real.rpow_nonneg hQnn _)
    _ = C ^ p⁻¹ * rsQProb q n d t E ^ (1 - p⁻¹) := mul_comm _ _

end

end ERZeroFreeness
