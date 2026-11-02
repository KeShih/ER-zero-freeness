/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountInterp
import ERZeroFreeness.CountSignedPoly
import ERZeroFreeness.CountConnSets
import ERZeroFreeness.CountSgModel
import ERZeroFreeness.VBRelation

/-! # Proposition 8.4(ii) at the coefficient level

The Viana–Bray part of `prop:counting`, for the approximation
`Z̃_k(β) = 2^n cosh(β)^{|E|} exp(∑_{j ≤ k} ℓ_j(G) tanh(β)^j)` (`vbApprox`) built from the exact
coefficients `ℓ_1, …, ℓ_k`: if `𝓘_{G_n,J}` has no zeros in `{|t| ≤ r}` with probability tending
to one, for some `r > tanh β*`, then with probability tending to one over `(G_n, J)`,
`eq:connected-set-bound` holds and `(1-ε) Z^{VB}(β) ≤ Z̃_k(β) ≤ (1+ε) Z^{VB}(β)` for all
`β ∈ [-β*, β*]`, `ε ∈ (0,1)` and `k ≥ C log(n/ε)` (`vb_counting_real`).  The algorithm itself
(running time, numerical evaluation of `exp`, `cosh`, `tanh`) is not formalized.

## Main results

* `Count.vbZ_eq_signedPoly`: `eq:viana-bray`, `Z^{VB}_{G,J}(β) = 2^n cosh(β)^{|E|} 𝓘_{G,J}(tanh β)`.
* `vb_log_expansion`: the deterministic core, via the interpolation estimate.
* `vb_counting_coefficients`, `vb_counting_relative_error`, `vb_counting_event`,
  `vb_counting_real`: the probabilistic statements.
* `vbApprox_vbZ_real`: for real `β`, `Z̃_k(β)` and `Z^{VB}(β)` are positive real numbers.

## Proof

`Count.vbZ_eq_signedPoly` restates `vbZ_eq` (`VBRelation`).  `vb_log_expansion`:
`Count.vbZ_eq_signedPoly` at real `β` (`cosh β > 0`) and `exists_eval_eq_exp_logCoeff` with
`M = r`, `t = tanh β`; `natDegree ≤ |E|`.  The probabilistic statements: the zero-free event is
contained in the target events (`tendsto_sgProb_of_subset`, `tendsto_sgProb_inter`,
`sgProb_graphEvent`, `tendsto_erProb_connSetBound`); `|tanh β| ≤ tanh β*` on `[-β*, β*]`
(`tanh` is odd and increasing: `Real.artanh_tanh`, `Real.artanh_lt_artanh`);
`x ↦ x^{k+1}/(1-x)` is increasing on `[0,1)`.  Relative error: with `θ = tanh β*/r` take
`C = 3/(1-θ)`.  If `m = |E(G)| ≥ 1` then `n ≥ 2` and `m ≤ n²`, so for `ε ∈ (0,1)`
`max{1, log(m/(ε/2))} ≤ 3 log(n/ε) ≤ k(1-θ)` (`log 2 > 1/3`), and the threshold estimate
`CountVB_tail_le` gives `m θ^{k+1}/((k+1)(1-θ)) ≤ ε/2`; if `m = 0` the bound is `0`.
Then `vbApprox = vbZ · exp(-E)` and `‖exp(-E) - 1‖ ≤ 2‖E‖` (`Complex.norm_exp_sub_one_le`).
Realness: `ellCoeff_rational` makes `∑ ℓ_j tanh(β)^j` real (`Complex.ofReal_exp`,
`Complex.ofReal_cosh`, `Complex.ofReal_tanh`); `vbZ` at real `β` is a nonempty sum of
`Real.exp`s (`edgeA 2 σ e = ±1` is real).  Real form: `‖(x:ℂ) - y‖ = |x - y|`
(`Complex.norm_real`) and `|x - y| ≤ ε y ⇔ (1-ε) y ≤ x ≤ (1+ε) y` (`abs_sub_le_iff`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountVB

/-- **`eq:viana-bray`.** `Z^{VB}_{G,J}(β) = 2^n (cosh β)^{|E(G)|} 𝓘_{G,J}(tanh β)` for
signs `J_e ∈ {±1}` and `cosh β ≠ 0`. -/
theorem Count.vbZ_eq_signedPoly {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ)
    (hJ : ∀ e ∈ G.edgeFinset, J e = 1 ∨ J e = -1) {β : ℂ} (hβ : Complex.cosh β ≠ 0) :
    vbZ G J β = 2 ^ Fintype.card V * Complex.cosh β ^ G.edgeFinset.card *
      (signedPoly G 2 J).eval (Complex.tanh β) :=
  ERZeroFreeness.vbZ_eq G J hJ hβ

/-- `tanh` is monotone on `ℝ` (through `artanh ∘ tanh = id`). -/
private lemma CountVB_tanh_le_tanh {x y : ℝ} (h : x ≤ y) : Real.tanh x ≤ Real.tanh y := by
  by_contra hlt
  rw [not_le] at hlt
  have h' := Real.artanh_lt_artanh (Real.neg_one_lt_tanh y) (Real.tanh_lt_one x) hlt
  rw [Real.artanh_tanh, Real.artanh_tanh] at h'
  linarith

/-- `tanh x ≥ 0` for `x ≥ 0`. -/
private lemma CountVB_tanh_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  have h := CountVB_tanh_le_tanh hx
  rwa [Real.tanh_zero] at h

/-- `|tanh β| ≤ tanh β*` for `β ∈ [-β*, β*]` (`tanh` is odd and increasing). -/
private lemma CountVB_abs_tanh_le {β βs : ℝ} (hβ : β ∈ Set.Icc (-βs) βs) :
    |Real.tanh β| ≤ Real.tanh βs := by
  rw [abs_le]
  constructor
  · have h := CountVB_tanh_le_tanh hβ.1
    rw [Real.tanh_neg] at h
    linarith
  · exact CountVB_tanh_le_tanh hβ.2

/-- `x ↦ m x^{k+1}/((k+1)(1-x))` is increasing on `[0,1)` (`m ≥ 0`). -/
private lemma CountVB_tail_mono {m x y : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y < 1) (k : ℕ) :
    m * x ^ (k + 1) / ((k + 1) * (1 - x)) ≤ m * y ^ (k + 1) / ((k + 1) * (1 - y)) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have h1y : 0 < 1 - y := by linarith
  rw [mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hm
  refine div_le_div₀ (pow_nonneg (hx.trans hxy) _) (pow_le_pow_left₀ hx hxy _)
    (mul_pos hk h1y) ?_
  exact mul_le_mul_of_nonneg_left (by linarith) hk.le

/-- Deterministic core of `prop:counting`(ii): if `𝓘_{G,J}` has no zeros in
`{|t| ≤ r}` and `|tanh β| < r`, then for every `k`,
`Z^{VB}_{G,J}(β) = 2^n cosh(β)^{|E|} exp(∑_{j ≤ k} ℓ_j(G) tanh(β)^j + E)` with
`|E| ≤ |E(G)| θ^{k+1}/((k+1)(1-θ))`, `θ = |tanh β|/r`. -/
theorem vb_log_expansion {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ)
    (hJ : ∀ e ∈ G.edgeFinset, J e = 1 ∨ J e = -1) {r : ℝ}
    (hzf : ∀ t : ℂ, ‖t‖ ≤ r → (signedPoly G 2 J).eval t ≠ 0) {β : ℝ}
    (hβ : |Real.tanh β| < r) (k : ℕ) :
    ∃ E : ℂ, vbZ G J β = 2 ^ Fintype.card V * (Real.cosh β : ℂ) ^ G.edgeFinset.card *
        Complex.exp (∑ j ∈ Finset.Icc 1 k, ellCoeff G 2 J j * (Real.tanh β : ℂ) ^ j + E) ∧
      ‖E‖ ≤ G.edgeFinset.card * (|Real.tanh β| / r) ^ (k + 1) /
        ((k + 1) * (1 - |Real.tanh β| / r)) := by
  have hcosh : Complex.cosh (β : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]
    exact_mod_cast (Real.cosh_pos β).ne'
  have hp : (signedPoly G 2 J).eval 0 = 1 := Count.signedPoly_eval_zero (by norm_num) G J
  have hzf' : ∀ z : ℂ, ‖z‖ < r → (signedPoly G 2 J).eval z ≠ 0 := fun z hz => hzf z hz.le
  have ht : ‖(Real.tanh β : ℂ)‖ = |Real.tanh β| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have ht' : ‖(Real.tanh β : ℂ)‖ < r := by rw [ht]; exact hβ
  obtain ⟨E, hE, hEb⟩ := exists_eval_eq_exp_logCoeff hp hzf' ht' k
  refine ⟨E, ?_, ?_⟩
  · rw [Count.vbZ_eq_signedPoly G J hJ hcosh, ← Complex.ofReal_cosh, ← Complex.ofReal_tanh, hE]
    rfl
  · rw [ht] at hEb
    refine hEb.trans ?_
    have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hβ
    have hθ0 : 0 ≤ |Real.tanh β| / r := div_nonneg (abs_nonneg _) hr.le
    have hθ1 : |Real.tanh β| / r < 1 := (div_lt_one hr).mpr hβ
    have hdeg : ((signedPoly G 2 J).natDegree : ℝ) ≤ G.edgeFinset.card := by
      exact_mod_cast Count.signedPoly_natDegree_le G 2 J
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_right hdeg ?_
    refine div_nonneg (pow_nonneg hθ0 _) (mul_nonneg (by positivity) (by linarith))

/-- **Proposition 8.4(ii) `prop:counting`, coefficient level.** Let `q = 2`, `J` uniform
signs, `β* > 0`, and suppose that for some `r > tanh β*`, with probability tending to one,
`𝓘_{G_n,J}` has no zeros in `{|t| ≤ r}`.  Then with probability tending to one over `(G_n, J)`,
for all `β ∈ [-β*, β*]` and all `k`,
`Z^{VB}(β) = 2^n cosh(β)^{|E|} exp(∑_{j ≤ k} ℓ_j tanh(β)^j + E)`,
`|E| ≤ |E(G_n)| θ^{k+1}/((k+1)(1-θ))`, `θ = tanh β*/r`. -/
theorem vb_counting_coefficients {d : ℝ} (hd : 0 < d) {βs r : ℝ} (hβs : 0 < βs)
    (hr : Real.tanh βs < r)
    (hzf : Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ t : ℂ, ‖t‖ ≤ r → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0})
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ β ∈ Set.Icc (-βs) βs, ∀ k : ℕ, ∃ E : ℂ,
        vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β =
          2 ^ n * (Real.cosh β : ℂ) ^ GJ.1.edgeFinset.card *
            Complex.exp (∑ j ∈ Finset.Icc 1 k,
              ellCoeff GJ.1 2 (fun e => boolSign (GJ.2 e)) j * (Real.tanh β : ℂ) ^ j + E) ∧
        ‖E‖ ≤ GJ.1.edgeFinset.card * (Real.tanh βs / r) ^ (k + 1) /
          ((k + 1) * (1 - Real.tanh βs / r))})
      atTop (𝓝 1) := by
  have hr0 : 0 < r := lt_of_le_of_lt (CountVB_tanh_nonneg hβs.le) hr
  refine Count.tendsto_sgProb_of_subset hd (fun n => ?_) hzf
  intro GJ hGJ
  simp only [Set.mem_ofPred_eq] at hGJ ⊢
  intro β hβ k
  have hJ : ∀ e ∈ GJ.1.edgeFinset, boolSign (GJ.2 e) = 1 ∨ boolSign (GJ.2 e) = -1 := by
    intro e _
    unfold boolSign
    split_ifs <;> simp
  have habs : |Real.tanh β| ≤ Real.tanh βs := CountVB_abs_tanh_le hβ
  obtain ⟨E, hE, hEb⟩ :=
    vb_log_expansion GJ.1 (fun e => boolSign (GJ.2 e)) hJ hGJ (habs.trans_lt hr) k
  refine ⟨E, ?_, ?_⟩
  · rw [hE, Fintype.card_fin]
  · refine hEb.trans ?_
    exact CountVB_tail_mono (Nat.cast_nonneg _) (div_nonneg (abs_nonneg _) hr0.le)
      (div_le_div_of_nonneg_right habs hr0.le) ((div_lt_one hr0).mpr hr) k

/-- The step from bound (8) (`exists_eval_eq_exp_logCoeff`) to the threshold: if
`k ≥ max{1, log(N/ε)}/(1-θ)` then `N θ^{k+1} / ((k+1)(1-θ)) ≤ ε` (by `θ ≤ e^{θ-1}` and
`k(1-θ) ≥ 1`). -/
private lemma CountVB_tail_le {N θ ε : ℝ} (hN : 0 ≤ N) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hε : 0 < ε) {k : ℕ} (hk : max 1 (Real.log (N / ε)) / (1 - θ) ≤ k) :
    N * θ ^ (k + 1) / ((k + 1) * (1 - θ)) ≤ ε := by
  have h1θ : 0 < 1 - θ := by linarith
  rw [div_le_iff₀ h1θ] at hk
  have hk1 : 1 ≤ (k : ℝ) * (1 - θ) := le_trans (le_max_left _ _) hk
  have hkl : Real.log (N / ε) ≤ (k : ℝ) * (1 - θ) := le_trans (le_max_right _ _) hk
  have hden : 1 ≤ ((k : ℝ) + 1) * (1 - θ) := by nlinarith
  have hθk : θ ^ (k + 1) ≤ Real.exp (-((k : ℝ) * (1 - θ))) := by
    have h1 : θ ≤ Real.exp (θ - 1) := by linarith [Real.add_one_le_exp (θ - 1)]
    have h2 : θ ^ k ≤ Real.exp (θ - 1) ^ k := pow_le_pow_left₀ hθ0 h1 k
    rw [← Real.exp_nat_mul] at h2
    have h3 : θ ^ (k + 1) ≤ θ ^ k := pow_le_pow_of_le_one hθ0 hθ1.le (Nat.le_succ k)
    calc θ ^ (k + 1) ≤ θ ^ k := h3
      _ ≤ Real.exp (k * (θ - 1)) := h2
      _ = Real.exp (-((k : ℝ) * (1 - θ))) := by congr 1; ring
  have hnum : N * θ ^ (k + 1) ≤ ε := by
    rcases hN.eq_or_lt with h | h
    · rw [← h, zero_mul]; exact hε.le
    · have hexp : Real.exp (-((k : ℝ) * (1 - θ))) ≤ ε / N := by
        calc Real.exp (-((k : ℝ) * (1 - θ))) ≤ Real.exp (-Real.log (N / ε)) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = ε / N := by rw [Real.exp_neg, Real.exp_log (div_pos h hε), inv_div]
      calc N * θ ^ (k + 1) ≤ N * (ε / N) := mul_le_mul_of_nonneg_left (hθk.trans hexp) hN
        _ = ε := by field_simp
  calc N * θ ^ (k + 1) / ((k + 1) * (1 - θ)) ≤ N * θ ^ (k + 1) :=
        div_le_self (mul_nonneg hN (pow_nonneg hθ0 _)) hden
    _ ≤ ε := hnum

/-- A graph on `Fin n` with at least one edge has `n ≥ 2`, and `|E(G)| ≤ n²`. -/
private lemma CountVB_card_edge {n : ℕ} (G : SimpleGraph (Fin n))
    (h : 1 ≤ G.edgeFinset.card) : 2 ≤ n ∧ (G.edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
  have h1 := G.card_edgeFinset_le_card_choose_two
  rw [Fintype.card_fin] at h1
  constructor
  · by_contra hn
    rw [not_le] at hn
    rw [Nat.choose_eq_zero_of_lt hn] at h1
    omega
  · have h2 := Nat.choose_le_pow n 2
    exact_mod_cast h1.trans h2

/-- The logarithmic arithmetic of `vb_counting_relative_error`: for `n ≥ 2`, `1 ≤ m ≤ n²` and
`ε ∈ (0,1)`, `max{1, log(m/(ε/2))} ≤ 3 log(n/ε)` (uses `log 2 > 1/3`). -/
private lemma CountVB_log_bound {n : ℕ} {m ε : ℝ} (hn : (2 : ℝ) ≤ n) (hm1 : 1 ≤ m)
    (hmn : m ≤ (n : ℝ) ^ 2) (hε0 : 0 < ε) (hε1 : ε < 1) :
    max 1 (Real.log (m / (ε / 2))) ≤ 3 * Real.log (n / ε) := by
  have hn0 : (0 : ℝ) < n := by linarith
  have hm0 : 0 < m := by linarith
  have hlogm : Real.log m ≤ 2 * Real.log n := by
    have h := Real.log_le_log hm0 hmn
    rw [Real.log_pow] at h
    push_cast at h
    linarith
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hlogε : Real.log ε < 0 := Real.log_neg hε0 hε1
  have hlog2 := Real.log_two_gt_d9
  have h1 : Real.log (m / (ε / 2)) = Real.log m - (Real.log ε - Real.log 2) := by
    rw [Real.log_div hm0.ne' (by positivity), Real.log_div hε0.ne' (by norm_num)]
  have h2 : Real.log (n / ε) = Real.log n - Real.log ε := Real.log_div hn0.ne' hε0.ne'
  rw [h1, h2]
  refine max_le ?_ ?_
  · linarith
  · linarith

/-- **Proposition 8.4(ii), relative error `ε` from `k = O(log(n/ε))` coefficients.**
Under the hypothesis of `prop:counting`(ii) there is `C = C(β*, r)` such that, with probability
tending to one over `(G_n, J)`, for all `β ∈ [-β*, β*]`, `ε ∈ (0,1)` and `k ≥ C log(n/ε)`,
`|Z̃_k(β) - Z^{VB}(β)| ≤ ε |Z^{VB}(β)|`. -/
theorem vb_counting_relative_error {d : ℝ} (hd : 0 < d) {βs r : ℝ} (hβs : 0 < βs)
    (hr : Real.tanh βs < r)
    (hzf : Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ t : ℂ, ‖t‖ ≤ r → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0})
      atTop (𝓝 1)) :
    ∃ C : ℝ, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ β ∈ Set.Icc (-βs) βs, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
        C * Real.log (n / ε) ≤ k →
          ‖vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β -
              vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β‖ ≤
            ε * ‖vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β‖})
      atTop (𝓝 1) := by
  have hts0 : 0 ≤ Real.tanh βs := CountVB_tanh_nonneg hβs.le
  have hr0 : 0 < r := lt_of_le_of_lt hts0 hr
  have hθ0 : 0 ≤ Real.tanh βs / r := div_nonneg hts0 hr0.le
  have hθ1 : Real.tanh βs / r < 1 := (div_lt_one hr0).mpr hr
  have h1θ : 0 < 1 - Real.tanh βs / r := by linarith
  refine ⟨3 / (1 - Real.tanh βs / r), ?_⟩
  refine Count.tendsto_sgProb_of_subset hd (fun n => ?_) (vb_counting_coefficients hd hβs hr hzf)
  intro GJ hGJ
  simp only [Set.mem_ofPred_eq] at hGJ ⊢
  intro β hβ ε hε0 hε1 k hk
  obtain ⟨E, hE, hEb⟩ := hGJ β hβ k
  have hE2 : ‖E‖ ≤ ε / 2 := by
    refine hEb.trans ?_
    rcases Nat.eq_zero_or_pos GJ.1.edgeFinset.card with hm | hm
    · rw [hm, Nat.cast_zero, zero_mul, zero_div]
      linarith
    · obtain ⟨hn2, hmn⟩ := CountVB_card_edge GJ.1 hm
      refine CountVB_tail_le (Nat.cast_nonneg _) hθ0 hθ1 (half_pos hε0) ?_
      rw [div_le_iff₀ h1θ]
      have hk' : 3 * Real.log (n / ε) ≤ k * (1 - Real.tanh βs / r) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1θ] at hk
        linarith
      exact (CountVB_log_bound (by exact_mod_cast hn2) (Nat.one_le_cast.mpr hm) hmn hε0
        hε1).trans hk'
  have hEle1 : ‖-E‖ ≤ 1 := by rw [norm_neg]; linarith
  have happrox : vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β =
      vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β * Complex.exp (-E) := by
    rw [hE, vbApprox, Fintype.card_fin, mul_assoc _ (Complex.exp _), ← Complex.exp_add,
      add_neg_cancel_right]
  rw [happrox, ← mul_sub_one, norm_mul, mul_comm ε]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖Complex.exp (-E) - 1‖ ≤ 2 * ‖-E‖ := Complex.norm_exp_sub_one_le hEle1
    _ ≤ ε := by rw [norm_neg]; linarith

/-- **The event `𝒢_n` of the proof of `prop:counting`(ii), coefficient level.** For
`B > 2e(d+1)`, with probability tending to one both `eq:connected-set-bound` holds (so
`lem:local-decomposition` computes `ℓ_1, …, ℓ_k` from `≤ 2k n² B^{2k}` connected sets of size
`≤ 2k`, `card_local_sets_le`) and the `ε`-approximation of `vb_counting_relative_error`
holds. -/
theorem vb_counting_event {d : ℝ} (hd : 0 < d) {βs r : ℝ} (hβs : 0 < βs)
    (hr : Real.tanh βs < r)
    (hzf : Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ t : ℂ, ‖t‖ ≤ r → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0})
      atTop (𝓝 1))
    {B : ℝ} (hB : 2 * Real.exp 1 * (d + 1) < B) :
    ∃ C : ℝ, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ConnSetBound B GJ.1 ∧
        ∀ β ∈ Set.Icc (-βs) βs, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
          C * Real.log (n / ε) ≤ k →
            ‖vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β -
                vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β‖ ≤
              ε * ‖vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β‖})
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := vb_counting_relative_error hd hβs hr hzf
  refine ⟨C, ?_⟩
  have hA : Tendsto (fun n : ℕ => sgProb n (d / n) {GJ | ConnSetBound B GJ.1}) atTop (𝓝 1) := by
    refine Tendsto.congr (fun n => ?_) (tendsto_erProb_connSetBound hd hB)
    exact (Count.sgProb_graphEvent n (d / n) {G | ConnSetBound B G}).symm
  exact Count.tendsto_sgProb_inter hd hA hC

/-- For real `β`, the coefficient-level approximation `Z̃_k(β)` (`vbApprox`) and `Z^{VB}(β)` are
positive real numbers (the `ℓ_j` are rational, `ellCoeff_rational`), for any integer signs. -/
theorem vbApprox_vbZ_real {V : Type*} [Fintype V] (G : SimpleGraph V) (J : Sym2 V → ℤ) (k : ℕ)
    (β : ℝ) :
    (∃ x : ℝ, 0 < x ∧ vbApprox G J k β = x) ∧ (∃ y : ℝ, 0 < y ∧ vbZ G J β = y) := by
  constructor
  · choose c hc using fun j => ellCoeff_rational G 2 J j
    refine ⟨2 ^ Fintype.card V * Real.cosh β ^ G.edgeFinset.card *
      Real.exp (∑ j ∈ Finset.Icc 1 k, (c j : ℝ) * Real.tanh β ^ j),
      mul_pos (mul_pos (by positivity) (pow_pos (Real.cosh_pos β) _)) (Real.exp_pos _), ?_⟩
    have hsum : ∑ j ∈ Finset.Icc 1 k, ellCoeff G 2 J j * (Real.tanh β : ℂ) ^ j =
        ((∑ j ∈ Finset.Icc 1 k, (c j : ℝ) * Real.tanh β ^ j : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc j]
      push_cast
      rfl
    rw [vbApprox, hsum, ← Complex.ofReal_exp]
    push_cast
    ring
  · have ha : ∀ (σ : V → Fin 2) (e : Sym2 V),
        edgeA 2 σ e = ((if (e.map σ).IsDiag then (1 : ℝ) else -1 : ℝ) : ℂ) := by
      intro σ e
      unfold edgeA
      split_ifs <;> norm_num
    refine ⟨∑ σ : V → Fin 2, Real.exp (β * ∑ e ∈ G.edgeFinset,
      (J e : ℝ) * (if (e.map σ).IsDiag then (1 : ℝ) else -1)),
      Finset.sum_pos (fun σ _ => Real.exp_pos _) Finset.univ_nonempty, ?_⟩
    rw [vbZ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    refine congrArg _ (Finset.sum_congr rfl fun e _ => ?_)
    rw [ha σ e]

/-- **Proposition 8.4(ii) `prop:counting`, coefficient level, in the paper's form.**
Under the hypothesis of `prop:counting`(ii), for every `B > 2e(d+1)` there is `C = C(d, β*, r)`
such that, with probability tending to one over `(G_n, J)`, `eq:connected-set-bound` holds (so
the oracle of `lem:coefficient-oracle` does not fail) and, simultaneously for all
`β ∈ [-β*, β*]`, `ε ∈ (0,1)` and `k ≥ C log(n/ε)`, the numbers `Z̃_k(β)` and `Z^{VB}(β)` are
real and `(1-ε) Z^{VB}(β) ≤ Z̃_k(β) ≤ (1+ε) Z^{VB}(β)`. -/
theorem vb_counting_real {d : ℝ} (hd : 0 < d) {βs r : ℝ} (hβs : 0 < βs)
    (hr : Real.tanh βs < r)
    (hzf : Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ∀ t : ℂ, ‖t‖ ≤ r → (signedPoly GJ.1 2 (fun e => boolSign (GJ.2 e))).eval t ≠ 0})
      atTop (𝓝 1))
    {B : ℝ} (hB : 2 * Real.exp 1 * (d + 1) < B) :
    ∃ C : ℝ, Tendsto (fun n : ℕ => sgProb n (d / n)
      {GJ | ConnSetBound B GJ.1 ∧
        ∀ β ∈ Set.Icc (-βs) βs, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ,
          C * Real.log (n / ε) ≤ k →
            ∃ x y : ℝ, vbApprox GJ.1 (fun e => boolSign (GJ.2 e)) k β = x ∧
              vbZ GJ.1 (fun e => boolSign (GJ.2 e)) β = y ∧
              (1 - ε) * y ≤ x ∧ x ≤ (1 + ε) * y})
      atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := vb_counting_event hd hβs hr hzf hB
  refine ⟨C, Count.tendsto_sgProb_of_subset hd (fun n => ?_) hC⟩
  intro GJ hGJ
  simp only [Set.mem_ofPred_eq] at hGJ ⊢
  refine ⟨hGJ.1, fun β hβ ε hε0 hε1 k hk => ?_⟩
  obtain ⟨⟨x, -, hx⟩, ⟨y, hy0, hy⟩⟩ :=
    vbApprox_vbZ_real GJ.1 (fun e => boolSign (GJ.2 e)) k β
  have h := hGJ.2 β hβ ε hε0 hε1 k hk
  rw [hx, hy, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hy0] at h
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp h
  exact ⟨x, y, hx, hy, by linarith, by linarith⟩

end CountVB

end

end ERZeroFreeness
