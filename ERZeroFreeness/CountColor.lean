/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Main
import ERZeroFreeness.NonColor

/-! # `CountColor`: Corollary 1.3 (zero-freeness level) and the arithmetic of Corollary 1.4
(blueprint §11)

Plan.  `two_mul_log_lt_d2`: `d₂(q) = 2(q-1) log(q-1) · (q-1)²/(q(q-2))` and
`(q-1)² > q(q-2) > 0`, `log(q-1) > 0`.  `dnc_lt_d2_succ`: `log q > 0`,
`d₂(q+1) = 2q log q · q²/(q²-1)`.  `eventually_lt_two_mul_log`: with `x = a d/log d`,
`2(x-1) log(x-1)/d → 2a > 1` (`Real.isLittleO_log_id_atTop` composed with `Real.log`,
`Real.tendsto_log_atTop`).  `cor_range_d2`: `x ↦ (x-1) log(x-1)` is increasing on `[2,∞)`, so
`d₂(q) > 2(q-1)log(q-1) ≥ 2(x-1)log(x-1) > d` for `q ≥ x ≥ 3`; `0 < d` since `D ≥ 1`.
`cor_range`: `potts_zero_free`.
Corollary 1.4: if `3 ≤ q < q'` both had `d₂ ≤ d < (2·-1) log ·`, then
`d₂(q') > 2(q'-1) log(q'-1) ≥ 2q log q > (2q-1) log q > d ≥ d₂(q')`; `q_d := 1` if no `q` is
exceptional.
The paper's claims on `d₂`, `d_nc`: with `u = x - 1 ≥ 2 < v = y - 1`,
`v³(u²-1) - u³(v²-1) = (v-u)(u²v² - u² - uv - v²) > 0`, and `log` is increasing; asymptotics:
`d₂(q)/(2q log q) = ((q-1)³/(q²(q-2))) · (log(q-1)/log q)` for `q ≥ 3`, both factors `→ 1`.
Proved in `docs/counting/scratch-proofs.lean` (paste): `two_mul_log_lt_d2`, `dnc_lt_d2_succ`,
`d2_dnc_subsingleton`, `cor_all_but_one_arith`, `d2_formula_strictMonoOn`, `d2_strictMonoOn`,
`dnc_strictMonoOn`, `tendsto_d2_div_two_mul_log`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountColor

/-- [CO.1] `d₂(q) > 2(q-1) log(q-1)` for `q ≥ 3` (replaces "`d₂` is increasing" and
"`d₂(q) ∼ 2q log q`" in the proof of `cor:range`). -/
theorem two_mul_log_lt_d2 {q : ℕ} (hq : 3 ≤ q) :
    2 * ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) < d2 q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 < Real.log ((q : ℝ) - 1) := Real.log_pos (by linarith)
  have hden : 0 < (q : ℝ) * ((q : ℝ) - 2) := by nlinarith
  unfold d2
  rw [lt_div_iff₀ hden]
  have h1 : 0 < 2 * ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) := by
    have : 0 < (q : ℝ) - 1 := by linarith
    positivity
  have key : 2 * ((q : ℝ) - 1) ^ 3 * Real.log ((q : ℝ) - 1) =
      2 * ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) * ((q : ℝ) * ((q : ℝ) - 2)) +
        2 * ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) := by ring
  linarith

/-- [CO.2] The display of the proof of `cor:all-but-one`:
`d_nc(q) = (2q-1) log q < 2q log q < 2q³ log q/(q²-1) = d₂(q+1)`. -/
theorem dnc_lt_d2_succ {q : ℕ} (hq : 2 ≤ q) :
    (2 * (q : ℝ) - 1) * Real.log q < 2 * q * Real.log q ∧
      2 * (q : ℝ) * Real.log q < d2 (q + 1) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hl : 0 < Real.log q := Real.log_pos (by linarith)
  have hql : 0 < (q : ℝ) * Real.log q := mul_pos (by linarith) hl
  refine ⟨by nlinarith, ?_⟩
  unfold d2
  push_cast
  have e1 : ((q : ℝ) + 1 - 1) = q := by ring
  have e2 : ((q : ℝ) + 1 - 2) = q - 1 := by ring
  rw [e1, e2]
  have hden : 0 < ((q : ℝ) + 1) * ((q : ℝ) - 1) := by nlinarith
  rw [lt_div_iff₀ hden]
  have key : 2 * (q : ℝ) * Real.log q * (((q : ℝ) + 1) * ((q : ℝ) - 1)) =
      2 * (q : ℝ) ^ 3 * Real.log q - 2 * ((q : ℝ) * Real.log q) := by ring
  linarith

/-- `d / log d → ∞` (helper for [CO.3]). -/
private lemma CountColor_tendsto_div_log :
    Tendsto (fun d : ℝ => d / Real.log d) atTop atTop := by
  have h0 : Tendsto (fun d : ℝ => Real.log d / d) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hpos : ∀ᶠ d : ℝ in atTop, Real.log d / d ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with d hd
    exact div_pos (Real.log_pos hd) (by linarith)
  have h1 : Tendsto (fun d : ℝ => Real.log d / d) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨h0, hpos⟩
  have h2 := tendsto_inv_nhdsGT_zero.comp h1
  have e : (fun d : ℝ => d / Real.log d) =
      (fun x : ℝ => x⁻¹) ∘ (fun d : ℝ => Real.log d / d) := by
    funext d
    simp [inv_div]
  rw [e]
  exact h2

/-- The identity `2(x-1)M = d · (2a(1 - 1/x) · M/L)` for `x = a d/L` (helper for [CO.3]). -/
private lemma CountColor_two_mul_eq {a d L M : ℝ} (ha : a ≠ 0) (hd : d ≠ 0) (hL : L ≠ 0) :
    2 * (a * d / L - 1) * M = d * (2 * a * (1 - 1 / (a * d / L)) * (M / L)) := by
  field_simp

/-- [CO.3] The asymptotic input of `cor:range`: for `a > 1/2` and all large `d`, `x = a d/log d`
satisfies `x ≥ 3` and `2(x-1) log(x-1) > d`. -/
theorem eventually_lt_two_mul_log {a : ℝ} (ha : 1 / 2 < a) :
    ∀ᶠ d : ℝ in atTop, 3 ≤ a * d / Real.log d ∧
      d < 2 * (a * d / Real.log d - 1) * Real.log (a * d / Real.log d - 1) := by
  have ha0 : 0 < a := by linarith
  have hlog : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  -- `x(d) = a d / log d → ∞`
  have hx : Tendsto (fun d : ℝ => a * d / Real.log d) atTop atTop := by
    have h := CountColor_tendsto_div_log.const_mul_atTop ha0
    have e : (fun d : ℝ => a * d / Real.log d) = fun d : ℝ => a * (d / Real.log d) := by
      funext d
      rw [mul_div_assoc]
    rw [e]
    exact h
  -- `1 - 1/x → 1` and `log (1 - 1/x) → 0`
  have hy : Tendsto (fun d : ℝ => 1 - 1 / (a * d / Real.log d)) atTop (𝓝 1) := by
    have h0 := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hx)
    rw [sub_zero] at h0
    exact h0
  have hl1 : Tendsto (fun d : ℝ => Real.log (1 - 1 / (a * d / Real.log d))) atTop (𝓝 0) := by
    have h3 := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp hy
    rw [Real.log_one] at h3
    exact h3
  -- `log log d / log d → 0`
  have hll : Tendsto (fun d : ℝ => Real.log (Real.log d) / Real.log d) atTop (𝓝 0) :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hlog).tendsto_div_nhds_zero
  -- `log (x - 1)/log d = log a/log d + 1 - log log d/log d + log (1 - 1/x)/log d → 1`
  have hL : Tendsto (fun d : ℝ => Real.log a / Real.log d + 1 -
      Real.log (Real.log d) / Real.log d +
      Real.log (1 - 1 / (a * d / Real.log d)) / Real.log d) atTop (𝓝 1) := by
    have h := ((((tendsto_const_nhds (x := Real.log a)).div_atTop hlog).add
      (tendsto_const_nhds (x := (1 : ℝ)))).sub hll).add (hl1.div_atTop hlog)
    have e : (0 : ℝ) + 1 - 0 + 0 = 1 := by norm_num
    rw [e] at h
    exact h
  -- the ratio `2(x-1) log(x-1)/d → 2a > 1`
  have hR : Tendsto (fun d : ℝ => 2 * a * (1 - 1 / (a * d / Real.log d)) *
      (Real.log a / Real.log d + 1 - Real.log (Real.log d) / Real.log d +
        Real.log (1 - 1 / (a * d / Real.log d)) / Real.log d)) atTop (𝓝 (2 * a)) := by
    have h := ((tendsto_const_nhds (x := 2 * a)).mul hy).mul hL
    rwa [mul_one, mul_one] at h
  have hev := hR.eventually (lt_mem_nhds (by linarith : (1 : ℝ) < 2 * a))
  filter_upwards [hx.eventually_ge_atTop 3, hev, eventually_gt_atTop 1] with d hx3 hR1 hd1
  refine ⟨hx3, ?_⟩
  have hd0 : 0 < d := by linarith
  have hL0 : 0 < Real.log d := Real.log_pos hd1
  have hx0 : 0 < a * d / Real.log d := by linarith
  have hy0 : 1 - 1 / (a * d / Real.log d) ≠ 0 := by
    have : 1 / (a * d / Real.log d) < 1 := by
      rw [div_lt_one hx0]
      linarith
    exact (sub_pos.mpr this).ne'
  have hsplit : Real.log (a * d / Real.log d - 1) = Real.log a + Real.log d -
      Real.log (Real.log d) + Real.log (1 - 1 / (a * d / Real.log d)) := by
    have e1 : a * d / Real.log d - 1 = a * d / Real.log d * (1 - 1 / (a * d / Real.log d)) := by
      field_simp
    rw [e1, Real.log_mul hx0.ne' hy0, Real.log_div (by positivity) hL0.ne',
      Real.log_mul ha0.ne' hd0.ne']
  have e2 : Real.log (a * d / Real.log d - 1) / Real.log d = Real.log a / Real.log d + 1 -
      Real.log (Real.log d) / Real.log d +
      Real.log (1 - 1 / (a * d / Real.log d)) / Real.log d := by
    rw [hsplit]
    field_simp
  rw [CountColor_two_mul_eq ha0.ne' hd0.ne' hL0.ne', e2]
  exact lt_mul_of_one_lt_right hd0 hR1

/-- [CO.4] **Corollary 1.3 `cor:range` (hypotheses of Theorem 1.1).** For every `η > 0` and all
sufficiently large `d`, every integer `q ≥ (1/2 + η) d / log d` satisfies the hypotheses of
Theorem 1.1: `0 < d`, `q ≥ 3` and `d < d₂(q)`. -/
theorem cor_range_d2 {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, ∀ d : ℝ, D ≤ d → ∀ q : ℕ, (1 / 2 + η) * d / Real.log d ≤ q →
      0 < d ∧ 3 ≤ q ∧ d < d2 q := by
  obtain ⟨D₀, hD₀⟩ := Filter.eventually_atTop.mp
    (eventually_lt_two_mul_log (by linarith : (1 : ℝ) / 2 < 1 / 2 + η))
  refine ⟨max D₀ 1, fun d hd q hq => ?_⟩
  have hd1 : 1 ≤ d := le_trans (le_max_right _ _) hd
  obtain ⟨hx3, hlt⟩ := hD₀ d (le_trans (le_max_left _ _) hd)
  set x := (1 / 2 + η) * d / Real.log d with hxdef
  have hq3 : (3 : ℝ) ≤ q := le_trans hx3 hq
  refine ⟨by linarith, by exact_mod_cast hq3, ?_⟩
  have hq3' : 3 ≤ q := by exact_mod_cast hq3
  have hlx : 0 < Real.log (x - 1) := Real.log_pos (by linarith)
  have hlog : Real.log (x - 1) ≤ Real.log ((q : ℝ) - 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hmul : (x - 1) * Real.log (x - 1) ≤ ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) :=
    mul_le_mul (by linarith) hlog hlx.le (by linarith)
  have h1 := two_mul_log_lt_d2 hq3'
  nlinarith

/-- [CO.5] **Corollary 1.3 `cor:range`, zero-freeness level.** For every `η > 0` and all
sufficiently large `d`, Theorem 1.1 applies to every integer `q ≥ (1/2 + η) d / log d`. -/
theorem cor_range {η : ℝ} (hη : 0 < η) :
    ∃ D : ℝ, ∀ d : ℝ, D ≤ d → ∀ q : ℕ, (1 / 2 + η) * d / Real.log d ≤ q →
      ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1) := by
  obtain ⟨D, hD⟩ := cor_range_d2 hη
  refine ⟨D, fun d hd q hq => ?_⟩
  obtain ⟨hd0, hq3, hd2⟩ := hD d hd q hq
  exact potts_zero_free hq3 hd0 hd2

/-- [CO.6] **Arithmetic core of Corollary 1.4 `cor:all-but-one`.** The intervals
`[d₂(q), (2q-1) log q)`, `q ≥ 3`, are pairwise disjoint: for every `d` at most one integer
`q ≥ 3` has `d₂(q) ≤ d < (2q-1) log q`. -/
theorem d2_dnc_subsingleton (d : ℝ) :
    {q : ℕ | 3 ≤ q ∧ d2 q ≤ d ∧ d < (2 * (q : ℝ) - 1) * Real.log q}.Subsingleton := by
  have key : ∀ q q' : ℕ, 3 ≤ q → q < q' → (2 * (q : ℝ) - 1) * Real.log q < d2 q' := by
    intro q q' hq hqq'
    have h1 := two_mul_log_lt_d2 (by omega : 3 ≤ q')
    have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
    have hqq : (q : ℝ) ≤ (q' : ℝ) - 1 := by
      have : (q : ℝ) + 1 ≤ q' := by exact_mod_cast hqq'
      linarith
    have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
    have hlog : Real.log q ≤ Real.log ((q' : ℝ) - 1) := Real.log_le_log (by linarith) hqq
    have h2 : (q : ℝ) * Real.log q ≤ ((q' : ℝ) - 1) * Real.log ((q' : ℝ) - 1) :=
      mul_le_mul hqq hlog hlogq.le (by linarith)
    nlinarith
  rintro q ⟨hq, hq2, hqd⟩ q' ⟨hq', hq2', hqd'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := key q q' hq h; linarith
  · have := key q' q hq' h; linarith

/-- [CO.7] Corollary 1.4, arithmetic form: there is an integer `q_d ≥ 1` such that every
integer `q ≥ 3`, `q ≠ q_d`, has `d < d₂(q)` or `d ≥ d_nc(q) = (2q-1) log q`. -/
theorem cor_all_but_one_arith (d : ℝ) :
    ∃ qd : ℕ, 1 ≤ qd ∧
      ∀ q : ℕ, 3 ≤ q → q ≠ qd → d < d2 q ∨ (2 * (q : ℝ) - 1) * Real.log q ≤ d := by
  by_cases h : ∃ q₀ : ℕ, 3 ≤ q₀ ∧ d2 q₀ ≤ d ∧ d < (2 * (q₀ : ℝ) - 1) * Real.log q₀
  · obtain ⟨q₀, hq₀⟩ := h
    refine ⟨q₀, by have := hq₀.1; omega, fun q hq hne => ?_⟩
    by_contra hcon
    push Not at hcon
    exact hne (d2_dnc_subsingleton d ⟨hq, hcon.1, hcon.2⟩ hq₀)
  · push Not at h
    refine ⟨1, le_rfl, fun q hq _ => ?_⟩
    by_contra hcon
    push Not at hcon
    exact absurd (h q hq hcon.1) (not_le.mpr hcon.2)

/-- [CO.8] Corollary 1.4, zero-freeness form: for `d > 0` there is an integer `q_d ≥ 1` such
that every integer `q ≥ 3`, `q ≠ q_d`, either satisfies the conclusion of Theorem 1.1 or has
`d ≥ (2q-1) log q` (where [Achlioptas–Naor] makes `G_n` non-`q`-colourable with high
probability; not part of this plan, see `docs/noncolor/NonColorPlan.lean`). -/
theorem cor_all_but_one_zero_free {d : ℝ} (hd : 0 < d) :
    ∃ qd : ℕ, 1 ≤ qd ∧ ∀ q : ℕ, 3 ≤ q → q ≠ qd →
      (∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1)) ∨
      (2 * (q : ℝ) - 1) * Real.log q ≤ d := by
  obtain ⟨qd, hqd1, h⟩ := cor_all_but_one_arith d
  refine ⟨qd, hqd1, fun q hq hne => ?_⟩
  rcases h q hq hne with h1 | h2
  · exact Or.inl (potts_zero_free hq hd h1)
  · exact Or.inr h2

/-- [CO.9] "Direct differentiation shows that `d₂` is strictly increasing on `[3, ∞)`" (proof of
`cor:range`), for `d₂` as a function of a real variable,
`x ↦ 2(x-1)³ log(x-1)/(x(x-2))` (`d2 q` is this function at `x = q`, by definition). -/
theorem d2_formula_strictMonoOn :
    StrictMonoOn (fun x : ℝ => 2 * (x - 1) ^ 3 * Real.log (x - 1) / (x * (x - 2)))
      (Set.Ici 3) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hlu : 0 < Real.log (x - 1) := Real.log_pos (by linarith)
  have hluv : Real.log (x - 1) < Real.log (y - 1) := Real.log_lt_log (by linarith) (by linarith)
  have hdx : 0 < x * (x - 2) := by nlinarith
  have hdy : 0 < y * (y - 2) := by nlinarith
  show 2 * (x - 1) ^ 3 * Real.log (x - 1) / (x * (x - 2)) <
    2 * (y - 1) ^ 3 * Real.log (y - 1) / (y * (y - 2))
  rw [div_lt_div_iff₀ hdx hdy]
  -- with `u = x - 1 ≥ 2 < v = y - 1`: `u³(v²-1) < v³(u²-1)`
  have key : (x - 1) ^ 3 * (y * (y - 2)) < (y - 1) ^ 3 * (x * (x - 2)) := by
    have hid : (y - 1) ^ 3 * (x * (x - 2)) - (x - 1) ^ 3 * (y * (y - 2)) =
        (y - x) * ((x - 1) ^ 2 * (y - 1) ^ 2 - (x - 1) ^ 2 - (x - 1) * (y - 1) -
          (y - 1) ^ 2) := by
      ring
    have hu : (2 : ℝ) ≤ x - 1 := by linarith
    have hvu : x - 1 < y - 1 := by linarith
    have hfac : 0 < (x - 1) ^ 2 * (y - 1) ^ 2 - (x - 1) ^ 2 - (x - 1) * (y - 1) -
        (y - 1) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (y - 1)) (by nlinarith : (0 : ℝ) ≤ (x - 1) ^ 2 - 4),
        mul_pos (by linarith : (0 : ℝ) < (y - 1) - (x - 1))
          (by linarith : (0 : ℝ) < 3 * (y - 1) + 2 * (x - 1))]
    have : 0 < (y - x) * ((x - 1) ^ 2 * (y - 1) ^ 2 - (x - 1) ^ 2 - (x - 1) * (y - 1) -
        (y - 1) ^ 2) :=
      mul_pos (by linarith) hfac
    linarith
  have hpos : 0 < (y - 1) ^ 3 * (x * (x - 2)) := mul_pos (pow_pos (by linarith) 3) hdx
  calc 2 * (x - 1) ^ 3 * Real.log (x - 1) * (y * (y - 2))
      = 2 * Real.log (x - 1) * ((x - 1) ^ 3 * (y * (y - 2))) := by ring
    _ < 2 * Real.log (x - 1) * ((y - 1) ^ 3 * (x * (x - 2))) :=
        mul_lt_mul_of_pos_left key (by linarith)
    _ ≤ 2 * Real.log (y - 1) * ((y - 1) ^ 3 * (x * (x - 2))) :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = 2 * (y - 1) ^ 3 * Real.log (y - 1) * (x * (x - 2)) := by ring

/-- [CO.10] `d₂` is strictly increasing on the integers `q ≥ 3`. -/
theorem d2_strictMonoOn : StrictMonoOn d2 (Set.Ici 3) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  exact d2_formula_strictMonoOn (Set.mem_Ici.mpr (by exact_mod_cast ha))
    (Set.mem_Ici.mpr (by exact_mod_cast hb)) (by exact_mod_cast hab)

/-- [CO.11] "`d₂(q) ∼ 2q log q` as `q → ∞`" (introduction, proof of `cor:range`). -/
theorem tendsto_d2_div_two_mul_log :
    Tendsto (fun q : ℕ => d2 q / (2 * q * Real.log q)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun q : ℕ => 1 / (q : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hA : Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) ^ 3 / (1 - 2 * (1 / (q : ℝ)))) atTop
      (𝓝 1) := by
    have h1 : Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) ^ 3) atTop (𝓝 ((1 - 0) ^ 3)) :=
      (tendsto_const_nhds.sub hinv).pow 3
    have h2 : Tendsto (fun q : ℕ => 1 - 2 * (1 / (q : ℝ))) atTop (𝓝 (1 - 2 * 0)) :=
      tendsto_const_nhds.sub (hinv.const_mul 2)
    have h3 := h1.div h2 (by norm_num)
    have e : ((1 : ℝ) - 0) ^ 3 / (1 - 2 * 0) = 1 := by norm_num
    rw [e] at h3
    exact h3
  have hlog : Tendsto (fun q : ℕ => Real.log (q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL1 : Tendsto (fun q : ℕ => Real.log (1 - 1 / (q : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun q : ℕ => 1 - 1 / (q : ℝ)) atTop (𝓝 1) := by
      have h0 := (tendsto_const_nhds (x := (1 : ℝ))).sub hinv
      rw [sub_zero] at h0
      exact h0
    have h3 := ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp h
    rw [Real.log_one] at h3
    exact h3
  have hL : Tendsto (fun q : ℕ => 1 + Real.log (1 - 1 / (q : ℝ)) / Real.log q) atTop
      (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add (hL1.div_atTop hlog)
  have hprod := hA.mul hL
  rw [one_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 3] with q hq3
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq3
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq2 : (q : ℝ) - 2 ≠ 0 := by intro h; linarith
  have hlq : Real.log q ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h1ne : 1 - 1 / (q : ℝ) ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have : (q : ℝ) = 1 := by field_simp at h; linarith
    linarith
  have hsplit : Real.log ((q : ℝ) - 1) = Real.log q + Real.log (1 - 1 / (q : ℝ)) := by
    rw [← Real.log_mul hq0 h1ne, mul_sub, mul_one, mul_one_div_cancel hq0]
  unfold d2
  rw [hsplit]
  field_simp

/-- [CO.12] "`d_nc(q) = (2q-1) log q` is increasing in `q`" (proof of `cor:all-but-one`). -/
theorem dnc_strictMonoOn :
    StrictMonoOn (fun q : ℕ => (2 * (q : ℝ) - 1) * Real.log q) (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  have hlab : Real.log a < Real.log b := Real.log_lt_log (by linarith) hab'
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  show (2 * (a : ℝ) - 1) * Real.log a < (2 * (b : ℝ) - 1) * Real.log b
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 * a - 1) (sub_pos.mpr hlab),
    mul_pos (by linarith : (0 : ℝ) < 2 * b - 2 * a) hlb]

/-- [CO.13] **Corollary 1.4 `cor:all-but-one`, without the algorithm and without citation.**
For every `d > 0` there is an integer `q_d ≥ 1` such that every integer `q ≥ 3`, `q ≠ q_d`,
satisfies one of: Potts zero-freeness on `K_ρ` with high probability (the conclusion of
Theorem 1.1, on which the FPTAS of Theorem 1.2 at `x = 0` rests), or `Z_{G_n}(q,0) = 0` with high
probability (`G_n` has no proper `q`-colouring, so the constant `0` is exact).  Proof plan:
`cor_all_but_one_arith` [CO.7]; `potts_zero_free` in the first case and `noncolorable_whp`
(`NonColor`, the first-moment bound behind [Achlioptas–Naor]) in the second.  The cases
`q = 1, 2`, which the paper settles by exact algorithms, are not stated. -/
theorem cor_all_but_one {d : ℝ} (hd : 0 < d) :
    ∃ qd : ℕ, 1 ≤ qd ∧ ∀ q : ℕ, 3 ≤ q → q ≠ qd →
      (∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z ∈ Kρ ρ, pottsZ G q z ≠ 0}) atTop (𝓝 1)) ∨
      Tendsto (fun n : ℕ => erProb n (d / n) {G | pottsZ G q 0 = 0}) atTop (𝓝 1) := by
  obtain ⟨qd, hqd1, h⟩ := cor_all_but_one_arith d
  refine ⟨qd, hqd1, fun q hq hne => ?_⟩
  rcases h q hq hne with h1 | h2
  · exact Or.inl (potts_zero_free hq hd h1)
  · exact Or.inr (noncolorable_whp (by omega) h2)

end CountColor

end

end ERZeroFreeness
