/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# The sharp entropy comparison (Lemma 5.2, `lem:entropy-comparison`) and threshold facts

`entropy_comparison`: `D(p ‖ u) = ∑ p_i log(q p_i) ≥ c_q (q ∑ p_i² - 1)` on the simplex,
`q ≥ 3`, with `c_q = (q-1)log(q-1)/(q(q-2))` (`cq`) and `0 log 0 = 0` (`Real.log 0 = 0`).
The paper deduces it from the Curie–Weiss–Potts variational problem of Costeniuc–Ellis–Touchette
[CET]; here it is proved directly.  The file also proves `0 < c_q < 1/2`, `d₂(q) = 2(q-1)² c_q`
and `d₂(q) < (q-1)²` (`eq:d2-below-square`).

Proof (no Lagrange multipliers).  Put `x_i = q p_i - 1` (so `∑ x_i = 0`, `x_i ≥ -1`);
the claim is `∑ g(x_i) ≥ 0` for `g(x) = (1+x)log(1+x) - x - c x²`, `c = c_q < 1/2`.
`g'' = 1/(1+x) - 2c`, so `g` is convex on `[-1, x_c]` and concave on `[x_c, ∞)`,
`x_c = 1/(2c) - 1 > 0`.  Merge all coordinates above `x_c` by concavity
(`g(a) + g(b) ≥ g(a+b-x_c) + g(x_c)` for `a, b ≥ x_c`) into one value `X`, then apply
Jensen (`ConvexOn.map_sum_le`) to the remaining `q - 1` values in `[-1, x_c]`:
`∑ g(x_i) ≥ φ(X) := g(X) + (q-1) g(-X/(q-1))`.  With `N = q - 1`,
`φ'(y) = log(N(1+y)/(N-y)) - 2y log N/(N-1)`, and writing `y = (N-1)/2 + u`,
`φ'(y) = 2 artanh(2u/(N+1)) - 2u log N/(N-1)`; since `artanh(w)/w` is increasing
(`Real.hasSum_log_sub_log_of_abs_lt_one`) and `artanh((N-1)/(N+1)) = (log N)/2`,
`φ' ≥ 0` on `[0, (N-1)/2]`, `≤ 0` on `[(N-1)/2, N-1]`, `≥ 0` on `[N-1, N]`;
with `φ(0) = φ(N-1) = 0` this gives `φ ≥ 0` on `[0, N]`.
`c_q < 1/2` and `d₂(q) < (q-1)²` both reduce to `log x < (x - 1/x)/2` for `x = q - 1 > 1`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- `log x < (x - x⁻¹)/2` for `x > 1` (equivalently `u < sinh u` for `u > 0`). -/
private lemma entropy_log_lt_half_sub_inv {x : ℝ} (hx : 1 < x) :
    Real.log x < (x - x⁻¹) / 2 := by
  have hx0 : 0 < x := by linarith
  have hl : 0 < Real.log x := Real.log_pos hx
  have h := Real.self_lt_sinh_iff.mpr hl
  rw [Real.sinh_eq, Real.exp_neg, Real.exp_log hx0] at h
  exact h

/-- `c_q > 0` for `q ≥ 3`. -/
theorem cq_pos {q : ℕ} (hq : 3 ≤ q) : 0 < cq q := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  unfold cq
  have h1 : 0 < Real.log ((q : ℝ) - 1) := Real.log_pos (by linarith)
  have h2 : 0 < (q : ℝ) - 1 := by linarith
  have h3 : 0 < (q : ℝ) * ((q : ℝ) - 2) := by nlinarith
  positivity

/-- `c_q < 1/2` for `q ≥ 3`, from `log x < (x - x⁻¹)/2` at `x = q - 1`. -/
theorem cq_lt_half {q : ℕ} (hq : 3 ≤ q) : cq q < 1 / 2 := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  unfold cq
  have h3 : 0 < (q : ℝ) * ((q : ℝ) - 2) := by nlinarith
  rw [div_lt_iff₀ h3]
  have hx : (1 : ℝ) < (q : ℝ) - 1 := by linarith
  have h := entropy_log_lt_half_sub_inv hx
  have h2 : 0 < (q : ℝ) - 1 := by linarith
  -- `(q-1) log(q-1) < (q-1) · ((q-1) - (q-1)⁻¹)/2 = q(q-2)/2`
  have key : ((q : ℝ) - 1) * Real.log ((q : ℝ) - 1) <
      ((q : ℝ) - 1) * ((((q : ℝ) - 1) - ((q : ℝ) - 1)⁻¹) / 2) :=
    mul_lt_mul_of_pos_left h h2
  have e : ((q : ℝ) - 1) * ((((q : ℝ) - 1) - ((q : ℝ) - 1)⁻¹) / 2) =
      1 / 2 * ((q : ℝ) * ((q : ℝ) - 2)) := by
    field_simp
    ring
  linarith

/-- `d₂(q) = 2(q-1)² c_q`. -/
theorem d2_eq (q : ℕ) : d2 q = 2 * ((q : ℝ) - 1) ^ 2 * cq q := by
  unfold d2 cq
  ring

/-- `d₂(q) < (q-1)²` for `q ≥ 3` (`eq:d2-below-square`). -/
theorem d2_lt_sq {q : ℕ} (hq : 3 ≤ q) : d2 q < ((q : ℝ) - 1) ^ 2 := by
  rw [d2_eq]
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have h2 : 0 < ((q : ℝ) - 1) ^ 2 := by nlinarith
  have := cq_lt_half hq
  nlinarith

/-- `g(x) = (1+x) log(1+x) - x - c x²`. -/
private def entG (c x : ℝ) : ℝ := (1 + x) * Real.log (1 + x) - x - c * x ^ 2

private lemma entG_continuous (c : ℝ) : Continuous (entG c) := by
  unfold entG
  have h : Continuous fun x : ℝ => (1 + x) * Real.log (1 + x) :=
    Real.continuous_mul_log.comp (continuous_const.add continuous_id)
  exact (h.sub continuous_id).sub (continuous_const.mul (continuous_id.pow 2))

private lemma entG_hasDerivAt (c : ℝ) {x : ℝ} (hx : 1 + x ≠ 0) :
    HasDerivAt (entG c) (Real.log (1 + x) - 2 * c * x) x := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id x).const_add 1
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x := h1.log hx
  have h2 := h1.mul hlog
  have h3 := (h2.sub (hasDerivAt_id' x)).sub ((hasDerivAt_pow 2 x).const_mul c)
  refine h3.congr_deriv ?_
  field_simp
  ring

private lemma entG_convexOn {c : ℝ} (hc : 0 < c) :
    ConvexOn ℝ (Set.Icc (-1) (1 / (2 * c) - 1)) (entG c) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _) (entG_continuous c).continuousOn
    (f' := fun x => Real.log (1 + x) - 2 * c * x) (f'' := fun x => (1 + x)⁻¹ - 2 * c)
  · intro x hx
    rw [interior_Icc] at hx
    exact (entG_hasDerivAt c (by linarith [hx.1])).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + x)) x :=
      h1.log (by linarith [hx.1])
    have h3 := hlog.sub ((hasDerivAt_id' x).const_mul (2 * c))
    refine (h3.congr_deriv ?_).hasDerivWithinAt
    simp
  · intro x hx
    rw [interior_Icc] at hx
    have h1 : 0 < 1 + x := by linarith [hx.1]
    have h2 : 1 + x < 1 / (2 * c) := by linarith [hx.2]
    have h3 : 2 * c < (1 + x)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) h1]
      rw [one_div] at h2
      exact h2
    linarith

/-- Increments of `g` decrease on the concave range `[1/(2c) - 1, ∞)`. -/
private lemma entG_incr_antitoneOn {c : ℝ} (hc : 0 < c) {e : ℝ} (he : 0 ≤ e) :
    AntitoneOn (fun s => entG c (s + e) - entG c s) (Set.Ici (1 / (2 * c) - 1)) := by
  have ha : -1 < 1 / (2 * c) - 1 := by
    have : 0 < 1 / (2 * c) := by positivity
    linarith
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici _)
    (((entG_continuous c).comp (continuous_id.add continuous_const)).sub
      (entG_continuous c)).continuousOn
    (f' := fun s => (Real.log (1 + (s + e)) - 2 * c * (s + e)) - (Real.log (1 + s) - 2 * c * s))
  · intro s hs
    rw [interior_Ici, Set.mem_Ioi] at hs
    have hs' : -1 < s := lt_trans ha hs
    have h1 := (entG_hasDerivAt c (x := s + e) (by linarith)).comp s
      ((hasDerivAt_id' s).add_const e)
    have h2 := entG_hasDerivAt c (x := s) (by linarith)
    refine ((h1.sub h2).congr_deriv ?_).hasDerivWithinAt
    simp
  · intro s hs
    rw [interior_Ici, Set.mem_Ioi] at hs
    have hs' : 1 / (2 * c) < 1 + s := by linarith
    have h1s : 0 < 1 + s := lt_trans (by positivity) hs'
    -- log((1+s+e)/(1+s)) ≤ e/(1+s) ≤ 2 c e
    have hlog : Real.log (1 + (s + e)) - Real.log (1 + s) ≤ e / (1 + s) := by
      rw [← Real.log_div (by linarith) h1s.ne']
      have := Real.log_le_sub_one_of_pos (x := (1 + (s + e)) / (1 + s))
        (div_pos (by linarith) h1s)
      have e1 : (1 + (s + e)) / (1 + s) - 1 = e / (1 + s) := by field_simp; ring
      linarith
    have hfrac : e / (1 + s) ≤ 2 * c * e := by
      rw [div_le_iff₀ h1s]
      have : 1 ≤ 2 * c * (1 + s) := by
        rw [div_lt_iff₀ (by positivity)] at hs'
        linarith
      nlinarith
    nlinarith

private lemma entG_incr_le {c : ℝ} (hc : 0 < c) {s e : ℝ} (hs : 1 / (2 * c) - 1 ≤ s)
    (he : 0 ≤ e) :
    entG c (s + e) - entG c s ≤ entG c (1 / (2 * c) - 1 + e) - entG c (1 / (2 * c) - 1) :=
  entG_incr_antitoneOn hc he (Set.self_mem_Ici) hs hs

/-- Merging the coordinates above the inflection point by concavity. -/
private lemma entG_merge {c : ℝ} (hc : 0 < c) {ι : Type*} (T : Finset ι) (e : ι → ℝ)
    (he : ∀ i ∈ T, 0 ≤ e i) {M : ℝ} (hM : 1 / (2 * c) - 1 ≤ M) :
    entG c (M + ∑ i ∈ T, e i) - entG c M ≤
      ∑ i ∈ T, (entG c (1 / (2 * c) - 1 + e i) - entG c (1 / (2 * c) - 1)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert j T hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    have hT : 0 ≤ ∑ i ∈ T, e i :=
      Finset.sum_nonneg fun i hi => he i (Finset.mem_insert_of_mem hi)
    have h1 := entG_incr_le hc (s := M + ∑ i ∈ T, e i) (e := e j) (by linarith)
      (he j (Finset.mem_insert_self j T))
    have h2 := ih fun i hi => he i (Finset.mem_insert_of_mem hi)
    have e1 : M + (e j + ∑ i ∈ T, e i) = M + ∑ i ∈ T, e i + e j := by ring
    rw [e1]
    linarith

/-- `w ↦ (log(1+w) - log(1-w))/w` is nondecreasing on `[0,1)` (series of `2 artanh`). -/
private lemma entA_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) :
    v * (Real.log (1 + u) - Real.log (1 - u)) ≤ u * (Real.log (1 + v) - Real.log (1 - v)) := by
  rcases hu.eq_or_lt with rfl | hu'
  · simp
  · have hv0 : 0 < v := lt_of_lt_of_le hu' huv
    have hsu := (Real.hasSum_log_sub_log_of_abs_lt_one (x := u)
      (by rw [abs_lt]; constructor <;> linarith)).mul_left v
    have hsv := (Real.hasSum_log_sub_log_of_abs_lt_one (x := v)
      (by rw [abs_lt]; constructor <;> linarith)).mul_left u
    refine hasSum_le (fun k => ?_) hsu hsv
    have h1 : u ^ (2 * k) ≤ v ^ (2 * k) := pow_le_pow_left₀ hu huv _
    have h2 : 0 ≤ 2 * (1 / (2 * (k : ℝ) + 1)) := by positivity
    have h3 : 0 ≤ u * v := by positivity
    calc v * (2 * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1))
        = (2 * (1 / (2 * (k : ℝ) + 1))) * (u * v) * u ^ (2 * k) := by ring
      _ ≤ (2 * (1 / (2 * (k : ℝ) + 1))) * (u * v) * v ^ (2 * k) := by gcongr
      _ = u * (2 * (1 / (2 * (k : ℝ) + 1)) * v ^ (2 * k + 1)) := by ring

/-- `c = N log N / ((N+1)(N-1))`, i.e. `c_q` with `N = q - 1`. -/
private def entC (N : ℝ) : ℝ := N * Real.log N / ((N + 1) * (N - 1))

/-- `φ(y) = g(y) + N g(-y/N)`. -/
private def entPhi (N y : ℝ) : ℝ := entG (entC N) y + N * entG (entC N) (-y / N)

/-- `φ'(y)`. -/
private def entPhi' (N y : ℝ) : ℝ :=
  Real.log (1 + y) - Real.log (1 + -y / N) - 2 * entC N * (1 + 1 / N) * y

private lemma entPhi_continuous (N : ℝ) : Continuous (entPhi N) := by
  unfold entPhi
  exact (entG_continuous _).add
    (continuous_const.mul ((entG_continuous _).comp (continuous_neg.div_const N)))

private lemma entPhi_hasDerivAt {N : ℝ} (hN : 1 < N) {y : ℝ} (hy1 : -1 < y) (hy2 : y < N) :
    HasDerivAt (entPhi N) (entPhi' N y) y := by
  have hN0 : 0 < N := by linarith
  have h1 := entG_hasDerivAt (entC N) (x := y) (by linarith)
  have hlin : HasDerivAt (fun y : ℝ => -y / N) (-1 / N) y := (hasDerivAt_neg y).div_const N
  have hx : 1 + -y / N ≠ 0 := by
    have : y / N < 1 := by rw [div_lt_one hN0]; exact hy2
    have : 0 < 1 + -y / N := by rw [neg_div]; linarith
    exact this.ne'
  have h2 := (entG_hasDerivAt (entC N) hx).comp y hlin
  have h3 := h1.add (h2.const_mul N)
  refine h3.congr_deriv ?_
  unfold entPhi'
  field_simp
  ring

/-- `(N-1)/(N+1) · φ'(y) = w₀ A(w) - w A(w₀)` with `w = (2y+1-N)/(N+1)`, `w₀ = (N-1)/(N+1)`,
`A(w) = log(1+w) - log(1-w)`. -/
private lemma entPhi'_eq {N : ℝ} (hN : 1 < N) {y : ℝ} (hy1 : -1 < y) (hy2 : y < N) :
    (N - 1) / (N + 1) * entPhi' N y =
      (N - 1) / (N + 1) * (Real.log (1 + (2 * y + 1 - N) / (N + 1)) -
          Real.log (1 - (2 * y + 1 - N) / (N + 1))) -
        (2 * y + 1 - N) / (N + 1) * (Real.log (1 + (N - 1) / (N + 1)) -
          Real.log (1 - (N - 1) / (N + 1))) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N + 1 := by linarith
  have hN2 : 0 < N - 1 := by linarith
  have hy1' : 0 < 1 + y := by linarith
  have hy2' : 0 < N - y := by linarith
  have e1 : 1 + (2 * y + 1 - N) / (N + 1) = 2 * (1 + y) / (N + 1) := by field_simp; ring
  have e2 : 1 - (2 * y + 1 - N) / (N + 1) = 2 * (N - y) / (N + 1) := by field_simp; ring
  have e3 : 1 + (N - 1) / (N + 1) = 2 * N / (N + 1) := by field_simp; ring
  have e4 : 1 - (N - 1) / (N + 1) = 2 / (N + 1) := by field_simp; ring
  have e5 : 1 + -y / N = (N - y) / N := by field_simp; ring
  have l1 : Real.log (2 * (1 + y) / (N + 1)) =
      Real.log 2 + Real.log (1 + y) - Real.log (N + 1) := by
    rw [Real.log_div (by positivity) hN1.ne', Real.log_mul (by norm_num) hy1'.ne']
  have l2 : Real.log (2 * (N - y) / (N + 1)) =
      Real.log 2 + Real.log (N - y) - Real.log (N + 1) := by
    rw [Real.log_div (by positivity) hN1.ne', Real.log_mul (by norm_num) hy2'.ne']
  have l3 : Real.log (2 * N / (N + 1)) = Real.log 2 + Real.log N - Real.log (N + 1) := by
    rw [Real.log_div (by positivity) hN1.ne', Real.log_mul (by norm_num) hN0.ne']
  have l4 : Real.log (2 / (N + 1)) = Real.log 2 - Real.log (N + 1) := by
    rw [Real.log_div (by norm_num) hN1.ne']
  have l5 : Real.log ((N - y) / N) = Real.log (N - y) - Real.log N := by
    rw [Real.log_div hy2'.ne' hN0.ne']
  unfold entPhi'
  rw [e1, e2, e3, e4, e5, l1, l2, l3, l4, l5]
  unfold entC
  field_simp
  ring

private lemma entA_neg (u : ℝ) :
    Real.log (1 + -u) - Real.log (1 - -u) = -(Real.log (1 + u) - Real.log (1 - u)) := by
  rw [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

private lemma entPhi'_nonneg_left {N : ℝ} (hN : 1 < N) {y : ℝ} (hy1 : 0 < y)
    (hy2 : y < (N - 1) / 2) : 0 ≤ entPhi' N y := by
  have hN1 : 0 < N + 1 := by linarith
  have hw0 : 0 < (N - 1) / (N + 1) := div_pos (by linarith) hN1
  have key := entPhi'_eq hN (y := y) (by linarith) (by linarith)
  have hw : (2 * y + 1 - N) / (N + 1) = -((N - 1 - 2 * y) / (N + 1)) := by
    field_simp; ring
  rw [hw, entA_neg] at key
  have hu0 : 0 ≤ (N - 1 - 2 * y) / (N + 1) := div_nonneg (by linarith) hN1.le
  have huv : (N - 1 - 2 * y) / (N + 1) ≤ (N - 1) / (N + 1) := by
    apply div_le_div_of_nonneg_right _ hN1.le; linarith
  have hv1 : (N - 1) / (N + 1) < 1 := by rw [div_lt_one hN1]; linarith
  have m := entA_mono hu0 huv hv1
  have : 0 ≤ (N - 1) / (N + 1) * entPhi' N y := by rw [key]; linarith
  nlinarith

private lemma entPhi'_nonpos_mid {N : ℝ} (hN : 1 < N) {y : ℝ} (hy1 : (N - 1) / 2 < y)
    (hy2 : y < N - 1) : entPhi' N y ≤ 0 := by
  have hN1 : 0 < N + 1 := by linarith
  have hw0 : 0 < (N - 1) / (N + 1) := div_pos (by linarith) hN1
  have key := entPhi'_eq hN (y := y) (by linarith) (by linarith)
  have hu0 : 0 ≤ (2 * y + 1 - N) / (N + 1) := div_nonneg (by linarith) hN1.le
  have huv : (2 * y + 1 - N) / (N + 1) ≤ (N - 1) / (N + 1) := by
    apply div_le_div_of_nonneg_right _ hN1.le; linarith
  have hv1 : (N - 1) / (N + 1) < 1 := by rw [div_lt_one hN1]; linarith
  have m := entA_mono hu0 huv hv1
  have : (N - 1) / (N + 1) * entPhi' N y ≤ 0 := by rw [key]; linarith
  nlinarith

private lemma entPhi'_nonneg_right {N : ℝ} (hN : 1 < N) {y : ℝ} (hy1 : N - 1 < y)
    (hy2 : y < N) : 0 ≤ entPhi' N y := by
  have hN1 : 0 < N + 1 := by linarith
  have hw0 : 0 < (N - 1) / (N + 1) := div_pos (by linarith) hN1
  have key := entPhi'_eq hN (y := y) (by linarith) hy2
  have hu0 : 0 ≤ (N - 1) / (N + 1) := hw0.le
  have huv : (N - 1) / (N + 1) ≤ (2 * y + 1 - N) / (N + 1) := by
    apply div_le_div_of_nonneg_right _ hN1.le; linarith
  have hv1 : (2 * y + 1 - N) / (N + 1) < 1 := by rw [div_lt_one hN1]; linarith
  have m := entA_mono hu0 huv hv1
  have : 0 ≤ (N - 1) / (N + 1) * entPhi' N y := by rw [key]; linarith
  nlinarith

private lemma entPhi_zero (N : ℝ) : entPhi N 0 = 0 := by
  simp [entPhi, entG]

private lemma entPhi_sub_one {N : ℝ} (hN : 1 < N) : entPhi N (N - 1) = 0 := by
  have hN0 : 0 < N := by linarith
  have hN2 : 0 < N - 1 := by linarith
  unfold entPhi entG entC
  have e1 : 1 + (N - 1) = N := by ring
  have e2 : 1 + -(N - 1) / N = N⁻¹ := by field_simp; ring
  rw [e1, e2, Real.log_inv]
  field_simp
  ring

/-- `φ ≥ 0` on `[0, N]`: `φ` increases on `[0, (N-1)/2]`, decreases on `[(N-1)/2, N-1]` and
increases on `[N-1, N]`, while `φ(0) = φ(N-1) = 0`. -/
private lemma entPhi_nonneg {N : ℝ} (hN : 1 < N) {y : ℝ} (hy0 : 0 ≤ y) (hyN : y ≤ N) :
    0 ≤ entPhi N y := by
  rcases le_or_gt y ((N - 1) / 2) with h1 | h1
  · have hmono : MonotoneOn (entPhi N) (Set.Icc 0 ((N - 1) / 2)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (entPhi_continuous N).continuousOn (f' := entPhi' N)
      · intro x hx
        rw [interior_Icc] at hx
        exact (entPhi_hasDerivAt hN (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact entPhi'_nonneg_left hN hx.1 hx.2
    have := hmono ⟨le_refl 0, by linarith⟩ ⟨hy0, h1⟩ hy0
    rwa [entPhi_zero] at this
  · rcases le_or_gt y (N - 1) with h2 | h2
    · have hanti : AntitoneOn (entPhi N) (Set.Icc ((N - 1) / 2) (N - 1)) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
          (entPhi_continuous N).continuousOn (f' := entPhi' N)
        · intro x hx
          rw [interior_Icc] at hx
          exact (entPhi_hasDerivAt hN (by linarith [hx.1]) (by linarith [hx.2])).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact entPhi'_nonpos_mid hN hx.1 hx.2
      have := hanti ⟨h1.le, h2⟩ ⟨by linarith, le_refl _⟩ h2
      rwa [entPhi_sub_one hN] at this
    · have hmono : MonotoneOn (entPhi N) (Set.Icc (N - 1) N) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
          (entPhi_continuous N).continuousOn (f' := entPhi' N)
        · intro x hx
          rw [interior_Icc] at hx
          exact (entPhi_hasDerivAt hN (by linarith [hx.1]) hx.2).hasDerivWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          exact entPhi'_nonneg_right hN hx.1 hx.2
      have := hmono ⟨le_refl _, by linarith⟩ ⟨h2.le, hyN⟩ h2.le
      rwa [entPhi_sub_one hN] at this

/-- The core inequality: `∑ g(x_i) ≥ 0` for `x_i ≥ -1`, `∑ x_i = 0`, `c = c_q`. -/
private lemma entG_sum_nonneg {q : ℕ} (hq : 3 ≤ q) (x : Fin q → ℝ) (hx : ∀ i, -1 ≤ x i)
    (hsum : ∑ i, x i = 0) : 0 ≤ ∑ i, entG (cq q) (x i) := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  set N : ℝ := (q : ℝ) - 1 with hN_def
  have hN : 1 < N := by linarith
  have hcN : cq q = entC N := by
    simp only [cq, entC, hN_def]
    congr 1
    ring
  set c := cq q with hc_def
  have hc0 : 0 < c := cq_pos hq
  have hc1 : c < 1 / 2 := cq_lt_half hq
  set a := 1 / (2 * c) - 1 with ha_def
  have ha : 0 < a := by
    have : 1 < 1 / (2 * c) := by rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  -- a maximizing index
  have hne : (Finset.univ : Finset (Fin q)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ x hne
  have hmax : ∀ i, x i ≤ x i₀ := fun i => hi₀ i (Finset.mem_univ i)
  have hM0 : 0 ≤ x i₀ := by
    have h1 : ∑ i, x i ≤ ∑ _i : Fin q, x i₀ := Finset.sum_le_sum fun i _ => hmax i
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    rw [hsum] at h1
    have : (0 : ℝ) < q := by linarith
    nlinarith
  set T := Finset.univ.erase i₀ with hT_def
  have hcardT : (T.card : ℝ) = N := by
    rw [hT_def, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (by omega)]
    simp [hN_def]
  set z : Fin q → ℝ := fun i => min (x i) a with hz_def
  set e : Fin q → ℝ := fun i => x i - min (x i) a with he_def
  set X := x i₀ + ∑ i ∈ T, e i with hX_def
  have he0 : ∀ i, 0 ≤ e i := fun i => by simp only [he_def]; linarith [min_le_left (x i) a]
  have hdec : ∀ i, entG c (x i) = entG c (z i) + (entG c (a + e i) - entG c a) := by
    intro i
    by_cases h : x i ≤ a
    · simp only [hz_def, he_def, min_eq_left h, sub_self, add_zero]
    · have h : a < x i := lt_of_not_ge h
      simp only [hz_def, he_def, min_eq_right h.le]
      have : a + (x i - a) = x i := by ring
      rw [this]
      ring
  -- merging the coordinates above the inflection point
  have hB : entG c X ≤ entG c (x i₀) + ∑ i ∈ T, (entG c (a + e i) - entG c a) := by
    by_cases hMa : a ≤ x i₀
    · have := entG_merge hc0 T e (fun i _ => he0 i) hMa
      linarith
    · have hMa : x i₀ < a := lt_of_not_ge hMa
      have hz : ∀ i ∈ T, e i = 0 := by
        intro i _
        have : x i ≤ a := (hmax i).trans hMa.le
        simp only [he_def, min_eq_left this, sub_self]
      have h1 : ∑ i ∈ T, e i = 0 := Finset.sum_eq_zero hz
      have h2 : ∑ i ∈ T, (entG c (a + e i) - entG c a) = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hz i hi, add_zero, sub_self]
      rw [hX_def, h1, h2, add_zero, add_zero]
  -- Jensen for the remaining `q - 1` values in the convex range
  have hzsum : ∑ i ∈ T, z i = -X := by
    have h1 : ∑ i ∈ T, x i = -x i₀ := by
      have := Finset.add_sum_erase Finset.univ x (Finset.mem_univ i₀)
      rw [hsum] at this
      linarith
    have h2 : ∑ i ∈ T, z i = ∑ i ∈ T, x i - ∑ i ∈ T, e i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [hz_def, he_def]; ring
    rw [h2, h1, hX_def]
    ring
  have hzmem : ∀ i ∈ T, z i ∈ Set.Icc (-1) a := fun i _ =>
    ⟨le_min (hx i) (by linarith), min_le_right _ _⟩
  have hN0 : 0 < N := by linarith
  have hC : N * entG c (-X / N) ≤ ∑ i ∈ T, entG c (z i) := by
    have hJ := (entG_convexOn hc0).map_sum_le (t := T) (w := fun _ => 1 / N) (p := z)
      (fun _ _ => by positivity)
      (by rw [Finset.sum_const, nsmul_eq_mul, hcardT]; field_simp) hzmem
    simp only [smul_eq_mul, ← Finset.mul_sum, hzsum] at hJ
    have e1 : 1 / N * -X = -X / N := by ring
    rw [e1] at hJ
    have := mul_le_mul_of_nonneg_left hJ hN0.le
    rw [← mul_assoc, mul_one_div_cancel hN0.ne', one_mul] at this
    exact this
  -- the range of the merged value
  have hX0 : 0 ≤ X := by
    have : 0 ≤ ∑ i ∈ T, e i := Finset.sum_nonneg fun i _ => he0 i
    linarith
  have hXN : X ≤ N := by
    have : ∑ _i ∈ T, (-1 : ℝ) ≤ ∑ i ∈ T, z i := Finset.sum_le_sum fun i hi => (hzmem i hi).1
    rw [Finset.sum_const, nsmul_eq_mul, hcardT, hzsum] at this
    linarith
  have hphi := entPhi_nonneg hN hX0 hXN
  unfold entPhi at hphi
  rw [← hcN] at hphi
  -- combine
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i₀)]
  have hsplit : ∑ i ∈ T, entG c (x i) =
      ∑ i ∈ T, entG c (z i) + ∑ i ∈ T, (entG c (a + e i) - entG c a) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hdec i
  rw [hsplit]
  linarith

/-- **Lemma 5.2 (`lem:entropy-comparison`)**, after Costeniuc–Ellis–Touchette:
`c_q (q ∑ p_i² - 1) ≤ D(p ‖ u) = ∑ p_i log(q p_i)` for every probability vector `p` on `[q]`,
`q ≥ 3`. -/
theorem entropy_comparison {q : ℕ} (hq : 3 ≤ q) (p : Fin q → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) :
    cq q * ((q : ℝ) * ∑ i, p i ^ 2 - 1) ≤ ∑ i, p i * Real.log ((q : ℝ) * p i) := by
  have hq0 : (0 : ℝ) < q := by
    have : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hx : ∀ i, -1 ≤ (q : ℝ) * p i - 1 := fun i => by nlinarith [hp0 i]
  have hsum : ∑ i, ((q : ℝ) * p i - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp1]
    simp
  have h := entG_sum_nonneg hq (fun i => (q : ℝ) * p i - 1) hx hsum
  have hterm : ∀ i, entG (cq q) ((q : ℝ) * p i - 1) =
      (q : ℝ) * (p i * Real.log ((q : ℝ) * p i)) - ((q : ℝ) * p i - 1) -
        cq q * ((q : ℝ) ^ 2 * p i ^ 2 - 2 * (q : ℝ) * p i + 1) := by
    intro i
    unfold entG
    have : 1 + ((q : ℝ) * p i - 1) = (q : ℝ) * p i := by ring
    rw [this]
    ring
  have expand : ∑ i, entG (cq q) ((q : ℝ) * p i - 1) =
      (q : ℝ) * (∑ i, p i * Real.log ((q : ℝ) * p i) - cq q * ((q : ℝ) * ∑ i, p i ^ 2 - 1)) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hsum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hp1]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  rw [expand] at h
  have := (mul_nonneg_iff_of_pos_left hq0).mp h
  linarith

end

end ERZeroFreeness
