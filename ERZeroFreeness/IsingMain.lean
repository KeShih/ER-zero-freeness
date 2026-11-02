/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.IsingSecondMoment
import ERZeroFreeness.IsingRelation
import ERZeroFreeness.Main

/-!
# Theorem 1.5(i): zero-freeness for the Ising antiferromagnet

`ising_af_zero_free` is the zero-freeness assertion of Theorem 1.5(i) (`thm:ising-applications`):
for `0 < x_* < 1` with `d((1-x_*)/(1+x_*))² < 1` there is `ρ > 0` such that, with probability
tending to one, `Z_{G_n}(2,z) ≠ 0` whenever `dist(z, [x_*, 1]) ≤ ρ`.

Proof (Step 2 of Section 7).  Put `s = (1-x_*)/(1+x_*)`, so that `ds² < 1` and `x_s = x_*`, and
choose `r > 0` with `d((s+r)² + 2r) < 1`.  On the tube `L_r(I_s)`, `|t| ≤ s + r` and
`(Re t)_+ ≤ r`, so `ising_second_moment` bounds `E|Ẑ_{G_n}(t)|²` uniformly; the pointwise bound
`‖a‖ ≤ 1/2 + ‖a‖²/2` (in place of Cauchy–Schwarz) gives the first-moment hypothesis
`eq:first-moment-hypothesis` for `q = 2` (`ising_first_moment`), and `prop_zero_free_moment`
with `q = 2` gives zero-freeness near `[x_s, 1] = [x_*, 1]`.  `ising_af_tplane_zero_free` is the
corresponding statement in the `t`-plane.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- On the tube `L_r(I_s)`: `‖t‖ ≤ s + r`. -/
private lemma IsingMain_norm_le_of_mem_tube {s r : ℝ} {t : ℂ} (ht : t ∈ tube s r) :
    ‖t‖ ≤ s + r := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxt⟩ := ht
  have hx : ‖(x : ℂ)‖ ≤ s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc ‖t‖ = ‖(t - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖t - x‖ + ‖(x : ℂ)‖ := norm_add_le _ _
    _ ≤ r + s := add_le_add hxt hx
    _ = s + r := add_comm r s

/-- On the tube `L_r(I_s)`: `Re t ≤ r`. -/
private lemma IsingMain_re_le_of_mem_tube {s r : ℝ} {t : ℂ} (ht : t ∈ tube s r) :
    t.re ≤ r := by
  obtain ⟨x, ⟨hx1, hx2⟩, hxt⟩ := ht
  have h1 : (t - x).re ≤ ‖t - x‖ := Complex.re_le_norm _
  rw [Complex.sub_re, Complex.ofReal_re] at h1
  linarith

/-- Choice of the tube radius: `Λ₀ = d((s+r)² + 2r) < 1` for some `r > 0`, by continuity at
`r = 0`, where the value is `d s² < 1`. -/
private lemma IsingMain_exists_r {d s : ℝ} (hds : d * s ^ 2 < 1) :
    ∃ r > 0, d * ((s + r) ^ 2 + 2 * r) < 1 := by
  have e : ∀ᶠ r in 𝓝 (0 : ℝ), d * ((s + r) ^ 2 + 2 * r) < 1 :=
    ContinuousAt.eventually_lt (f := fun r : ℝ => d * ((s + r) ^ 2 + 2 * r))
      (g := fun _ => (1 : ℝ)) (by fun_prop) (by fun_prop)
      (by simp only [add_zero, mul_zero]; exact hds)
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 e
  have hmem : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]
    linarith
  exact ⟨δ / 2, by linarith, hδP hmem⟩

/-- Pointwise `‖a‖ ≤ 1/2 + ‖a‖²/2`. -/
private lemma IsingMain_norm_le_half (a : ℂ) : ‖a‖ ≤ 1 / 2 + 1 / 2 * ‖a‖ ^ 2 := by
  nlinarith [sq_nonneg (‖a‖ - 1)]

/-- The first-moment hypothesis `eq:first-moment-hypothesis` for `q = 2`: if `s ≥ 0` and
`ds² < 1`, then for some `r > 0`, `E|Ẑ_{G_n}(t)|` is bounded uniformly in `n ≥ d` and
`t ∈ L_r(I_s)`. -/
theorem ising_first_moment {d : ℝ} (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s) (hds : d * s ^ 2 < 1) :
    ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ t ∈ tube s r,
      erExp n (d / n) (fun G => ‖(zhat G 2).eval t‖) ≤ B := by
  obtain ⟨r, hr, hΛ₀⟩ := IsingMain_exists_r hds
  obtain ⟨C, hC, hCb⟩ := ising_second_moment (T := s + r) hd (by linarith)
  refine ⟨r, hr, 1 / 2 + 1 / 2 * (C * (Real.sqrt (1 - d * ((s + r) ^ 2 + 2 * r)))⁻¹), ?_⟩
  intro n hn t ht
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  have htn := IsingMain_norm_le_of_mem_tube ht
  have htre := IsingMain_re_le_of_mem_tube ht
  have hmax : max t.re 0 ≤ r := max_le htre hr.le
  -- `Λ(t) ≤ Λ₀ < 1` on the tube
  have hΛt : d * (‖t‖ ^ 2 + 2 * max t.re 0) ≤ d * ((s + r) ^ 2 + 2 * r) := by
    have h1 : ‖t‖ ^ 2 ≤ (s + r) ^ 2 := pow_le_pow_left₀ (norm_nonneg t) htn 2
    have h2 : ‖t‖ ^ 2 + 2 * max t.re 0 ≤ (s + r) ^ 2 + 2 * r := by linarith
    exact mul_le_mul_of_nonneg_left h2 hd.le
  have hΛt1 : d * (‖t‖ ^ 2 + 2 * max t.re 0) < 1 := lt_of_le_of_lt hΛt hΛ₀
  have hsec := hCb n hn t htn hΛt1
  -- `(1 - Λ(t))^{-1/2} ≤ (1 - Λ₀)^{-1/2}`
  have hsqrt : (Real.sqrt (1 - d * (‖t‖ ^ 2 + 2 * max t.re 0)))⁻¹ ≤
      (Real.sqrt (1 - d * ((s + r) ^ 2 + 2 * r)))⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.2 (by linarith)) (Real.sqrt_le_sqrt (by linarith))
  have hsec' : erExp n (d / n) (fun G => ‖(zhat G 2).eval t‖ ^ 2) ≤
      C * (Real.sqrt (1 - d * ((s + r) ^ 2 + 2 * r)))⁻¹ :=
    hsec.trans (mul_le_mul_of_nonneg_left hsqrt hC.le)
  calc erExp n (d / n) (fun G => ‖(zhat G 2).eval t‖)
      ≤ erExp n (d / n) (fun G => 1 / 2 + 1 / 2 * ‖(zhat G 2).eval t‖ ^ 2) :=
        erExp_mono hp0 hp1 fun G => IsingMain_norm_le_half _
    _ = 1 / 2 + 1 / 2 * erExp n (d / n) (fun G => ‖(zhat G 2).eval t‖ ^ 2) := by
        rw [erExp_add (fun _ => (1 / 2 : ℝ)) (fun G => 1 / 2 * ‖(zhat G 2).eval t‖ ^ 2),
          erExp_const, erExp_const_mul]
    _ ≤ 1 / 2 + 1 / 2 * (C * (Real.sqrt (1 - d * ((s + r) ^ 2 + 2 * r)))⁻¹) := by
        linarith

/-- `t`-plane zero-freeness for `q = 2`: if `0 < s < 1` and `ds² < 1`, then for some `ρ > 0`,
with probability tending to one, `Ẑ_{G_n}` has no zeros on the tube `L_ρ(I_s)`.  This is the
zero-free input of the counting assertion of Theorem 1.5(i) (Proposition 8.4(i)). -/
theorem ising_af_tplane_zero_free {d : ℝ} (hd : 0 < d) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hds : d * s ^ 2 < 1) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ t ∈ tube s ρ, (zhat G 2).eval t ≠ 0}) atTop (𝓝 1) := by
  obtain ⟨r, hr, B, hB⟩ := ising_first_moment hd hs0.le hds
  exact zero_free_of_first_moment (q := 2) le_rfl hd hs0 hs1 (by norm_num; linarith) hds hr hB

/-- For `s = (1-x_*)/(1+x_*)`: `x_s = (1 - (2-1)s)/(1+s) = x_*`. -/
private lemma IsingMain_xs_eq {xs : ℝ} (hx0 : 0 < xs) :
    (1 - (((2 : ℕ) : ℝ) - 1) * ((1 - xs) / (1 + xs))) / (1 + (1 - xs) / (1 + xs)) = xs := by
  have h1x : (1 + xs) ≠ 0 := by linarith
  have h2 : (1 + (1 - xs) / (1 + xs)) = 2 / (1 + xs) := by
    field_simp
    ring
  have h3 : (1 - (((2 : ℕ) : ℝ) - 1) * ((1 - xs) / (1 + xs))) = 2 * xs / (1 + xs) := by
    push_cast
    field_simp
    ring
  rw [h2, h3]
  field_simp

/-- **Theorem 1.5(i)** (`thm:ising-applications`, zero-field Ising antiferromagnet),
zero-freeness assertion: for `0 < x_* < 1` with `d((1-x_*)/(1+x_*))² < 1` there is `ρ > 0` such
that, with probability tending to one, `Z_{G_n}(2,z) ≠ 0` whenever `dist(z, [x_*, 1]) ≤ ρ`. -/
theorem ising_af_zero_free {d : ℝ} (hd : 0 < d) {xs : ℝ} (hx0 : 0 < xs) (hx1 : xs < 1)
    (hdx : d * ((1 - xs) / (1 + xs)) ^ 2 < 1) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc xs 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G 2 z ≠ 0})
      atTop (𝓝 1) := by
  -- the parameter `s = (1-x_*)/(1+x_*) ∈ (0,1)`
  have h1x : 0 < 1 + xs := by linarith
  have hs0 : 0 < (1 - xs) / (1 + xs) := div_pos (by linarith) h1x
  have hs1 : (1 - xs) / (1 + xs) < 1 := by
    rw [div_lt_one h1x]
    linarith
  have hsq : (((2 : ℕ) : ℝ) - 1) * ((1 - xs) / (1 + xs)) ≤ 1 := by
    have : (((2 : ℕ) : ℝ) - 1) = 1 := by norm_num
    rw [this, one_mul]
    exact hs1.le
  obtain ⟨r, hr, B, hmom⟩ := ising_first_moment hd hs0.le hdx
  obtain ⟨ρz, hρz, hlim⟩ := prop_zero_free_moment (q := 2) le_rfl hd hs0 hs1 hsq hdx hr hmom
  refine ⟨ρz, hρz, ?_⟩
  -- `x_s = x_*`, so the interval `[x_s, 1]` is `[x_*, 1]`
  rw [IsingMain_xs_eq hx0] at hlim
  exact hlim

end

end ERZeroFreeness
