/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSSplitAnchored
import ERZeroFreeness.RSAnchor
import ERZeroFreeness.RSLocal

/-!
# Appendix C: Poisson complex first-moment transfer (Lemma C.4, `lem:rs-transfer`)

* `rs_transfer` (**Lemma C.4**, `t`-plane form, from `rs_anchored`, `rs_anchor`, `rs_local_i`,
  `rs_local_ii` and `rs_exists_params`): fix `q ≥ 3`, `x_* ∈ [0,1)`, `d > 0` with
  `d t(x_*)² < 1` and `Δ ∈ (0,d)` such that `eq:rs-input` holds at `s = d + Δ` for every
  `x ∈ (0,1) ∩ [x_*,1)`.  Then every `τ ∈ I_{s_*} = [t(x_*), 0] = t([x_*,1])` has an open
  neighbourhood `O` in `ℂ` and `n₀`, `B` with
  `E_{𝖯_d}[e^{dm/n} |F_G(t)|] ≤ B` for all `n ≥ n₀` and `t ∈ O`  (**`eq:rs-moment`**).

**Deviations from the paper.**
* The paper states Lemma C.4 in the `z`-plane: neighbourhoods `O_y` of the points `y ∈ [x_*,1]`
  with `closure(O_y) ⊂ ℂ \ {-(q-1)}`, and `F_G(z)`.  Since `F_G(z) = F_G(t(z))` and `t` is a
  homeomorphism near `[x_*,1]` (with `t(y) = τ`), this is the same statement in the coordinate
  `t`; it removes the Möbius and compact-closure steps (the paper's `O_y` is the preimage under
  `t` of the set `O` constructed below).
* At `y = 0` the paper takes `O_0 = {|z| < x̂}`, using `|M_z| ≤ e^{2x̂} M_{x̂}` for `|z| ≤ x̂`.
  Here the set `O` built in the `t`-plane at the small anchor `x̂` is shown to contain
  `τ = t(0) = -1/(q-1)` directly (step 4 below).
* The hypothesis `eq:rs-input` is taken in the paper's form `= o(n)`; only its upper half is used.

## Proof

(Paper, `app:rs-split`, Step 2, with the case `y = 0` treated in `t`-coordinates.)
1. Parameters: `s_* = -t(x_*) ∈ (0, 1/(q-1)]`; `rs_exists_params` gives `t_* ∈ (s_*, 1)`,
   `η ∈ (0,1]` with `θ_* < 1`; put `p = 2/(1+θ_*)` (`1 < p`, `pθ_* < 1`).  `rs_local_i` gives `C₀`,
   `rs_local_ii` gives `C₁`, `rs_anchor` gives `c₁, c₂`.
2. For `τ ∈ [t(x_*), 0]` let `y = (1 + (q-1)τ)/(1 - τ) ∈ [x_*, 1]`, so `tRe q y = τ`.
3. If `y > 0`: apply `rs_anchor` at `y` (inputs: `hfe` via `Asymptotics.IsLittleO.bound` for
   `y < 1`; Lemma C.5(i) at `t = (tRe q y : ℂ)` with `rs_rsH_ofReal`; Lemma C.5(ii) at
   `t = tRe q y`), get `γ_y`, put `ζ = min(1/4, c₂γ_y²/(18dℓ²))`, and
   `O = {t : ‖t‖ < t_* ∧ Re t < t_*² ∧ ∀ a b, ‖M_t(a,b)‖ < e^ζ M_y(a,b)}`, which is open and
   contains `τ` (entries of `M_y` are `≥ y > 0`, `rs_rsM_mem`).  `rs_anchored` bounds
   `E[e^{dm/n}|F_t|]` on `O` for large `n`.
4. If `y = 0` (so `x_* = 0`, `τ = -1/(q-1)`): for anchors `x ≤ 1/2`, `γ_x ≥ c₁/ℓ²` gives
   `ζ_x ≥ c₃/ℓ⁶`, `c₃ = min(1/4, c₂c₁²/(18d))`; since `x log⁶(e/x) → 0` as `x ↓ 0`, fix
   `x̂ ∈ (0,1/2]` with `x̂/(q-1) < c₃/ℓ(x̂)⁶`.  The set `O` of step 3 built at the anchor `x̂`
   contains `τ = -1/(q-1)`: its diagonal entries are `0`, its off-diagonal entries `q/(q-1)`, and
   `q/(q-1) < e^{ζ_x̂} q/(x̂+q-1)` because `1 + x̂/(q-1) < 1 + ζ_x̂ ≤ e^{ζ_x̂}`.
-/

open Polynomial Filter Topology Asymptotics

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSSplitAux

/-- A small anchor: some `u ≥ log 2` has `e^{-u}(1+u)⁶ < c` (so `x̂ = e^{-u} ≤ 1/2` and
`x̂ log⁶(e/x̂) < c`). -/
theorem exists_small_anchor {c : ℝ} (hc : 0 < c) :
    ∃ u : ℝ, Real.log 2 ≤ u ∧ Real.exp (-u) * (1 + u) ^ 6 < c := by
  have hlim : Tendsto (fun u : ℝ => Real.exp (-u) * (1 + u) ^ 6) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 6).comp
      (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have h2 := h.const_mul (Real.exp 1)
    rw [mul_zero] at h2
    refine h2.congr fun u => ?_
    simp only [Function.comp, id]
    have e1 : Real.exp 1 * Real.exp (-1) = 1 := by rw [← Real.exp_add]; norm_num
    rw [show -(1 + u) = -1 + -u by ring, Real.exp_add]
    linear_combination ((1 + u) ^ 6 * Real.exp (-u)) * e1
  obtain ⟨u, hu⟩ := ((hlim.eventually (gt_mem_nhds hc)).and
    (eventually_ge_atTop (Real.log 2))).exists
  exact ⟨u, hu.2, hu.1⟩

/-- For real `τ`, the complex entry `M_τ(a,b)` is the cast of the real one. -/
theorem rsM_ofReal {q : ℕ} (τ : ℝ) (a b : Fin q) :
    rsM q (τ : ℂ) a b = ((rsM q τ a b : ℝ) : ℂ) := by
  unfold rsM; push_cast; ring

/-- The neighbourhoods `{t : ‖t‖ < t_*, Re t < t_*², |M_t| < e^ζ M_{t₀} entrywise}` are open. -/
theorem isOpen_nbhd (q : ℕ) (tstar ζ t₀ : ℝ) :
    IsOpen {t : ℂ | ‖t‖ < tstar ∧ t.re < tstar ^ 2 ∧
      ∀ a b : Fin q, ‖rsM q t a b‖ < Real.exp ζ * rsM q t₀ a b} := by
  have h1 : IsOpen {t : ℂ | ‖t‖ < tstar} := isOpen_lt continuous_norm continuous_const
  have h2 : IsOpen {t : ℂ | t.re < tstar ^ 2} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {t : ℂ | ∀ a b : Fin q, ‖rsM q t a b‖ < Real.exp ζ * rsM q t₀ a b} := by
    have e : {t : ℂ | ∀ a b : Fin q, ‖rsM q t a b‖ < Real.exp ζ * rsM q t₀ a b} =
        ⋂ a : Fin q, ⋂ b : Fin q, {t : ℂ | ‖rsM q t a b‖ < Real.exp ζ * rsM q t₀ a b} := by
      ext t; simp
    rw [e]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      isOpen_lt (by unfold rsM; fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

/-- At `t = -1/(q-1)` (`x = 0`) the entries of `M` are dominated by `(1 + x̂/(q-1)) M_{x̂}`. -/
theorem rsM_zero_le {q : ℕ} (hq : 3 ≤ q) {xh : ℝ} (hxh0 : 0 < xh) (a b : Fin q) :
    rsM q (-1 / ((q : ℝ) - 1)) a b ≤ (1 + xh / ((q : ℝ) - 1)) * rsM q (tRe q xh) a b ∧
      0 ≤ rsM q (-1 / ((q : ℝ) - 1)) a b := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have hd' : 0 < xh + q - 1 := by linarith
  unfold rsM rsA tRe
  split_ifs
  · push_cast
    have e0 : (1 : ℝ) + -1 / ((q : ℝ) - 1) * ((q : ℝ) - 1) = 0 := by field_simp; ring
    have e1 : (1 : ℝ) + (xh - 1) / (xh + q - 1) * ((q : ℝ) - 1) = xh * q / (xh + q - 1) := by
      field_simp; ring
    rw [e0, e1]
    have h1 : 0 ≤ xh / ((q : ℝ) - 1) := div_nonneg hxh0.le (by linarith)
    exact ⟨mul_nonneg (by linarith) (div_nonneg (by positivity) hd'.le), le_rfl⟩
  · push_cast
    have e0 : (1 : ℝ) + -1 / ((q : ℝ) - 1) * -1 = q / ((q : ℝ) - 1) := by field_simp; ring
    have e1 : (1 + xh / ((q : ℝ) - 1)) * (1 + (xh - 1) / (xh + q - 1) * -1) =
        q / ((q : ℝ) - 1) := by field_simp; ring
    rw [e0, e1]
    exact ⟨le_rfl, div_nonneg (by linarith) (by linarith)⟩

/-- `c₃/ℓ⁶ ≤ ζ = min(1/4, c₂γ²/(18dℓ²))` when `γ ≥ c₁/ℓ²` and `ℓ ≥ 1`. -/
theorem zeta_ge {c₁ c₂ d γ L : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hd : 0 < d) (hL : 1 ≤ L)
    (hγ : c₁ / L ^ 2 ≤ γ) :
    min (1 / 4) (c₂ * c₁ ^ 2 / (18 * d)) / L ^ 6 ≤
      min (1 / 4) (c₂ * γ ^ 2 / (18 * d * L ^ 2)) := by
  have hL0 : 0 < L := by linarith
  have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ hL
  refine le_min ?_ ?_
  · calc min (1 / 4) (c₂ * c₁ ^ 2 / (18 * d)) / L ^ 6 ≤ min (1 / 4) (c₂ * c₁ ^ 2 / (18 * d)) :=
          div_le_self (le_min (by norm_num) (by positivity)) hL6
      _ ≤ 1 / 4 := min_le_left _ _
  · have hγ2 : (c₁ / L ^ 2) ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ (by positivity) hγ 2
    calc min (1 / 4) (c₂ * c₁ ^ 2 / (18 * d)) / L ^ 6 ≤ c₂ * c₁ ^ 2 / (18 * d) / L ^ 6 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = c₂ * (c₁ / L ^ 2) ^ 2 / (18 * d * L ^ 2) := by field_simp
      _ ≤ c₂ * γ ^ 2 / (18 * d * L ^ 2) := by gcongr

end RSSplitAux

open RSSplitAux in
/-- **Lemma C.4 (`lem:rs-transfer`), `t`-plane form.** -/
theorem rs_transfer {q : ℕ} (hq : 3 ≤ q) {xs : ℝ} (hxs0 : 0 ≤ xs) (hxs1 : xs < 1) {d : ℝ}
    (hd : 0 < d) (hKS : d * tRe q xs ^ 2 < 1) {Δ : ℝ} (hΔ0 : 0 < Δ) (hΔd : Δ < d)
    (hfe : ∀ x : ℝ, 0 < x → x < 1 → xs ≤ x →
      (fun n : ℕ => rsExp n (d + Δ)
          (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)))
        =o[atTop] (fun n : ℕ => (n : ℝ))) :
    ∀ τ ∈ Set.Icc (tRe q xs) 0, ∃ O : Set ℂ, IsOpen O ∧ (τ : ℂ) ∈ O ∧ ∃ n₀ : ℕ, ∃ B : ℝ,
      ∀ n : ℕ, n₀ ≤ n → ∀ t ∈ O,
        rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) ≤ B := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : 2 ≤ q := by omega
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  -- the parameters of `eq:rs-parameters`
  have htxs0 : tRe q xs ≤ 0 := rs_tRe_nonpos hq2 hxs0 hxs1.le
  have htxs1 : -1 / ((q : ℝ) - 1) ≤ tRe q xs := rs_tRe_ge hq2 hxs0
  have hs₀0 : 0 ≤ -tRe q xs := by linarith
  have hs₀1 : -tRe q xs ≤ 1 / ((q : ℝ) - 1) := by
    have : -1 / ((q : ℝ) - 1) = -(1 / ((q : ℝ) - 1)) := by ring
    linarith
  have hds : d * (-tRe q xs) ^ 2 < 1 := by rw [neg_sq]; exact hKS
  obtain ⟨tstar, η, hst, -, -, hη0, -, hθ⟩ := rs_exists_params hq hd hs₀0 hs₀1 hds
  have hθ0 : 0 ≤ rsTheta q d tstar η := by unfold rsTheta; positivity
  set p : ℝ := 2 / (1 + rsTheta q d tstar η) with hp
  have hp1 : 1 < p := by
    rw [hp, lt_div_iff₀ (by linarith)]; linarith
  have hpθ : p * rsTheta q d tstar η < 1 := by
    rw [hp, div_mul_eq_mul_div, div_lt_one (by linarith)]; linarith
  -- Lemma C.5 and Lemma C.7
  obtain ⟨C₀, hC₀, hloc1⟩ := rs_local_i hq2 hd.le hη0 hθ
  obtain ⟨C₁, hC₁, hloc2⟩ := rs_local_ii hq2 hd.le hη0 hp1.le hpθ
  obtain ⟨c₁, hc₁, c₂, hc₂, hc₂1, hanc⟩ := rs_anchor hq hd hΔ0 hΔd hη0 hp1 hC₀ hC₁
  -- Step 1 at every real anchor `x ∈ (0,1] ∩ [x_*, 1]`
  have hanchor : ∀ x : ℝ, 0 < x → x ≤ 1 → xs ≤ x →
      ∃ γ > 0, γ ≤ 1 ∧ (x ≤ 1 / 2 → c₁ / rsEll x ^ 2 ≤ γ) ∧
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ t : ℂ, ‖t‖ ≤ tstar → t.re ≤ tstar ^ 2 →
          (∀ a b : Fin q, ‖rsM q t a b‖ ≤
            Real.exp (min (1 / 4) (c₂ * γ ^ 2 / (18 * d * rsEll x ^ 2))) *
              rsM q (tRe q x) a b) →
          rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) ≤
            Real.exp (d ^ 2) * Real.sqrt (2 * C₀ + 4) := by
    intro x hx0 hx1 hxsx
    have htx0 : tRe q x ≤ 0 := rs_tRe_nonpos hq2 hx0.le hx1
    have htxle : tRe q xs ≤ tRe q x := rs_tRe_mono hq2 hxs0 hxsx
    have htx : |tRe q x| ≤ tstar := by
      rw [abs_of_nonpos htx0]; linarith
    have hin1 : x < 1 → ∀ ε > 0, ∀ᶠ n : ℕ in atTop, rsExp n (d + Δ)
        (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)) ≤ ε * n := by
      intro hx1' ε hε
      filter_upwards [(hfe x hx0 hx1' hxsx).bound hε] with n hn
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast] at hn
      exact (le_abs_self _).trans hn
    have hin2 : ∀ n : ℕ, 0 < n → rsExp n d (rsHR q η (tRe q x)) ≤ C₀ := by
      intro n hn
      have h := (hloc1 n hn ((tRe q x : ℝ) : ℂ)
        (by rw [Complex.norm_real, Real.norm_eq_abs]; exact htx)
        (by rw [Complex.ofReal_re]; exact htx0.trans (sq_nonneg _))).2
      have heq : rsExp n d (rsH q η ((tRe q x : ℝ) : ℂ)) = rsExp n d (rsHR q η (tRe q x)) := by
        unfold rsExp poisPiExp
        exact tsum_congr fun N => by rw [rs_rsH_ofReal]
      rw [heq] at h
      exact (le_abs_self _).trans h
    obtain ⟨γ, hγ0, hγ1, hlow, hev⟩ := hanc x hx0 hx1 hin1 hin2
      (fun n hn E => (hloc2 n hn (tRe q x) (rs_tRe_ge hq2 hx0.le) htx0 htx E).2)
    exact ⟨γ, hγ0, hγ1, hlow, Filter.eventually_atTop.1
      (rs_anchored hq hd hC₁ hc₂ hc₂1 hγ0 hγ1 hx0 hx1 htx hloc1 hev)⟩
  -- the point `τ` and the anchor `y = t⁻¹(τ)`
  intro τ hτ
  have h1τ : 0 < 1 - τ := by linarith [hτ.2]
  set y : ℝ := (1 + ((q : ℝ) - 1) * τ) / (1 - τ) with hy
  have hty : tRe q y = τ := by
    have e1 : y - 1 = q * τ / (1 - τ) := by rw [hy]; field_simp; ring
    have e2 : y + q - 1 = q / (1 - τ) := by rw [hy]; field_simp; ring
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    unfold tRe
    rw [e1, e2, div_div_div_cancel_right₀ h1τ.ne', mul_div_cancel_left₀ _ hq0]
  have hden : 0 < xs + q - 1 := by linarith
  have hτl : (xs - 1) / (xs + q - 1) ≤ τ := hτ.1
  rw [div_le_iff₀ hden] at hτl
  have hxsy : xs ≤ y := by rw [hy, le_div_iff₀ h1τ]; nlinarith
  have hy1 : y ≤ 1 := by rw [hy, div_le_one h1τ]; nlinarith [hτ.2]
  have hy0 : 0 ≤ y := hxs0.trans hxsy
  have hτnorm : ‖((τ : ℝ) : ℂ)‖ < tstar := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hτ.2]; linarith [hτ.1]
  have hτre : ((τ : ℝ) : ℂ).re < tstar ^ 2 := by
    rw [Complex.ofReal_re]; nlinarith [hτ.2]
  rcases hy0.lt_or_eq with hypos | hyzero
  · -- a positive anchor `y` with `t(y) = τ`
    obtain ⟨γ, hγ0, hγ1, -, n₀, hbound⟩ := hanchor y hypos hy1 hxsy
    have hℓ : 0 < rsEll y := by
      unfold rsEll
      rw [Real.log_div (Real.exp_ne_zero 1) hypos.ne', Real.log_exp]
      linarith [Real.log_nonpos hypos.le hy1]
    set ζ := min (1 / 4) (c₂ * γ ^ 2 / (18 * d * rsEll y ^ 2)) with hζdef
    have hζ : 0 < ζ := lt_min (by norm_num) (by positivity)
    refine ⟨_, isOpen_nbhd q tstar ζ (tRe q y), ⟨hτnorm, hτre, fun a b => ?_⟩, n₀, _,
      fun n hn t ht => hbound n hn t ht.1.le ht.2.1.le (fun a b => (ht.2.2 a b).le)⟩
    have hM := rs_rsM_mem hq hy0 hy1 a b
    rw [rsM_ofReal, Complex.norm_real, Real.norm_eq_abs, ← hty,
      abs_of_nonneg (by linarith [hM.1])]
    have hpos : 0 < rsM q (tRe q y) a b := by linarith [hM.1]
    have he : 1 < Real.exp ζ := Real.one_lt_exp_iff.2 hζ
    nlinarith
  · -- `y = 0`: then `x_* = 0` and `τ = -1/(q-1)`; use a small positive anchor `x̂`
    have hxs : xs = 0 := le_antisymm (hxsy.trans hyzero.symm.le) hxs0
    have hτ0 : τ = -1 / ((q : ℝ) - 1) := by
      have : tRe q 0 = τ := by rw [← hyzero] at hty; exact hty
      rw [← this]; unfold tRe; ring
    set c₃ : ℝ := min (1 / 4) (c₂ * c₁ ^ 2 / (18 * d)) with hc₃
    have hc₃0 : 0 < c₃ := lt_min (by norm_num) (by positivity)
    obtain ⟨u, hu1, hu2⟩ := exists_small_anchor (mul_pos hc₃0 hq1)
    have hu0 : 0 ≤ u := le_trans (Real.log_nonneg (by norm_num)) hu1
    have hxh0 : 0 < Real.exp (-u) := Real.exp_pos _
    have hxh2 : Real.exp (-u) ≤ 1 / 2 := by
      rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
      exact Real.exp_le_exp.2 (by linarith)
    have hxh1 : Real.exp (-u) ≤ 1 := by linarith
    have hell : rsEll (Real.exp (-u)) = 1 + u := by
      unfold rsEll
      rw [Real.log_div (Real.exp_ne_zero 1) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
      ring
    obtain ⟨γ, hγ0, hγ1, hlow, n₀, hbound⟩ :=
      hanchor (Real.exp (-u)) hxh0 hxh1 (by rw [hxs]; exact hxh0.le)
    have hγl : c₁ / (1 + u) ^ 2 ≤ γ := by rw [← hell]; exact hlow hxh2
    set ζ := min (1 / 4) (c₂ * γ ^ 2 / (18 * d * rsEll (Real.exp (-u)) ^ 2)) with hζdef
    have hL1 : 1 ≤ 1 + u := by linarith
    -- `x̂/(q-1) < c₃/ℓ⁶ ≤ ζ`
    have hζbig : Real.exp (-u) / ((q : ℝ) - 1) < ζ := by
      have h1 : Real.exp (-u) / ((q : ℝ) - 1) < c₃ / (1 + u) ^ 6 := by
        rw [div_lt_div_iff₀ hq1 (by positivity)]
        linarith
      refine h1.trans_le ?_
      rw [hζdef, hell]
      exact zeta_ge hc₁ hc₂ hd hL1 hγl
    have hζ0 : 0 < ζ := lt_of_le_of_lt (by positivity) hζbig
    refine ⟨_, isOpen_nbhd q tstar ζ (tRe q (Real.exp (-u))), ⟨hτnorm, hτre, fun a b => ?_⟩,
      n₀, _, fun n hn t ht => hbound n hn t ht.1.le ht.2.1.le (fun a b => (ht.2.2 a b).le)⟩
    have hM := rs_rsM_mem hq hxh0.le hxh1 a b
    have hpos : 0 < rsM q (tRe q (Real.exp (-u))) a b := by linarith [hM.1]
    have hcmp := rsM_zero_le hq hxh0 a b
    rw [← hτ0] at hcmp
    rw [rsM_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcmp.2]
    have he : 1 + Real.exp (-u) / ((q : ℝ) - 1) < Real.exp ζ := by
      have := Real.add_one_lt_exp hζ0.ne'
      linarith
    calc rsM q τ a b ≤ (1 + Real.exp (-u) / ((q : ℝ) - 1)) * rsM q (tRe q (Real.exp (-u))) a b :=
          hcmp.1
      _ < Real.exp ζ * rsM q (tRe q (Real.exp (-u))) a b := by gcongr
end

end ERZeroFreeness
