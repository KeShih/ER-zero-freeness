/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSSplit
import ERZeroFreeness.RSFreeEnergy
import ERZeroFreeness.RSBetheMono
import ERZeroFreeness.RSCompare
import ERZeroFreeness.Main

/-!
# Appendix C: Proposition C.2 and Theorem C.1 (zero-freeness up to condensation)

* `rs_exists_tube_bound` (compactness): local uniform bounds near every point of `[a, 0]` give a
  uniform bound on a tube `L_r([a,0])`;
* `rs_first_moment_tube` (**Proposition C.2**, `prop:rs-first-moment`, in the form consumed by
  `prop_zero_free_moment`): for `q ≥ 3`, `x_* ∈ [0,1)` and `0 < d < d_cond(q,x_*)`,
  `d t(x_*)² < 1` and `sup_{n ≥ d} sup_{t ∈ L_r(I_{s_*})} E |Ẑ_{G_n}(t)| < ∞` for some `r > 0`,
  where `I_{s_*} = [t(x_*), 0] = t([x_*,1])`;
* `rs_first_moment_zplane` (**Proposition C.2**, the paper's `z`-plane form `eq:rs-gn-moment`):
  an open neighbourhood `W ⊂ ℂ \ {-(q-1)}` of `[x_*,1]` with
  `sup_{n ≥ d} sup_{z ∈ W} E|Ẑ(t(z))| < ∞`;
* `potts_zero_free_condensation` (**Theorem C.1**, `thm:rs-extension`, zero-freeness part): with
  probability tending to one, `Z_{G_n}(q,z) ≠ 0` whenever `dist(z, [x_*,1]) ≤ ρ`.

The last three take the explicit hypothesis `CKPZProp36 q` (the planted free-energy bound
[CKPZ, Prop. 3.6], see `RSDefs`), which is used only through `rs_free_energy` (`eq:rs-input`).
The CK* modules prove this hypothesis (`ckpz_prop36`), and `AppendixC` states the three results
without it.

**Deviations from the paper.**
* "`sup_n`" in Proposition C.2 is read as `sup_{n ≥ d}` (for `n < d` the edge probability `d/n`
  exceeds `1`; the same convention as `prop_zero_free_moment`).
* The paper's conditioning of `𝖯_d` on simplicity is replaced by `rs_erExp_le_rsExp`
  (constant `e^{d/2}` instead of `e^{d/2 + d²/4}`), and the finitely many `n` below the threshold of
  Lemma C.4 are handled by the crude bound `rs_erExp_le_pow` instead of compactness of `closure W`.
* Lemma C.4 and the compactness argument are carried out in the `t`-plane; the `z`-plane form
  follows by taking `W = t⁻¹(⋃_{x ∈ I_{s_*}} B(x, r)) \ {-(q-1)}`.
* The counting part of Theorem C.1 (the FPTAS) is not formalized.

## Proof

Proposition C.2 (paper's proof from Lemmas C.3 and C.4): `d < d_cond(q,x_*) ≤ t(x_*)^{-2}`
(`rs_dCond_le_inv_sq`) gives `d t(x_*)² < 1`.  Put `Δ = min(d, d_cond(q,x_*) - d)/2`; by
monotonicity (`rs_dCond_mono`) `d + Δ < d_cond(q,x)` for all `x ∈ [x_*,1)`, so `rs_free_energy`
gives `eq:rs-input` at `s = d + Δ`.  `rs_transfer` gives local bounds, `rs_exists_tube_bound` a
tube bound for `n ≥ n₁`, `rs_erExp_le_rsExp` transfers it to `G(n,d/n)`, and `rs_erExp_le_pow`
covers `d ≤ n < n₁`.  Theorem C.1: `prop_zero_free_moment` with
`s = -t(x_*) = (1-x_*)/(x_*+q-1)`, for which `0 < s < 1`, `(q-1)s ≤ 1` and
`x_s = (1-(q-1)s)/(1+s) = x_*`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- Compactness: local uniform bounds near every point of `[a, 0]` give a uniform bound on the
closed tube `L_r([a,0]) = tube (-a) r` for some `r > 0`. -/
theorem rs_exists_tube_bound {a : ℝ} (f : ℕ → ℂ → ℝ)
    (hloc : ∀ τ ∈ Set.Icc a 0, ∃ O : Set ℂ, IsOpen O ∧ (τ : ℂ) ∈ O ∧ ∃ n₀ : ℕ, ∃ B : ℝ,
      ∀ n : ℕ, n₀ ≤ n → ∀ t ∈ O, f n t ≤ B) :
    ∃ r > 0, ∃ n₀ : ℕ, ∃ B : ℝ, ∀ n : ℕ, n₀ ≤ n → ∀ t ∈ tube (-a) r, f n t ≤ B := by
  choose! O hOo hτO n₀ B hB using hloc
  set K : Set ℂ := (fun x : ℝ => (x : ℂ)) '' Set.Icc a 0 with hKdef
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun τ : Set.Icc a 0 => O τ.1)
    (fun τ : Set.Icc a 0 => hOo τ.1 τ.2)
    (by rintro _ ⟨τ, hτ, rfl⟩; exact Set.mem_iUnion.2 ⟨⟨τ, hτ⟩, hτO τ hτ⟩)
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open
    (isOpen_biUnion fun (τ : Set.Icc a 0) _ => hOo τ.1 τ.2) hF
  refine ⟨r, hr, F.sup fun τ => n₀ τ.1, ∑ τ ∈ F, |B τ.1|, fun n hn t ht => ?_⟩
  obtain ⟨x, hx, hxt⟩ := ht
  rw [neg_neg] at hx
  have htK : t ∈ Metric.cthickening r K :=
    Metric.mem_cthickening_of_dist_le t x r K ⟨x, hx, rfl⟩ (by rwa [Complex.dist_eq])
  obtain ⟨τ, hτF, htO⟩ := Set.mem_iUnion₂.1 (hrU htK)
  calc f n t ≤ B τ.1 :=
        hB τ.1 τ.2 n ((Finset.le_sup (f := fun τ : Set.Icc a 0 => n₀ τ.1) hτF).trans hn) t htO
    _ ≤ |B τ.1| := le_abs_self _
    _ ≤ ∑ τ ∈ F, |B τ.1| :=
        Finset.single_le_sum (f := fun i : Set.Icc a 0 => |B i.1|) (fun i _ => abs_nonneg _) hτF

/-- For real `x`, the complex `t(x)` is the cast of the real `t(x)`. -/
theorem rs_tOf_ofReal (q : ℕ) (x : ℝ) : tOf q (x : ℂ) = ((tRe q x : ℝ) : ℂ) := by
  unfold tOf tRe; push_cast; ring

/-- `s = -t(x_*)` satisfies the hypotheses of `prop_zero_free_moment`, with `x_s = x_*`. -/
theorem rs_tRe_neg_facts {q : ℕ} (hq : 3 ≤ q) {xs : ℝ} (hxs0 : 0 ≤ xs) (hxs1 : xs < 1) :
    0 < -tRe q xs ∧ -tRe q xs < 1 ∧ ((q : ℝ) - 1) * (-tRe q xs) ≤ 1 ∧
      (1 - ((q : ℝ) - 1) * (-tRe q xs)) / (1 + (-tRe q xs)) = xs := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : 0 < xs + q - 1 := by linarith
  have ht : -tRe q xs = (1 - xs) / (xs + q - 1) := by
    unfold tRe; rw [← neg_div]; congr 1; ring
  rw [ht]
  refine ⟨div_pos (by linarith) hden, (div_lt_one hden).2 (by linarith), ?_, ?_⟩
  · rw [mul_div_assoc', div_le_one hden]; nlinarith
  · have h1 : 1 - ((q : ℝ) - 1) * ((1 - xs) / (xs + q - 1)) = q * xs / (xs + q - 1) := by
      field_simp; ring
    have h2 : 1 + (1 - xs) / (xs + q - 1) = q / (xs + q - 1) := by
      field_simp; ring
    have hq0 : (q : ℝ) ≠ 0 := by positivity
    rw [h1, h2, div_div_div_cancel_right₀ hden.ne', mul_div_cancel_left₀ _ hq0]

/-- **Proposition C.2 (`prop:rs-first-moment`), `t`-plane form.** For `q ≥ 3`, `x_* ∈ [0,1)` and
`0 < d < d_cond(q,x_*)`: `d t(x_*)² < 1`, and for some `r > 0` the first moment
`E_{G(n,d/n)} |Ẑ_G(t)|` is bounded uniformly in `n ≥ d` and `t ∈ L_r(I_{s_*})`,
`I_{s_*} = [t(x_*), 0]` (exactly the hypothesis `hmom` of `prop_zero_free_moment`). -/
theorem rs_first_moment_tube {q : ℕ} (hq : 3 ≤ q) (hCKPZ : CKPZProp36 q) {xs : ℝ}
    (hxs0 : 0 ≤ xs) (hxs1 : xs < 1) {d : ℝ} (hd : 0 < d) (hdc : d < dCond q xs) :
    d * tRe q xs ^ 2 < 1 ∧ ∃ r > 0, ∃ B : ℝ, ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube (-tRe q xs) r, erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ B := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  -- Kesten–Stigum: `d t(x_*)² < 1`
  have htne : tRe q xs ≠ 0 := (rs_tRe_neg (by omega) hxs0 hxs1).ne
  have ht2 : 0 < tRe q xs ^ 2 := by positivity
  have hKS : d * tRe q xs ^ 2 < 1 := by
    have h2 : d < (tRe q xs ^ 2)⁻¹ := hdc.trans_le (rs_dCond_le_inv_sq hq hxs0 hxs1)
    calc d * tRe q xs ^ 2 < (tRe q xs ^ 2)⁻¹ * tRe q xs ^ 2 := by gcongr
      _ = 1 := inv_mul_cancel₀ ht2.ne'
  refine ⟨hKS, ?_⟩
  -- the gap `Δ`
  obtain ⟨Δ, hΔ0, hΔd, hΔc⟩ : ∃ Δ : ℝ, 0 < Δ ∧ Δ < d ∧ d + Δ < dCond q xs :=
    ⟨min d (dCond q xs - d) / 2, half_pos (lt_min hd (sub_pos.2 hdc)),
      by linarith [min_le_left d (dCond q xs - d)],
      by linarith [min_le_right d (dCond q xs - d)]⟩
  have hfe : ∀ x : ℝ, 0 < x → x < 1 → xs ≤ x →
      (fun n : ℕ => rsExp n (d + Δ)
          (fun N => rsF q (tRe q x) N * Real.log (rsF q (tRe q x) N)))
        =o[atTop] (fun n : ℕ => (n : ℝ)) := fun x hx0 hx1 hxsx =>
    rs_free_energy hq hCKPZ hx0 hx1 (by linarith) (hΔc.trans_le (rs_dCond_mono hq hxs0 hxsx hx1))
  -- local bounds (Lemma C.4) and compactness
  obtain ⟨r, hr, n₁, B₁, hB₁⟩ := rs_exists_tube_bound
    (fun n t => rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖))
    (rs_transfer hq hxs0 hxs1 hd hKS hΔ0 hΔd hfe)
  have hs0 : 0 ≤ -tRe q xs := neg_nonneg.2 (rs_tRe_nonpos (by omega) hxs0 hxs1.le)
  set K : ℝ := 1 + ((q : ℝ) - 1) * (-tRe q xs + r) with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ ((q : ℝ) - 1) * (-tRe q xs + r) := mul_nonneg (by linarith) (by linarith)
    linarith
  refine ⟨r, hr, max (Real.exp (d / 2) * B₁) (K ^ (n₁.choose 2)), fun n hn t ht => ?_⟩
  by_cases hn1 : n₁ ≤ n
  · calc erExp n (d / n) (fun G => ‖(zhat G q).eval t‖)
        ≤ Real.exp (d / 2) *
            rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) :=
          rs_erExp_le_rsExp (by omega) hd hn t
      _ ≤ Real.exp (d / 2) * B₁ := by gcongr; exact hB₁ n hn1 t ht
      _ ≤ _ := le_max_left _ _
  · rw [not_le] at hn1
    obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
    have htT : ‖t‖ ≤ -tRe q xs + r := (SecondMomentAux.tube_bounds ht).1
    calc erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤ K ^ (n.choose 2) :=
          rs_erExp_le_pow (by omega) hp0 hp1 htT
      _ ≤ K ^ (n₁.choose 2) := pow_le_pow_right₀ hK1 (Nat.choose_le_choose 2 hn1.le)
      _ ≤ _ := le_max_right _ _

/-- **Proposition C.2 (`prop:rs-first-moment`), the paper's `z`-plane form `eq:rs-gn-moment`.**
`d t(x_*)² < 1`, and there is an open neighbourhood `W ⊂ ℂ \ {-(q-1)}` of `[x_*,1]` with
`sup_{n ≥ d} sup_{z ∈ W} E_{G(n,d/n)} |Ẑ_G(t(z))| < ∞`. -/
theorem rs_first_moment_zplane {q : ℕ} (hq : 3 ≤ q) (hCKPZ : CKPZProp36 q) {xs : ℝ}
    (hxs0 : 0 ≤ xs) (hxs1 : xs < 1) {d : ℝ} (hd : 0 < d) (hdc : d < dCond q xs) :
    d * tRe q xs ^ 2 < 1 ∧
      ∃ W : Set ℂ, IsOpen W ∧ (∀ x ∈ Set.Icc xs 1, (x : ℂ) ∈ W) ∧
        (∀ z ∈ W, z + q - 1 ≠ 0) ∧
        ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ z ∈ W,
          erExp n (d / n) (fun G => ‖(zhat G q).eval (tOf q z)‖) ≤ B := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hKS, r, hr, B, hmom⟩ := rs_first_moment_tube hq hCKPZ hxs0 hxs1 hd hdc
  set U : Set ℂ := ⋃ x ∈ Set.Icc (tRe q xs) 0, Metric.ball ((x : ℝ) : ℂ) r with hU
  refine ⟨hKS, {z | z + q - 1 ≠ 0} ∩ tOf q ⁻¹' U, ?_, ?_, fun z hz => hz.1, B, ?_⟩
  · have hV : IsOpen {z : ℂ | z + q - 1 ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    have hc : ContinuousOn (tOf q) {z : ℂ | z + q - 1 ≠ 0} := by
      unfold tOf
      exact ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => hz
    exact hc.isOpen_inter_preimage hV (isOpen_biUnion fun x _ => Metric.isOpen_ball)
  · intro x hx
    refine ⟨?_, ?_⟩
    · show (x : ℂ) + q - 1 ≠ 0
      have : ((x + q - 1 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (show x + q - 1 ≠ 0 by linarith [hx.1])
      push_cast at this
      exact this
    · show tOf q x ∈ U
      rw [rs_tOf_ofReal]
      exact Set.mem_biUnion (x := tRe q x)
        ⟨rs_tRe_mono (by omega) hxs0 hx.1, rs_tRe_nonpos (by omega) (hxs0.trans hx.1) hx.2⟩
        (Metric.mem_ball_self hr)
  · rintro n hn z ⟨-, hz⟩
    obtain ⟨x, hx, hxz⟩ := Set.mem_iUnion₂.1 hz
    refine hmom n hn (tOf q z) ⟨x, by rwa [neg_neg], ?_⟩
    rw [Metric.mem_ball, Complex.dist_eq] at hxz
    exact hxz.le

/-- **Theorem C.1 (`thm:rs-extension`), zero-freeness part.** Fix an integer `q ≥ 3`,
`x_* ∈ [0,1)` and `0 < d < d_cond(q,x_*)`, and assume [CKPZ, Prop. 3.6] (`CKPZProp36 q`).  There
is `ρ > 0` such that, with probability tending to one over `G_n ∼ G(n,d/n)`, `Z_{G_n}(q,z) ≠ 0`
whenever `dist(z,[x_*,1]) ≤ ρ`. -/
theorem potts_zero_free_condensation {q : ℕ} (hq : 3 ≤ q) (hCKPZ : CKPZProp36 q) {xs : ℝ}
    (hx0 : 0 ≤ xs) (hx1 : xs < 1) {d : ℝ} (hd : 0 < d) (hdc : d < dCond q xs) :
    ∃ ρ > 0, Tendsto (fun n : ℕ => erProb n (d / n)
        {G | ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc xs 1 ∧ ‖z - x‖ ≤ ρ) → pottsZ G q z ≠ 0})
      atTop (𝓝 1) := by
  obtain ⟨-, r, hr, B, hmom⟩ := rs_first_moment_tube hq hCKPZ hx0 hx1 hd hdc
  obtain ⟨hs0, hs1, hsq, hxs⟩ := rs_tRe_neg_facts hq hx0 hx1
  have hds : d * (-tRe q xs) ^ 2 < 1 := by
    rw [neg_sq]
    exact (rs_first_moment_tube hq hCKPZ hx0 hx1 hd hdc).1
  obtain ⟨ρz, hρz, hlim⟩ :=
    prop_zero_free_moment (by omega : 2 ≤ q) hd hs0 hs1 hsq hds hr hmom
  rw [hxs] at hlim
  exact ⟨ρz, hρz, hlim⟩

end

end ERZeroFreeness
