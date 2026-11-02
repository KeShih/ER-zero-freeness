/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs

/-!
# Normalization and the return to the `z`-plane

* `pottsZ_eq_zhat` is `eq:transformation`: per edge,
  `z^{[σ_u = σ_v]} = 1 + (z-1)[σ_u = σ_v] = b(z) (1 + t(z) A_{σ_u σ_v})`.
* `zplane_of_tplane` is the last paragraph of the proof of `prop:zero-free-moment`:
  `t(x) = (x-1)/(x+q-1)` maps `[x_s, 1]` onto `I_s = [-s,0]`, where
  `x_s = (1-(q-1)s)/(1+s)`, and `t(z) - t(x) = q(z-x)/((z+q-1)(x+q-1))`, so
  `|t(z) - t(x)| ≤ 2q|z-x|` once `|z - x| ≤ 1/2`; take `ρz = min (1/2) (ρ/(2q))`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Per-edge identity: `b(z) (1 + t(z) A_{σ e}) = z^{[σ_u = σ_v]}` for `e = uv`, when
`z + q - 1 ≠ 0`. -/
private lemma normalize_edge_factor {q : ℕ} (hq : 1 ≤ q) {z : ℂ} (hz : z + q - 1 ≠ 0)
    (σ : V → Fin q) (e : Sym2 V) :
    bFac q z * (1 + tOf q z * edgeA q σ e) = if (e.map σ).IsDiag then z else 1 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  unfold bFac tOf edgeA
  split_ifs
  · field_simp; ring
  · field_simp; ring

/-- Product of the per-edge identity over `E(G)`:
`b(z)^{|E|} ∏_e (1 + t(z) A_{σ e}) = z^{m_G(σ)}`. -/
private lemma normalize_prod_edge_factor {q : ℕ} (hq : 1 ≤ q) (G : SimpleGraph V) {z : ℂ}
    (hz : z + q - 1 ≠ 0) (σ : V → Fin q) :
    bFac q z ^ G.edgeFinset.card * ∏ e ∈ G.edgeFinset, (1 + tOf q z * edgeA q σ e) =
      z ^ monoCount G σ := by
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  simp_rw [normalize_edge_factor hq hz σ]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  rfl

/-- **`eq:transformation`.** `Z_G(q,z) = q^{|V|} b(z)^{|E|} Ẑ_G(t(z))` whenever `z + q - 1 ≠ 0`. -/
theorem pottsZ_eq_zhat {q : ℕ} (hq : 1 ≤ q) (G : SimpleGraph V) {z : ℂ} (hz : z + q - 1 ≠ 0) :
    pottsZ G q z =
      (q : ℂ) ^ Fintype.card V * bFac q z ^ G.edgeFinset.card * (zhat G q).eval (tOf q z) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqV : (q : ℂ) ^ Fintype.card V ≠ 0 := pow_ne_zero _ hq0
  rw [zhat_eval, mul_comm ((q : ℂ) ^ Fintype.card V), mul_assoc, ← mul_assoc ((q : ℂ) ^ _),
    mul_inv_cancel₀ hqV, one_mul, Finset.mul_sum]
  unfold pottsZ
  exact Finset.sum_congr rfl fun σ _ => (normalize_prod_edge_factor hq G hz σ).symm

/-- The Möbius difference identity `t(z) - t(w) = q (z - w) / ((z + q - 1)(w + q - 1))`. -/
private lemma normalize_tOf_sub {q : ℕ} {z w : ℂ} (hz : z + q - 1 ≠ 0) (hw : w + q - 1 ≠ 0) :
    tOf q z - tOf q w = q * (z - w) / ((z + q - 1) * (w + q - 1)) := by
  unfold tOf
  rw [div_sub_div _ _ hz hw]
  congr 1
  ring

/-- Zero-freeness of `Ẑ_G` on the tube `L_ρ(I_s)` gives zero-freeness of `Z_G(q,·)` on a
fixed neighbourhood of `[x_s, 1]`, `x_s = (1-(q-1)s)/(1+s)`, uniformly in the graph. -/
theorem zplane_of_tplane {q : ℕ} (hq : 2 ≤ q) {s ρ : ℝ} (hs : 0 ≤ s)
    (hsq : ((q : ℝ) - 1) * s ≤ 1) (hρ : 0 < ρ) :
    ∃ ρz > 0, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), (∀ t ∈ tube s ρ, (zhat G q).eval t ≠ 0) →
      ∀ z : ℂ, (∃ x : ℝ, x ∈ Set.Icc ((1 - ((q : ℝ) - 1) * s) / (1 + s)) 1 ∧ ‖z - x‖ ≤ ρz) →
        pottsZ G q z ≠ 0 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  refine ⟨min (1 / 2) (ρ / (2 * q)), lt_min (by norm_num) (by positivity), ?_⟩
  rintro n G hG z ⟨x, ⟨hx1, hx2⟩, hzx⟩
  have hzx2 : ‖z - x‖ ≤ ρ / (2 * q) := hzx.trans (min_le_right _ _)
  -- the left endpoint `x_s` is nonnegative (as `(q-1)s ≤ 1`), hence so is `x`
  have hs1 : (0 : ℝ) < 1 + s := by linarith
  have hx0 : 0 ≤ x :=
    (div_nonneg (by linarith) hs1.le : (0 : ℝ) ≤ (1 - ((q : ℝ) - 1) * s) / (1 + s)).trans hx1
  have hxq : (1 : ℝ) ≤ x + q - 1 := by linarith
  -- `‖x + q - 1‖ = x + q - 1 ≥ 1` and, since `‖z - x‖ ≤ 1/2`, `‖z + q - 1‖ ≥ 1/2`
  have hxnorm : ‖(x : ℂ) + q - 1‖ = x + q - 1 := by
    rw [show ((x : ℂ) + q - 1) = ((x + q - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hzq : (1 / 2 : ℝ) ≤ ‖z + q - 1‖ := by
    have h := norm_sub_norm_le ((x : ℂ) + q - 1) (z + q - 1)
    rw [show (x : ℂ) + q - 1 - (z + q - 1) = -(z - x) by ring, norm_neg, hxnorm] at h
    linarith [hzx.trans (min_le_left _ _)]
  have hz0 : z + q - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzq
    norm_num at hzq
  have hx0C : (x : ℂ) + q - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxnorm
    linarith
  -- `Z_G(q,z) = q^n b(z)^{|E|} Ẑ_G(t(z))` with `b(z) ≠ 0` and `t(z) ∈ L_ρ(I_s)` (centre `t(x)`)
  rw [pottsZ_eq_zhat (by omega) G hz0]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ hqC) (pow_ne_zero _ (div_ne_zero hz0 hqC)))
    (hG _ ⟨(x - 1) / (x + q - 1), ⟨?_, ?_⟩, ?_⟩)
  · -- `-s ≤ t(x)` because `x ≥ x_s`
    rw [le_div_iff₀ (by linarith)]
    have : 1 - ((q : ℝ) - 1) * s ≤ x * (1 + s) := by
      rwa [div_le_iff₀ hs1] at hx1
    linarith
  · -- `t(x) ≤ 0` because `x ≤ 1`
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  · -- `|t(z) - t(x)| = q|z - x| / (|z + q - 1| (x + q - 1)) ≤ 2q|z - x| ≤ ρ`
    have htx : (((x - 1) / (x + q - 1) : ℝ) : ℂ) = tOf q x := by
      unfold tOf; push_cast; rfl
    rw [htx, normalize_tOf_sub hz0 hx0C, norm_div, norm_mul, norm_mul, hxnorm,
      Complex.norm_natCast, div_le_iff₀ (by positivity)]
    have h1 : (q : ℝ) * ‖z - x‖ ≤ ρ / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q)] at hzx2
      linarith
    have h2 : 1 / 2 ≤ ‖z + q - 1‖ * (x + q - 1) :=
      hzq.trans (le_mul_of_one_le_right (norm_nonneg _) hxq)
    have h3 : ρ * (1 / 2) ≤ ρ * (‖z + q - 1‖ * (x + q - 1)) :=
      mul_le_mul_of_nonneg_left h2 hρ.le
    linarith

end

end ERZeroFreeness
