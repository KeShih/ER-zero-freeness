/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.VBModel
import ERZeroFreeness.IsingRademacher
import ERZeroFreeness.IsingRelation
import ERZeroFreeness.TwoReplica

/-!
# The second moment of the Viana–Bray polynomial (Step 3 of Section 7)

Let `(G_n, J)` follow the signed Erdős–Rényi model with `p = d/n`, and `I_n = 𝓘_{G_n,J}`.
Averaging each two-replica edge factor over its uniform sign removes the terms linear in `J_e`
(`vb_two_replica_identity`); with `1 + y ≤ e^y`, `∑_{u<v} η_uη_v ≤ S_η²/2` and
`eq:rademacher-moment` this gives the explicit bound
`E|I_n(t)|² ≤ (1 - d|t|²)^{-1/2}` for `n ≥ d` and `d|t|² < 1` (`vb_second_moment`).
`vb_first_moment` deduces a uniform first-moment bound on a closed disk `|t| ≤ R` with
`dR² < 1`, using `x ≤ 1/2 + x²/2` in place of Cauchy–Schwarz.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- The sign average for a fixed graph: `∑_J w(G,J) ∏_{e ∈ E(G)} f_e(J_e) =
w(G) ∏_{e ∈ E(G)} (f_e(true) + f_e(false))/2` (`sum_bool_prod` and `|E(G)| ≤ |Sym2|`). -/
private lemma VBSecondMoment_inner_sum {n : ℕ} {p : ℝ} (f : Sym2 (Fin n) → Bool → ℂ)
    (G : SimpleGraph (Fin n)) :
    ∑ J : Sym2 (Fin n) → Bool, ((sgWeight n p G J : ℝ) : ℂ) * ∏ e ∈ G.edgeFinset, f e (J e) =
      algebraMap ℝ ℂ (erWeight n p G) * ∏ e ∈ G.edgeFinset, ((f e true + f e false) / 2) := by
  simp only [sgWeight, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.coe_algebraMap]
  have hb : ∑ J : Sym2 (Fin n) → Bool, ∏ e ∈ G.edgeFinset, f e (J e) =
      2 ^ (Fintype.card (Sym2 (Fin n)) - G.edgeFinset.card) *
        ∏ e ∈ G.edgeFinset, (f e true + f e false) := by
    convert sum_bool_prod G.edgeFinset f
  rw [← Finset.mul_sum, hb, Finset.prod_div_distrib, Finset.prod_const]
  have hk : G.edgeFinset.card ≤ Fintype.card (Sym2 (Fin n)) := Finset.card_le_univ _
  have h2 : (2 : ℂ) ^ Fintype.card (Sym2 (Fin n)) =
      2 ^ (Fintype.card (Sym2 (Fin n)) - G.edgeFinset.card) * 2 ^ G.edgeFinset.card := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have h2ne : (2 : ℂ) ^ G.edgeFinset.card ≠ 0 := pow_ne_zero _ two_ne_zero
  have h2ne' : (2 : ℂ) ^ (Fintype.card (Sym2 (Fin n)) - G.edgeFinset.card) ≠ 0 :=
    pow_ne_zero _ two_ne_zero
  rw [h2]
  field_simp

/-- Edges and signs are independent: the signed analogue of `sum_erWeight_mul_prod`. -/
theorem sum_sgWeight_mul_prod {n : ℕ} {p : ℝ} (f : Sym2 (Fin n) → Bool → ℂ) :
    ∑ G : SimpleGraph (Fin n), ∑ J : Sym2 (Fin n) → Bool,
        ((sgWeight n p G J : ℝ) : ℂ) * ∏ e ∈ G.edgeFinset, f e (J e) =
      ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (((1 - p : ℝ) : ℂ) + (p : ℂ) * ((f e true + f e false) / 2)) := by
  rw [Finset.sum_congr rfl fun G _ => VBSecondMoment_inner_sum f G, sum_erWeight_mul_prod]
  simp only [Complex.coe_algebraMap]

/-- The two-replica edge factor `y_e(b) = (1 + t s_b A_e) conj(1 + t s_b B_e)` with
`s_b = boolSign b`. -/
private def VBSecondMoment_y {V : Type*} (t : ℂ) (σ τ : V → Fin 2) (e : Sym2 V) (b : Bool) : ℂ :=
  (1 + t * (((boolSign b : ℤ) : ℂ) * edgeA 2 σ e)) *
    (starRingEnd ℂ) (1 + t * (((boolSign b : ℤ) : ℂ) * edgeA 2 τ e))

/-- Averaging the two-replica edge factor over the sign kills the linear terms:
`(1-p) + p (y_e(true) + y_e(false))/2 = 1 + p|t|² A_e B_e`. -/
private lemma VBSecondMoment_edge {V : Type*} (p : ℝ) (t : ℂ) (σ τ : V → Fin 2) (e : Sym2 V) :
    ((1 - p : ℝ) : ℂ) + (p : ℂ) *
        ((VBSecondMoment_y t σ τ e true + VBSecondMoment_y t σ τ e false) / 2) =
      1 + (p : ℂ) * (((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e)) := by
  unfold VBSecondMoment_y
  rw [TwoReplicaAux.edgeA_eq_ofReal 2 σ e, TwoReplicaAux.edgeA_eq_ofReal 2 τ e]
  have h : t * (starRingEnd ℂ) t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [boolSign, if_true, Bool.false_eq_true, if_false, map_add, map_one, map_mul,
    map_neg, Complex.conj_ofReal, Int.cast_one, Int.cast_neg, Complex.ofReal_sub,
    Complex.ofReal_one]
  linear_combination (p : ℂ) * ((TwoReplicaAux.aRe 2 σ e : ℝ) : ℂ) *
    ((TwoReplicaAux.aRe 2 τ e : ℝ) : ℂ) * h

/-- Exchange of the `(G, J)` sums with the `(σ, τ)` sums. -/
private lemma VBSecondMoment_exchange {α β ι : Type*} (s : Finset α) (u : Finset β)
    (B : Finset ι) (w : α → β → ℂ) (c : ℂ) (X : α → β → ι → ι → ℂ) :
    ∑ a ∈ s, ∑ b ∈ u, w a b * (c * ∑ σ ∈ B, ∑ τ ∈ B, X a b σ τ) =
      c * ∑ σ ∈ B, ∑ τ ∈ B, ∑ a ∈ s, ∑ b ∈ u, w a b * X a b σ τ := by
  have h1 : ∀ a ∈ s, ∑ b ∈ u, w a b * (c * ∑ σ ∈ B, ∑ τ ∈ B, X a b σ τ) =
      c * ∑ σ ∈ B, ∑ τ ∈ B, ∑ b ∈ u, w a b * X a b σ τ := fun a _ =>
    TwoReplicaAux.sum_mul_mul_sum_sum u B (w a) c (X a)
  rw [Finset.sum_congr rfl h1]
  have h2 := TwoReplicaAux.sum_mul_mul_sum_sum s B (fun _ => (1 : ℂ)) c
    (fun a σ τ => ∑ b ∈ u, w a b * X a b σ τ)
  simp only [one_mul] at h2
  exact h2

/-- `|𝓘_{G,J}(t)|² = 4^{-n} ∑_{σ,τ} ∏_{e ∈ E(G)} y_e(J_e)` (as complex numbers). -/
private lemma VBSecondMoment_norm_sq (n : ℕ) (t : ℂ) (G : SimpleGraph (Fin n))
    (J : Sym2 (Fin n) → Bool) :
    (((‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖ ^ 2 : ℝ)) : ℂ) =
      ((2 : ℂ) ^ n)⁻¹ ^ 2 * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        ∏ e ∈ G.edgeFinset, VBSecondMoment_y t σ τ e (J e) := by
  set c : ℂ := ((2 : ℂ) ^ n)⁻¹ with hc
  have hcc : (starRingEnd ℂ) c = c := by rw [hc, map_inv₀, map_pow, map_ofNat]
  have he : (signedPoly G 2 (fun e => boolSign (J e))).eval t =
      c * ∑ σ : Fin n → Fin 2, ∏ e ∈ G.edgeFinset,
        (1 + t * (((boolSign (J e) : ℤ) : ℂ) * edgeA 2 σ e)) := by
    rw [signedPoly_eval, Fintype.card_fin, hc]
    norm_num
    exact Finset.sum_congr (Finset.ext fun _ => by simp) fun _ _ => rfl
  rw [he, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, TwoReplicaAux.mul_conj_sum_prod c hcc]
  rfl

/-- Sign averaging: `E|I_n(t)|² = E_{σ,τ} ∏_{u<v} (1 + p|t|² η_u η_v)` in the signed model with
edge probability `p`. -/
theorem vb_two_replica_identity (n : ℕ) (p : ℝ) (t : ℂ) :
    ((sgExp n p (fun G J => ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖ ^ 2) : ℝ) :
        ℂ) =
      ((4 : ℂ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + (p : ℂ) * (((‖t‖ ^ 2 : ℝ) : ℂ) * (edgeA 2 σ e * edgeA 2 τ e))) := by
  have h4 : ((2 : ℂ) ^ n)⁻¹ ^ 2 = ((4 : ℂ) ^ n)⁻¹ := by
    rw [inv_pow, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [sgExp, Complex.ofReal_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun J _ => by
    rw [VBSecondMoment_norm_sq n t G J]]
  rw [VBSecondMoment_exchange, h4]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [sum_sgWeight_mul_prod (fun e b => VBSecondMoment_y t σ τ e b)]
  exact Finset.prod_congr rfl fun e _ => VBSecondMoment_edge p t σ τ e

/-- `vb_two_replica_identity` in real form (`A_e = aRe 2 σ e` is real). -/
private lemma VBSecondMoment_real_form (n : ℕ) (p : ℝ) (t : ℂ) :
    sgExp n p (fun G J => ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖ ^ 2) =
      ((4 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + p * (‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e))) := by
  have h := vb_two_replica_identity n p t
  simp only [TwoReplicaAux.edgeA_eq_ofReal] at h
  apply Complex.ofReal_injective
  rw [h]
  push_cast
  rfl

/-- `|a_σ(e) a_τ(e)| ≤ 1` for `q = 2`. -/
private lemma VBSecondMoment_abs_aRe_mul_le {V : Type*} (σ τ : V → Fin 2) (e : Sym2 V) :
    |TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e| ≤ 1 := by
  rw [abs_mul]
  have h1 := TwoReplicaAux.abs_aRe_le (le_refl 2) σ e
  have h2 := TwoReplicaAux.abs_aRe_le (le_refl 2) τ e
  norm_num at h1 h2
  calc |TwoReplicaAux.aRe 2 σ e| * |TwoReplicaAux.aRe 2 τ e| ≤ 1 * 1 :=
        mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- `sum_top_edgeA_two_mul` in real form: `∑_{e ∈ E(K_n)} a_σ(e) a_τ(e) = (S_{σ+τ}² - n)/2`. -/
private lemma VBSecondMoment_sum_aRe_mul {n : ℕ} (σ τ : Fin n → Fin 2) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e =
      (isingMag (σ + τ) ^ 2 - n) / 2 := by
  have h := sum_top_edgeA_two_mul σ τ
  simp only [TwoReplicaAux.edgeA_eq_ofReal] at h
  exact_mod_cast h

/-- The pair bound of Step 3: `∏_{e ∈ E(K_n)} (1 + p|t|² a_σ(e) a_τ(e)) ≤ e^{d|t|² S_η²/(2n)}`
with `p = d/n` and `η = σ + τ`. -/
private lemma VBSecondMoment_prod_le {d : ℝ} (hd : 0 < d) {n : ℕ} (hn : d ≤ n) {t : ℂ}
    (ht : d * ‖t‖ ^ 2 < 1) (σ τ : Fin n → Fin 2) :
    ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (1 + d / n * (‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e))) ≤
      Real.exp (d * ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2 / (2 * n)) := by
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have hn1 : (1 : ℝ) ≤ n := by
    have : 0 < n := by exact_mod_cast hnpos
    exact_mod_cast this
  have hx : 0 ≤ d / n * ‖t‖ ^ 2 := by positivity
  have hx1 : d / n * ‖t‖ ^ 2 ≤ 1 := by
    calc d / n * ‖t‖ ^ 2 ≤ d * ‖t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (div_le_self hd.le hn1) (sq_nonneg _)
      _ ≤ 1 := ht.le
  calc ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (1 + d / n * (‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)))
      ≤ ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          Real.exp (d / n * ‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)) := by
        apply Finset.prod_le_prod
        · intro e _
          have habs := VBSecondMoment_abs_aRe_mul_le σ τ e
          have hneg := neg_abs_le (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)
          have hle : -(d / n * ‖t‖ ^ 2) ≤
              d / n * ‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e) := by
            nlinarith
          nlinarith
        · intro e _
          have := Real.add_one_le_exp
            (d / n * ‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e))
          have hr : d / n * (‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)) =
              d / n * ‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e) := by ring
          linarith
    _ = Real.exp (d / n * ‖t‖ ^ 2 * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ = Real.exp (d / n * ‖t‖ ^ 2 * ((isingMag (σ + τ) ^ 2 - n) / 2)) := by
        rw [VBSecondMoment_sum_aRe_mul]
    _ ≤ Real.exp (d * ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2 / (2 * n)) := by
        apply Real.exp_le_exp.mpr
        have h : d / n * ‖t‖ ^ 2 * ((isingMag (σ + τ) ^ 2 - n) / 2) =
            d * ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2 / (2 * n) - d * ‖t‖ ^ 2 / 2 := by
          field_simp
        rw [h]
        have : 0 ≤ d * ‖t‖ ^ 2 / 2 := by positivity
        linarith

/-- **The second-moment bound of Step 3** (Section 7): `E|I_n(t)|² ≤ (1 - d|t|²)^{-1/2}` for
`n ≥ d` and `d|t|² < 1`. -/
theorem vb_second_moment {d : ℝ} (hd : 0 < d) {n : ℕ} (hn : d ≤ n) {t : ℂ}
    (ht : d * ‖t‖ ^ 2 < 1) :
    sgExp n (d / n) (fun G J => ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖ ^ 2) ≤
      (Real.sqrt (1 - d * ‖t‖ ^ 2))⁻¹ := by
  have h0 : 0 ≤ d * ‖t‖ ^ 2 := by positivity
  have h8 := sum_sum_isingMag_add (n := n) (fun S => Real.exp (d * ‖t‖ ^ 2 * S ^ 2 / (2 * n)))
  rw [VBSecondMoment_real_form]
  calc ((4 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
        ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (1 + d / n * (‖t‖ ^ 2 * (TwoReplicaAux.aRe 2 σ e * TwoReplicaAux.aRe 2 τ e)))
      ≤ ((4 : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ τ : Fin n → Fin 2,
          Real.exp (d * ‖t‖ ^ 2 * isingMag (σ + τ) ^ 2 / (2 * n)) := by
        gcongr with σ _ τ _
        exact VBSecondMoment_prod_le hd hn ht σ τ
    _ = ((2 : ℝ) ^ n)⁻¹ * ∑ η : Fin n → Fin 2,
          Real.exp (d * ‖t‖ ^ 2 * isingMag η ^ 2 / (2 * n)) := by
        rw [h8, show (4 : ℝ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
        have h2 : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
        field_simp
    _ ≤ (Real.sqrt (1 - d * ‖t‖ ^ 2))⁻¹ := rademacher_moment h0 ht

/-- `x ≤ 1/2 + x²/2`, applied to `x = |z|`. -/
private lemma VBSecondMoment_le_half (x : ℝ) : x ≤ 1 / 2 + 1 / 2 * x ^ 2 := by
  nlinarith [sq_nonneg (x - 1)]

/-- Uniform first moment on a closed disk: if `dR² < 1`, then `E|I_n(t)|` is bounded uniformly
in `n ≥ d` and `|t| ≤ R`. -/
theorem vb_first_moment {d : ℝ} (hd : 0 < d) {R : ℝ} (hdR : d * R ^ 2 < 1) :
    ∃ B : ℝ, ∀ n : ℕ, d ≤ n → ∀ t : ℂ, ‖t‖ ≤ R →
      sgExp n (d / n) (fun G J => ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖) ≤ B := by
  refine ⟨1 / 2 + 1 / 2 * (Real.sqrt (1 - d * R ^ 2))⁻¹, fun n hn t ht => ?_⟩
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  have htR : d * ‖t‖ ^ 2 ≤ d * R ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg t) ht 2) hd.le
  have ht' : d * ‖t‖ ^ 2 < 1 := lt_of_le_of_lt htR hdR
  have h2 := vb_second_moment hd hn ht'
  have hsq : (Real.sqrt (1 - d * ‖t‖ ^ 2))⁻¹ ≤ (Real.sqrt (1 - d * R ^ 2))⁻¹ := by
    have hpos : 0 < Real.sqrt (1 - d * R ^ 2) := Real.sqrt_pos.mpr (by linarith)
    exact inv_anti₀ hpos (Real.sqrt_le_sqrt (by linarith))
  have hmono := sgExp_mono (n := n) hp0 hp1
    (f := fun G J => ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖)
    (g := fun G J => 1 / 2 + 1 / 2 * ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖ ^ 2)
    (fun G J => VBSecondMoment_le_half _)
  have hadd := sgExp_add (n := n) (p := d / n) (fun _ _ => (1 : ℝ) / 2)
    (fun G J => 1 / 2 * ‖(signedPoly G 2 (fun e => boolSign (J e))).eval t‖ ^ 2)
  rw [sgExp_const, sgExp_const_mul] at hadd
  rw [hadd] at hmono
  calc _ ≤ _ := hmono
    _ ≤ 1 / 2 + 1 / 2 * (Real.sqrt (1 - d * R ^ 2))⁻¹ := by linarith

end

end ERZeroFreeness
