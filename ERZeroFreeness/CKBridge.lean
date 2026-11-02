/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Lemmas 3.1–3.3 (the bridge from the literal to the planted form)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`.

`CKPZProp36 q` bounds the literal average `f^lit_n = ∑_m Pois(sn/2)(m) c̄_m(n)` (`rsCbar`).  The
rest of the proof bounds the planted average `f̄_n = q^{-n} ∑_σ E log F_G` (`rsFbar`), in which,
given `σ`, the edge counts `G_{vw}` are independent `Pois(s M(σ_v, σ_w)/(2n))`.  This file
compares the two.  Notation: `Z₁(σ) = n² φ(σ) = ∑_{(v,w)} M(σ_v, σ_w)` (`ckZ1`), the single-edge
law `p_σ(v, w) = M(σ_v, σ_w)/Z₁(σ)`, `g(σ, m) = E_{e ∼ p_σ^{⊗m}} log F_e` (`ckg`), the tilted
colouring law `ν_m(σ) = Z₁(σ)^m / ∑_{σ'} Z₁(σ')^m`, and `λ_σ`, the colour-proportion vector.

* Lemma 3.1 (two representations): `|log F_e| ≤ m ℓ₀` (`ck_abs_log_seqF_le`) and
  `|g(σ, m)| ≤ m ℓ₀` (`ck_abs_g_le`); `c̄_m = ∑_σ ν_m(σ) g(σ, m)` (`ck_cbar_eq`);
  `f̄_n = q^{-n} ∑_σ ∑_m Pois(s Z₁(σ)/(2n))(m) g(σ, m)` (`ck_fbar_eq`); and
  `ν_m(σ) ≤ q^{-n} (1 - 1/n)^{-m}` for `n ≥ 2` (`ck_nu_le`).
* Lemma 3.2 (regularity of `g`): `|g(σ, m+1) - g(σ, m)| ≤ ℓ₀` (`ck_g_succ`) and
  `|g(σ, m) - g(σ', m)| ≤ L m ‖λ_σ - λ_{σ'}‖₁` (`ck_g_lip`).
* Lemma 3.3 (bridge, `ck_bridge`): for `n ≥ 2` the series `f^lit_n` converges and
  `|f^lit_n - f̄_n| ≤ C √n`, with `C` independent of `n`.

## Route

Lemma 3.1(c) combines the pointwise one-tilt `𝖯_s(N) w_N(σ) = e^{κ(σ)} 𝖯^σ_s(N)`, where
`κ(σ) = (s/(2n))(Z₁(σ) - n²)`, with Poisson splitting (`rs_poisson_split`); Lemma 3.1(d) is
Jensen's inequality for `y ↦ y^m`.  The proofs of Lemmas 3.2 and 3.3 are outlined in the section
on them below.  They deviate from `docs/ckpz-proof.md` in two places: a hybrid argument, which
changes the law of one edge at a time, replaces the maximal coupling of Lemma 3.2(c); and
Lemma 3.3 compares both averages with the reference value `q^{-n} ∑_σ g(σ, ⌊sn/2⌋)` instead of
`g(σ₀, ⌊sn/2⌋)` at a balanced colouring `σ₀`.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### Lemma 3.1: two representations -/

/-- `0 < q` from `CKPar`. -/
private lemma CKBridgeA_q_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) : (0 : ℝ) < q := by
  have := hp.two_le
  exact_mod_cast (show 0 < q by omega)

/-- `∑_σ c = q^n c`. -/
private lemma CKBridgeA_sum_const {q n : ℕ} (c : ℝ) :
    ∑ _σ : Fin n → Fin q, c = (q : ℝ) ^ n * c := by
  simp [Finset.sum_const, Finset.card_univ]

/-- Each edge weight lies in `[m₋^m, m₊^m]`. -/
private lemma CKBridgeA_prod_mem {q n m : ℕ} {t : ℝ} (hp : CKPar q t) (σ : Fin n → Fin q)
    (e : Fin m → Fin n × Fin n) :
    ckMm q t ^ m ≤ ∏ j, rsM q t (σ (e j).1) (σ (e j).2) ∧
      ∏ j, rsM q t (σ (e j).1) (σ (e j).2) ≤ ckMp t ^ m := by
  have hb := ck_const_bounds hp
  constructor
  · calc ckMm q t ^ m = ∏ _j : Fin m, ckMm q t := by simp
      _ ≤ ∏ j, rsM q t (σ (e j).1) (σ (e j).2) :=
        Finset.prod_le_prod (fun j _ => hb.1.le) (fun j _ => (ck_rsM_mem hp _ _).1)
  · calc ∏ j, rsM q t (σ (e j).1) (σ (e j).2) ≤ ∏ _j : Fin m, ckMp t :=
        Finset.prod_le_prod (fun j _ => hb.1.le.trans (ck_rsM_mem hp _ _).1)
          (fun j _ => (ck_rsM_mem hp _ _).2)
      _ = ckMp t ^ m := by simp

/-- The edge weights are nonnegative. -/
private lemma CKBridgeA_prod_nonneg {q n m : ℕ} {t : ℝ} (hp : CKPar q t) (σ : Fin n → Fin q)
    (e : Fin m → Fin n × Fin n) : 0 ≤ ∏ j, rsM q t (σ (e j).1) (σ (e j).2) :=
  (pow_pos (ck_const_bounds hp).1 m).le.trans (CKBridgeA_prod_mem hp σ e).1

/-- `F_e ∈ [m₋^m, m₊^m]`. -/
private lemma CKBridgeA_seqF_mem {q n m : ℕ} {t : ℝ} (hp : CKPar q t)
    (e : Fin m → Fin n × Fin n) :
    ckMm q t ^ m ≤ rsSeqF q t e ∧ rsSeqF q t e ≤ ckMp t ^ m := by
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := pow_pos (CKBridgeA_q_pos hp) n
  unfold rsSeqF
  constructor
  · have h : ∑ _σ : Fin n → Fin q, ckMm q t ^ m ≤
        ∑ σ : Fin n → Fin q, ∏ j, rsM q t (σ (e j).1) (σ (e j).2) :=
      Finset.sum_le_sum fun σ _ => (CKBridgeA_prod_mem hp σ e).1
    rw [CKBridgeA_sum_const] at h
    rw [le_inv_mul_iff₀ hQ]
    exact h
  · have h : ∑ σ : Fin n → Fin q, ∏ j, rsM q t (σ (e j).1) (σ (e j).2) ≤
        ∑ _σ : Fin n → Fin q, ckMp t ^ m :=
      Finset.sum_le_sum fun σ _ => (CKBridgeA_prod_mem hp σ e).2
    rw [CKBridgeA_sum_const] at h
    rw [inv_mul_le_iff₀ hQ]
    exact h

/-- `F_e > 0`. -/
private lemma CKBridgeA_seqF_pos {q n m : ℕ} {t : ℝ} (hp : CKPar q t)
    (e : Fin m → Fin n × Fin n) : 0 < rsSeqF q t e :=
  (pow_pos (ck_const_bounds hp).1 m).trans_le (CKBridgeA_seqF_mem hp e).1

/-- `∑_e ∏_j M(σ_{e_j}) = Z₁(σ)^m`. -/
private lemma CKBridgeA_sum_prod {q n : ℕ} (t : ℝ) (σ : Fin n → Fin q) (m : ℕ) :
    ∑ e : Fin m → Fin n × Fin n, ∏ j, rsM q t (σ (e j).1) (σ (e j).2) = ckZ1 q t σ ^ m := by
  unfold ckZ1
  rw [Fintype.sum_pow]

/-- `Z₁(σ) > 0` for `n > 0`. -/
private lemma CKBridgeA_Z1_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) : 0 < ckZ1 q t σ := by
  have hb := ck_const_bounds hp
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  unfold ckZ1
  exact Finset.sum_pos (fun e _ => hb.1.trans_le (ck_rsM_mem hp _ _).1) Finset.univ_nonempty

/-- `Z₁(σ)^m g(σ, m) = ∑_e ∏_j M(σ_{e_j}) log F_e`. -/
private lemma CKBridgeA_Z1_mul_g {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) (m : ℕ) :
    ckZ1 q t σ ^ m * ckg q t σ m = ∑ e : Fin m → Fin n × Fin n,
      (∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * Real.log (rsSeqF q t e) := by
  unfold ckg
  rw [mul_inv_cancel_left₀ (pow_pos (CKBridgeA_Z1_pos hp hn σ) m).ne']

/-- Lemma 3.1(a): `|log F_e| ≤ m ℓ₀` for every edge list `e` of length `m`. -/
theorem ck_abs_log_seqF_le {q n m : ℕ} {t : ℝ} (hp : CKPar q t) (e : Fin m → Fin n × Fin n) :
    |Real.log (rsSeqF q t e)| ≤ m * ckEll q t := by
  have hb := ck_const_bounds hp
  obtain ⟨h1, h2⟩ := CKBridgeA_seqF_mem hp e
  have hpos : 0 < ckMm q t ^ m := pow_pos hb.1 m
  have hlo : Real.log (ckMm q t ^ m) ≤ Real.log (rsSeqF q t e) := Real.log_le_log hpos h1
  have hhi : Real.log (rsSeqF q t e) ≤ Real.log (ckMp t ^ m) :=
    Real.log_le_log (hpos.trans_le h1) h2
  rw [Real.log_pow] at hlo hhi
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hEll : -((m : ℝ) * ckEll q t) = (m : ℝ) * Real.log (ckMm q t) := by
    unfold ckEll; ring
  have hup : (m : ℝ) * Real.log (ckMp t) ≤ (m : ℝ) * ckEll q t :=
    mul_le_mul_of_nonneg_left hb.2.2.2.2.2.2.le hm
  rw [abs_le]
  constructor
  · rw [hEll]; exact hlo
  · exact hhi.trans hup

/-- Lemma 3.1(a): `|g(σ, m)| ≤ m ℓ₀` for `n ≥ 1`. -/
theorem ck_abs_g_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) (σ : Fin n → Fin q)
    (m : ℕ) : |ckg q t σ m| ≤ m * ckEll q t := by
  have hZm : 0 < ckZ1 q t σ ^ m := pow_pos (CKBridgeA_Z1_pos hp hn σ) m
  unfold ckg
  rw [abs_mul, abs_inv, abs_of_pos hZm, inv_mul_le_iff₀ hZm]
  calc |∑ e : Fin m → Fin n × Fin n,
          (∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * Real.log (rsSeqF q t e)|
      ≤ ∑ e : Fin m → Fin n × Fin n,
          |(∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * Real.log (rsSeqF q t e)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : Fin m → Fin n × Fin n,
          (∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * (m * ckEll q t) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [abs_mul, abs_of_nonneg (CKBridgeA_prod_nonneg hp σ e)]
        exact mul_le_mul_of_nonneg_left (ck_abs_log_seqF_le hp e) (CKBridgeA_prod_nonneg hp σ e)
    _ = ckZ1 q t σ ^ m * (m * ckEll q t) := by
        rw [← Finset.sum_mul, CKBridgeA_sum_prod]

/-- `∑_σ ∏_j M(σ_{e_j}) = q^n F_e`. -/
private lemma CKBridgeA_sum_sigma_prod {q n m : ℕ} {t : ℝ} (hp : CKPar q t)
    (e : Fin m → Fin n × Fin n) :
    ∑ σ : Fin n → Fin q, ∏ j, rsM q t (σ (e j).1) (σ (e j).2) = (q : ℝ) ^ n * rsSeqF q t e := by
  have hQ : (q : ℝ) ^ n ≠ 0 := (pow_pos (CKBridgeA_q_pos hp) n).ne'
  unfold rsSeqF
  rw [mul_inv_cancel_left₀ hQ]

/-- `∑_σ Z₁(σ)^m = q^n ∑_e F_e`. -/
private lemma CKBridgeA_sum_Z1_pow {q n : ℕ} {t : ℝ} (hp : CKPar q t) (m : ℕ) :
    ∑ σ : Fin n → Fin q, ckZ1 q t σ ^ m =
      (q : ℝ) ^ n * ∑ e : Fin m → Fin n × Fin n, rsSeqF q t e := by
  simp_rw [← CKBridgeA_sum_prod t _ m]
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => CKBridgeA_sum_sigma_prod hp e

/-- Lemma 3.1(b) at a general `t`. -/
private lemma CKBridgeA_cbar_gen {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) (m : ℕ) :
    (∑ e : Fin m → Fin n × Fin n, rsSeqF q t e * Real.log (rsSeqF q t e)) /
        ∑ e : Fin m → Fin n × Fin n, rsSeqF q t e =
      ∑ σ : Fin n → Fin q,
        ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) * ckg q t σ m := by
  have hQ : (q : ℝ) ^ n ≠ 0 := (pow_pos (CKBridgeA_q_pos hp) n).ne'
  have h1 : ∑ σ : Fin n → Fin q,
      ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) * ckg q t σ m =
      (∑ σ : Fin n → Fin q, ckZ1 q t σ ^ m * ckg q t σ m) /
        ∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have h2 : ∑ σ : Fin n → Fin q, ckZ1 q t σ ^ m * ckg q t σ m =
      (q : ℝ) ^ n * ∑ e : Fin m → Fin n × Fin n, rsSeqF q t e * Real.log (rsSeqF q t e) := by
    simp_rw [CKBridgeA_Z1_mul_g hp hn]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_mul, CKBridgeA_sum_sigma_prod hp e, mul_assoc]
  rw [h1, h2, CKBridgeA_sum_Z1_pow hp m, mul_div_mul_left _ _ hQ]

/-- Lemma 3.1(b): `c̄_m = ∑_σ ν_m(σ) g(σ, m)` with `ν_m(σ) = Z₁(σ)^m / ∑_{σ'} Z₁(σ')^m`, at
`t = t(x)`. -/
theorem ck_cbar_eq {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (m : ℕ) :
    rsCbar q n m x = ∑ σ : Fin n → Fin q,
      ckZ1 q (tRe q x) σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q (tRe q x) σ' ^ m) *
        ckg q (tRe q x) σ m := by
  unfold rsCbar
  exact CKBridgeA_cbar_gen (ckPar_tRe hq hx0 hx1) hn m

/-- `Z₁(σ) = n² + S(σ)`. -/
private lemma CKBridgeA_Z1_eq {q n : ℕ} (t : ℝ) (σ : Fin n → Fin q) :
    ckZ1 q t σ = (n : ℝ) ^ 2 + ckS q t σ := by
  unfold ckZ1 ckS
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ _e : Fin n × Fin n, (1 : ℝ) = (n : ℝ) ^ 2 := by simp [sq]
  rw [h1]
  ring

/-- `0 ≤ Z₁(σ) ≤ n²`. -/
private lemma CKBridgeA_Z1_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) (σ : Fin n → Fin q) :
    0 ≤ ckZ1 q t σ ∧ ckZ1 q t σ ≤ (n : ℝ) ^ 2 := by
  have hb := ck_const_bounds hp
  constructor
  · unfold ckZ1
    exact Finset.sum_nonneg fun e _ => hb.1.le.trans (ck_rsM_mem hp _ _).1
  · rw [CKBridgeA_Z1_eq]
    linarith [(ck_S_mem hp σ).2]

/-- `w_{count(e)}(σ) = ∏_j M(σ_{e_j})`. -/
private lemma CKBridgeA_rsW_edgeCount {q n m : ℕ} (t : ℝ) (σ : Fin n → Fin q)
    (e : Fin m → Fin n × Fin n) :
    rsW q t (rsEdgeCount e) σ = ∏ j, rsM q t (σ (e j).1) (σ (e j).2) := by
  unfold rsW rsEdgeCount
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := e)
    (fun j _ => Finset.mem_univ _) (fun j => rsM q t (σ (e j).1) (σ (e j).2))]
  refine Finset.prod_congr rfl fun uv _ => ?_
  rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.prod_const]

/-- Pointwise one-tilt: `𝖯_s(N) w_N(σ) = e^{κ} 𝖯^σ_s(N)` with `κ = (s/(2n))(Z₁(σ) - n²)`. -/
private lemma CKBridgeA_tilt {q n : ℕ} (s t : ℝ) (σ : Fin n → Fin q) (N : RSGraph n) :
    poisPi (rsMean n s) N * rsW q t N σ =
      Real.exp (s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2)) *
        poisPi (cpMean (fun a b => s * rsM q t a b) σ) N := by
  have h := rs_poisPi_mul_prod_pow (rsMean n s) (fun uv => rsM q t (σ uv.1) (σ uv.2)) N
  have e1 : (fun uv : Fin n × Fin n => rsMean n s uv * rsM q t (σ uv.1) (σ uv.2)) =
      cpMean (fun a b => s * rsM q t a b) σ := by
    funext uv
    simp only [rsMean, cpMean]
    ring
  have e2 : ∑ uv : Fin n × Fin n, rsMean n s uv * (rsM q t (σ uv.1) (σ uv.2) - 1) =
      s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2) := by
    simp only [rsMean]
    rw [← Finset.mul_sum, CKBridgeA_Z1_eq t σ]
    unfold ckS
    ring
  rw [e1, e2] at h
  exact h

/-- The tilted form of a `𝖯^σ_s`-term. -/
private lemma CKBridgeA_tilt' {q n : ℕ} (s t : ℝ) (σ : Fin n → Fin q) (N : RSGraph n) (f : ℝ) :
    poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * f =
      Real.exp (-(s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2))) *
        (poisPi (rsMean n s) N * (rsW q t N σ * f)) := by
  have h := CKBridgeA_tilt s t σ N
  have hexp : Real.exp (-(s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2))) *
      Real.exp (s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2)) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * f
      = (Real.exp (-(s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2))) *
          Real.exp (s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2))) *
          poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * f := by rw [hexp, one_mul]
    _ = Real.exp (-(s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2))) *
          ((Real.exp (s / (2 * n) * (ckZ1 q t σ - (n : ℝ) ^ 2)) *
            poisPi (cpMean (fun a b => s * rsM q t a b) σ) N) * f) := by ring
    _ = _ := by rw [← h]; ring

/-- `e^{-κ} Pois(sn/2)(m) n^{-2m} Z^m = Pois(sZ/(2n))(m)`. -/
private lemma CKBridgeA_pois_tilt {n : ℕ} (hn : 0 < n) (s Z : ℝ) (m : ℕ) :
    Real.exp (-(s / (2 * n) * (Z - (n : ℝ) ^ 2))) * poisPMF (s * n / 2) m *
        (((n : ℝ) ^ (2 * m))⁻¹ * Z ^ m) = poisPMF (s * Z / (2 * n)) m := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold poisPMF
  have h1 : Real.exp (-(s / (2 * n) * (Z - (n : ℝ) ^ 2))) * Real.exp (-(s * n / 2)) =
      Real.exp (-(s * Z / (2 * n))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have h2 : (s * n / 2) ^ m * (((n : ℝ) ^ (2 * m))⁻¹ * Z ^ m) = (s * Z / (2 * n)) ^ m := by
    rw [pow_mul, ← inv_pow, ← mul_pow, ← mul_pow]
    congr 1
    field_simp
  calc Real.exp (-(s / (2 * n) * (Z - (n : ℝ) ^ 2))) *
          (Real.exp (-(s * n / 2)) * (s * n / 2) ^ m / m.factorial) *
          (((n : ℝ) ^ (2 * m))⁻¹ * Z ^ m)
      = (Real.exp (-(s / (2 * n) * (Z - (n : ℝ) ^ 2))) * Real.exp (-(s * n / 2))) *
          ((s * n / 2) ^ m * (((n : ℝ) ^ (2 * m))⁻¹ * Z ^ m)) / m.factorial := by ring
    _ = _ := by rw [h1, h2]

/-- `n^{-2m} ∑_e |w_{count(e)}(σ) log F_{count(e)}| ≤ 2^m ℓ₀`. -/
private lemma CKBridgeA_inner_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) (σ : Fin n → Fin q)
    (m : ℕ) (hn : 0 < n) :
    ((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n,
        |rsW q t (rsEdgeCount e) σ * Real.log (rsF q t (rsEdgeCount e))| ≤
      2 ^ m * ckEll q t := by
  have hN : (0 : ℝ) < (n : ℝ) ^ (2 * m) := by positivity
  have hEll := (ck_const_bounds hp).2.2.2.2.2.1
  simp only [CKBridgeA_rsW_edgeCount, rs_rsF_edgeCount]
  rw [inv_mul_le_iff₀ hN]
  calc ∑ e : Fin m → Fin n × Fin n,
        |(∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * Real.log (rsSeqF q t e)|
      ≤ ∑ e : Fin m → Fin n × Fin n,
        (∏ j, rsM q t (σ (e j).1) (σ (e j).2)) * (m * ckEll q t) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [abs_mul, abs_of_nonneg (CKBridgeA_prod_nonneg hp σ e)]
        exact mul_le_mul_of_nonneg_left (ck_abs_log_seqF_le hp e) (CKBridgeA_prod_nonneg hp σ e)
    _ = ckZ1 q t σ ^ m * (m * ckEll q t) := by
        rw [← Finset.sum_mul, CKBridgeA_sum_prod]
    _ ≤ (n : ℝ) ^ (2 * m) * (2 ^ m * ckEll q t) := by
        have h1 : ckZ1 q t σ ^ m ≤ (n : ℝ) ^ (2 * m) := by
          rw [pow_mul]
          exact pow_le_pow_left₀ (CKBridgeA_Z1_mem hp σ).1 (CKBridgeA_Z1_mem hp σ).2 m
        have h2 : (m : ℝ) * ckEll q t ≤ 2 ^ m * ckEll q t := by
          refine mul_le_mul_of_nonneg_right ?_ hEll.le
          exact_mod_cast m.lt_two_pow_self.le
        exact mul_le_mul h1 h2 (mul_nonneg (Nat.cast_nonneg m) hEll.le) hN.le

/-- Lemma 3.1(c) for a fixed colouring `σ`. -/
private lemma CKBridgeA_fbar_sigma {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) {s : ℝ}
    (hs : 0 ≤ s) (σ : Fin n → Fin q) :
    ∑' N : RSGraph n, poisPi (cpMean (fun a b => s * rsM q t a b) σ) N * Real.log (rsF q t N) =
      ∑' m : ℕ, poisPMF (s * ckZ1 q t σ / (2 * n)) m * ckg q t σ m := by
  have hlam : 0 ≤ s * n / 2 := by positivity
  have hsum : Summable fun m : ℕ => poisPMF (s * n / 2) m * (((n : ℝ) ^ (2 * m))⁻¹ *
      ∑ e : Fin m → Fin n × Fin n,
        |rsW q t (rsEdgeCount e) σ * Real.log (rsF q t (rsEdgeCount e))|) := by
    have hS :=
      (RSPoisPiAux.hasSum_poisPMF_mul_pow (lam := s * n / 2) 2).summable.mul_right (ckEll q t)
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hS
    · exact mul_nonneg (poisPMF_nonneg hlam m)
        (mul_nonneg (by positivity) (Finset.sum_nonneg fun e _ => abs_nonneg _))
    · rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (CKBridgeA_inner_le hp σ m hn) (poisPMF_nonneg hlam m)
  have hsplit := (rs_poisson_split hs (fun N => rsW q t N σ * Real.log (rsF q t N)) hsum).2
  have hE : ∑' N : RSGraph n, poisPi (rsMean n s) N * (rsW q t N σ * Real.log (rsF q t N)) =
      rsExp n s (fun N => rsW q t N σ * Real.log (rsF q t N)) := rfl
  rw [tsum_congr fun N => CKBridgeA_tilt' s t σ N (Real.log (rsF q t N)), tsum_mul_left, hE,
    hsplit, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  simp only [CKBridgeA_rsW_edgeCount, rs_rsF_edgeCount]
  rw [← CKBridgeA_Z1_mul_g hp hn σ m, ← CKBridgeA_pois_tilt hn s (ckZ1 q t σ) m]
  ring

/-- Lemma 3.1(c): `f̄_n = q^{-n} ∑_σ ∑_m Pois(s Z₁(σ)/(2n))(m) g(σ, m)` for `n ≥ 1`, `s ≥ 0`.
Proof: for each `σ`, the pointwise one-tilt (`CKBridgeA_tilt`, the identity of `rs_one_tilt_pt`
with exponent `(s/(2n))(Z₁(σ) - n²)`) and Poisson splitting (`rs_poisson_split`) turn the
series over multigraphs into a Poisson mixture over edge lists (`CKBridgeA_fbar_sigma`). -/
theorem ck_fbar_eq {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    rsFbar q n s t = ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
      ∑' m : ℕ, poisPMF (s * ckZ1 q t σ / (2 * n)) m * ckg q t σ m := by
  simp only [rsFbar, cpExp, poisPiExp]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  congr 1
  exact CKBridgeA_fbar_sigma hp hn hs σ

/-- The average of `Z₁` is `n² + t(q-1)n`. -/
private lemma CKBridgeA_avg_Z1 {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : n ≠ 0) :
    ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, ckZ1 q t σ =
      (n : ℝ) ^ 2 + t * ((q : ℝ) - 1) * n := by
  have hq0 : q ≠ 0 := by have := hp.two_le; omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hQ : (q : ℝ) ^ n ≠ 0 := pow_ne_zero n hqR
  simp_rw [CKBridgeA_Z1_eq t, ck_S_eq hq0 t]
  rw [Finset.sum_add_distrib, CKBridgeA_sum_const, ← Finset.mul_sum, mul_add,
    inv_mul_cancel_left₀ hQ]
  have h := ck_avg_devSq (q := q) hq0 hn
  have h2 : ((q : ℝ) ^ n)⁻¹ * (t * q * (n : ℝ) ^ 2 * ∑ σ : Fin n → Fin q, rsDevSq σ) =
      t * q * (n : ℝ) ^ 2 * (((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, rsDevSq σ) := by ring
  rw [h2, h]
  field_simp

/-- Lemma 3.1(d): `ν_m(σ) ≤ q^{-n} (1 - 1/n)^{-m}` for `n ≥ 2`.  Proof: `Z₁(σ) ≤ n²`, and by
Jensen's inequality for `y ↦ y^m` the average of `Z₁^m` is at least `(n² (1 - 1/n))^m`. -/
theorem ck_nu_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 2 ≤ n) (σ : Fin n → Fin q) (m : ℕ) :
    ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) ≤
      ((q : ℝ) ^ n)⁻¹ * ((1 - (n : ℝ)⁻¹) ^ m)⁻¹ := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := pow_pos (CKBridgeA_q_pos hp) n
  have hgt := hp.gt
  have hB : 0 < 1 - (n : ℝ)⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ (by linarith))
  have hA : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  -- the average of `Z₁` is at least `n² (1 - 1/n)`
  have havg : (n : ℝ) ^ 2 * (1 - (n : ℝ)⁻¹) ≤
      ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, ckZ1 q t σ := by
    rw [CKBridgeA_avg_Z1 hp hn0]
    have e : (n : ℝ) ^ 2 * (1 - (n : ℝ)⁻¹) = (n : ℝ) ^ 2 - n := by
      field_simp
    rw [e]
    have hn0' : (0 : ℝ) ≤ n := by linarith
    nlinarith
  -- Jensen for `y ↦ y^m`
  have hw : ∑ _σ : Fin n → Fin q, ((q : ℝ) ^ n)⁻¹ = 1 := by
    rw [CKBridgeA_sum_const, mul_inv_cancel₀ hQ.ne']
  have hJ := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin n → Fin q))
    (fun _ => ((q : ℝ) ^ n)⁻¹) (fun σ => ckZ1 q t σ) (fun _ _ => by positivity) hw
    (fun σ _ => (CKBridgeA_Z1_mem hp σ).1) m
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hJ
  have hlow : ((n : ℝ) ^ 2 * (1 - (n : ℝ)⁻¹)) ^ m ≤
      ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m :=
    (pow_le_pow_left₀ (by positivity) havg m).trans hJ
  have hD : 0 < ∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m :=
    pos_of_mul_pos_right ((pow_pos (mul_pos hA hB) m).trans_le hlow) (inv_pos.2 hQ).le
  rw [div_le_iff₀ hD]
  calc ckZ1 q t σ ^ m ≤ ((n : ℝ) ^ 2) ^ m :=
        pow_le_pow_left₀ (CKBridgeA_Z1_mem hp σ).1 (CKBridgeA_Z1_mem hp σ).2 m
    _ = ((1 - (n : ℝ)⁻¹) ^ m)⁻¹ * ((n : ℝ) ^ 2 * (1 - (n : ℝ)⁻¹)) ^ m := by
        rw [mul_pow, mul_left_comm, inv_mul_cancel₀ (pow_pos hB m).ne', mul_one]
    _ ≤ ((1 - (n : ℝ)⁻¹) ^ m)⁻¹ *
          (((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) :=
        mul_le_mul_of_nonneg_left hlow (inv_nonneg.2 (pow_pos hB m).le)
    _ = ((q : ℝ) ^ n)⁻¹ * ((1 - (n : ℝ)⁻¹) ^ m)⁻¹ * ∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m := by
        ring

/-! ### Lemmas 3.2 and 3.3

Route:
* `g(σ,m) = E_{e ∼ p_σ^{⊗m}} log F_e` is written as a product expectation `CKBridgeB_PE`.
* `ck_g_succ`: peel off the first edge (`Fin.consEquiv`); one extra edge moves `log F` by
  at most `ℓ₀` (`CKBridgeB_log_cons`).
* `ck_g_lip`: in place of the maximal coupling of Lemma 3.2(c), a hybrid argument
  (`CKBridgeB_PE_hybrid`) changes the law of one edge at a time, and replacing one edge moves
  `log F` by at most `2ℓ₀` (`CKBridgeB_log_update`); one recoloured vertex moves `p_σ` by
  `O(1/n)` in `ℓ¹` (`CKBridgeB_p_update`); `g` is invariant under vertex permutations
  (`CKBridgeB_ckg_perm`), colourings with equal colour counts differ by a permutation
  (`CKBridgeB_exists_perm`), and an induction on `∑_c |N_c - N'_c|` recolours one vertex at a
  time (`CKBridgeB_count_induction`).
* `ck_bridge`: both averages are compared with the reference value
  `ḡ = q^{-n} ∑_σ g(σ, ⌊sn/2⌋)` (`CKBridgeB_ref_bound`), an average over `σ` in place of the
  value at a balanced colouring, using `E_σ ‖λ_σ - u‖₁ ≤ √(q/n)` (`CKBridgeB_avg_dev`), the
  tilted Poisson moment `E[m y^m]`, `E|m - λ| ≤ √λ` (`CKBridgeB_pois_series`) and
  `E_σ (sn/2 - sn φ(σ)/2) ≤ s/2` (`CKBridgeB_avg_gap`).
-/

/-! ### Product expectations over edge lists -/

/-- `∑_e (∏_j a(e_j)) G(e)`: the expectation of `G` under `a^{⊗m}` (no normalization). -/
private def CKBridgeB_PE {α : Type*} [Fintype α] (a : α → ℝ) (m : ℕ)
    (G : (Fin m → α) → ℝ) : ℝ :=
  ∑ e : Fin m → α, (∏ j, a (e j)) * G e

private lemma CKBridgeB_PE_succ {α : Type*} [Fintype α] (a : α → ℝ) (m : ℕ)
    (G : (Fin (m + 1) → α) → ℝ) :
    CKBridgeB_PE a (m + 1) G = ∑ f, a f * CKBridgeB_PE a m (fun e => G (Fin.cons f e)) := by
  unfold CKBridgeB_PE
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => α).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [mul_assoc]
  rfl

private lemma CKBridgeB_PE_sub {α : Type*} [Fintype α] (a : α → ℝ) (m : ℕ)
    (G H : (Fin m → α) → ℝ) :
    CKBridgeB_PE a m (fun e => G e - H e) = CKBridgeB_PE a m G - CKBridgeB_PE a m H := by
  unfold CKBridgeB_PE
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

private lemma CKBridgeB_PE_abs_le {α : Type*} [Fintype α] {a : α → ℝ} (ha : ∀ f, 0 ≤ a f)
    (m : ℕ) {G : (Fin m → α) → ℝ} {B : ℝ} (hG : ∀ e, |G e| ≤ B) :
    |CKBridgeB_PE a m G| ≤ (∑ f, a f) ^ m * B := by
  unfold CKBridgeB_PE
  rw [Fintype.sum_pow, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e _ => ?_)
  rw [abs_mul, abs_of_nonneg (Finset.prod_nonneg fun j _ => ha (e j))]
  exact mul_le_mul_of_nonneg_left (hG e) (Finset.prod_nonneg fun j _ => ha (e j))

/-- Hybrid argument: for probability vectors `a`, `b`, if changing one entry of `e` moves `G(e)`
by at most `B`, then `|E_{a^{⊗m}} G - E_{b^{⊗m}} G| ≤ m B ‖a - b‖₁`.  The law of one edge is
changed at a time. -/
private lemma CKBridgeB_PE_hybrid {α : Type*} [Fintype α] {a b : α → ℝ}
    (ha : ∀ f, 0 ≤ a f) (hb : ∀ f, 0 ≤ b f) (ha1 : ∑ f, a f = 1) (hb1 : ∑ f, b f = 1)
    {B : ℝ} : ∀ (m : ℕ) (G : (Fin m → α) → ℝ),
      (∀ e k x, |G (Function.update e k x) - G e| ≤ B) →
      |CKBridgeB_PE a m G - CKBridgeB_PE b m G| ≤ m * B * ∑ f, |a f - b f| := by
  intro m
  induction m with
  | zero =>
    intro G _
    have h : CKBridgeB_PE a 0 G = CKBridgeB_PE b 0 G := by
      unfold CKBridgeB_PE
      simp
    rw [h, sub_self, abs_zero]
    simp
  | succ m ih =>
    intro G hG
    have hne : Nonempty α := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at ha1
    obtain ⟨f₀⟩ := hne
    set S := ∑ f, |a f - b f| with hS
    have hGf : ∀ f, ∀ (e : Fin m → α) k x,
        |G (Fin.cons f (Function.update e k x)) - G (Fin.cons f e)| ≤ B := by
      intro f e k x
      rw [Fin.cons_update]
      exact hG _ _ _
    have key : CKBridgeB_PE a (m + 1) G - CKBridgeB_PE b (m + 1) G =
        ∑ f, a f * (CKBridgeB_PE a m (fun e => G (Fin.cons f e)) -
          CKBridgeB_PE b m (fun e => G (Fin.cons f e))) +
        ∑ f, (a f - b f) * (CKBridgeB_PE b m (fun e => G (Fin.cons f e)) -
          CKBridgeB_PE b m (fun e => G (Fin.cons f₀ e))) := by
      rw [CKBridgeB_PE_succ, CKBridgeB_PE_succ, ← Finset.sum_add_distrib]
      have h1 : ∀ f, a f * (CKBridgeB_PE a m (fun e => G (Fin.cons f e)) -
          CKBridgeB_PE b m (fun e => G (Fin.cons f e))) +
          (a f - b f) * (CKBridgeB_PE b m (fun e => G (Fin.cons f e)) -
          CKBridgeB_PE b m (fun e => G (Fin.cons f₀ e))) =
          (a f * CKBridgeB_PE a m (fun e => G (Fin.cons f e)) -
            b f * CKBridgeB_PE b m (fun e => G (Fin.cons f e))) -
          (a f - b f) * CKBridgeB_PE b m (fun e => G (Fin.cons f₀ e)) := fun f => by ring
      simp_rw [h1, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, ha1, hb1]
      ring
    rw [key]
    have hA : |∑ f, a f * (CKBridgeB_PE a m (fun e => G (Fin.cons f e)) -
          CKBridgeB_PE b m (fun e => G (Fin.cons f e)))| ≤ m * B * S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ f, |a f * (CKBridgeB_PE a m (fun e => G (Fin.cons f e)) -
            CKBridgeB_PE b m (fun e => G (Fin.cons f e)))|
          ≤ ∑ f, a f * (m * B * S) := by
            refine Finset.sum_le_sum fun f _ => ?_
            rw [abs_mul, abs_of_nonneg (ha f)]
            exact mul_le_mul_of_nonneg_left (ih _ (hGf f)) (ha f)
        _ = m * B * S := by rw [← Finset.sum_mul, ha1, one_mul]
    have hB : |∑ f, (a f - b f) * (CKBridgeB_PE b m (fun e => G (Fin.cons f e)) -
          CKBridgeB_PE b m (fun e => G (Fin.cons f₀ e)))| ≤ B * S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ f, |(a f - b f) * (CKBridgeB_PE b m (fun e => G (Fin.cons f e)) -
            CKBridgeB_PE b m (fun e => G (Fin.cons f₀ e)))|
          ≤ ∑ f, |a f - b f| * B := by
            refine Finset.sum_le_sum fun f _ => ?_
            rw [abs_mul]
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            rw [← CKBridgeB_PE_sub]
            have := CKBridgeB_PE_abs_le hb m (G := fun e => G (Fin.cons f e) - G (Fin.cons f₀ e))
              (B := B) (fun e => by
                have hc : (Fin.cons f₀ e : Fin (m + 1) → α) =
                    Function.update (Fin.cons f e : Fin (m + 1) → α) 0 f₀ :=
                  (Fin.update_cons_zero (α := fun _ => α) f e f₀).symm
                rw [hc, abs_sub_comm]
                exact hG _ _ _)
            rwa [hb1, one_pow, one_mul] at this
        _ = B * S := by rw [← Finset.sum_mul, mul_comm]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ m * B * S + B * S := add_le_add hA hB
      _ = ((m + 1 : ℕ) : ℝ) * B * S := by push_cast; ring

/-! ### `g` as a product expectation; one added edge -/

/-- The single-edge law `p_σ(v,w) = M(σ_v, σ_w) / (n² φ(σ))`. -/
private def CKBridgeB_p (q : ℕ) (t : ℝ) {n : ℕ} (σ : Fin n → Fin q) (f : Fin n × Fin n) : ℝ :=
  rsM q t (σ f.1) (σ f.2) / ckZ1 q t σ

private lemma CKBridgeB_ckg_eq {q n : ℕ} (t : ℝ) (σ : Fin n → Fin q) (m : ℕ) :
    ckg q t σ m = CKBridgeB_PE (CKBridgeB_p q t σ) m (fun e => Real.log (rsSeqF q t e)) := by
  unfold ckg CKBridgeB_PE CKBridgeB_p
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private lemma CKBridgeB_rsM_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    0 < rsM q t a b :=
  lt_of_lt_of_le (ck_const_bounds hp).1 (ck_rsM_mem hp a b).1

private lemma CKBridgeB_Z_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) : 0 < ckZ1 q t σ := by
  unfold ckZ1
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun e _ => CKBridgeB_rsM_pos hp _ _) Finset.univ_nonempty

private lemma CKBridgeB_p_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) (f : Fin n × Fin n) : 0 ≤ CKBridgeB_p q t σ f :=
  div_nonneg (CKBridgeB_rsM_pos hp _ _).le (CKBridgeB_Z_pos hp hn σ).le

private lemma CKBridgeB_p_sum {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) : ∑ f, CKBridgeB_p q t σ f = 1 := by
  unfold CKBridgeB_p
  rw [← Finset.sum_div]
  exact div_self (CKBridgeB_Z_pos hp hn σ).ne'

private lemma CKBridgeB_seqF_pos {q n m : ℕ} {t : ℝ} (hp : CKPar q t)
    (e : Fin m → Fin n × Fin n) : 0 < rsSeqF q t e := by
  unfold rsSeqF
  have hq2 := hp.two_le
  have hq : (0 : ℝ) < q := by positivity
  have : Nonempty (Fin q) := ⟨⟨0, by omega⟩⟩
  refine mul_pos (inv_pos.mpr (pow_pos hq n)) ?_
  exact Finset.sum_pos (fun τ _ => Finset.prod_pos fun j _ => CKBridgeB_rsM_pos hp _ _)
    Finset.univ_nonempty

private lemma CKBridgeB_seqF_cons {q n m : ℕ} {t : ℝ} (hp : CKPar q t) (f : Fin n × Fin n)
    (e : Fin m → Fin n × Fin n) :
    ckMm q t * rsSeqF q t e ≤ rsSeqF q t (Fin.cons f e) ∧
      rsSeqF q t (Fin.cons f e) ≤ ckMp t * rsSeqF q t e := by
  have hcons : ∀ τ : Fin n → Fin q,
      ∏ j, rsM q t (τ ((Fin.cons f e : Fin (m + 1) → Fin n × Fin n) j).1)
        (τ ((Fin.cons f e : Fin (m + 1) → Fin n × Fin n) j).2) =
      rsM q t (τ f.1) (τ f.2) * ∏ j, rsM q t (τ (e j).1) (τ (e j).2) := by
    intro τ
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hq2 := hp.two_le
  have hq : (0 : ℝ) < q := by positivity
  have hQ : (0 : ℝ) ≤ ((q : ℝ) ^ n)⁻¹ := (inv_pos.mpr (pow_pos hq n)).le
  unfold rsSeqF
  simp_rw [hcons]
  have hmul : ∀ c : ℝ, c * (((q : ℝ) ^ n)⁻¹ *
      ∑ τ : Fin n → Fin q, ∏ j, rsM q t (τ (e j).1) (τ (e j).2)) =
      ((q : ℝ) ^ n)⁻¹ * ∑ τ : Fin n → Fin q, c * ∏ j, rsM q t (τ (e j).1) (τ (e j).2) := by
    intro c
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hmul, hmul]
  constructor
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) hQ
    exact mul_le_mul_of_nonneg_right (ck_rsM_mem hp _ _).1
      (Finset.prod_nonneg fun j _ => (CKBridgeB_rsM_pos hp _ _).le)
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) hQ
    exact mul_le_mul_of_nonneg_right (ck_rsM_mem hp _ _).2
      (Finset.prod_nonneg fun j _ => (CKBridgeB_rsM_pos hp _ _).le)

private lemma CKBridgeB_log_cons {q n m : ℕ} {t : ℝ} (hp : CKPar q t) (f : Fin n × Fin n)
    (e : Fin m → Fin n × Fin n) :
    |Real.log (rsSeqF q t (Fin.cons f e)) - Real.log (rsSeqF q t e)| ≤ ckEll q t := by
  obtain ⟨h1, h2⟩ := CKBridgeB_seqF_cons hp f e
  have hF := CKBridgeB_seqF_pos hp e
  have hF' := CKBridgeB_seqF_pos hp (Fin.cons f e : Fin (m + 1) → Fin n × Fin n)
  obtain ⟨hm0, -, hp1, -, -, -, hlogp⟩ := ck_const_bounds hp
  have hlo : Real.log (ckMm q t) + Real.log (rsSeqF q t e) ≤
      Real.log (rsSeqF q t (Fin.cons f e)) := by
    rw [← Real.log_mul hm0.ne' hF.ne']
    exact Real.log_le_log (mul_pos hm0 hF) h1
  have hhi : Real.log (rsSeqF q t (Fin.cons f e)) ≤
      Real.log (ckMp t) + Real.log (rsSeqF q t e) := by
    rw [← Real.log_mul (by linarith) hF.ne']
    exact Real.log_le_log hF' h2
  have hell : ckEll q t = -Real.log (ckMm q t) := rfl
  rw [abs_le]
  constructor <;> linarith

/-- Lemma 3.2(a): `|g(σ, m+1) - g(σ, m)| ≤ ℓ₀` for `n ≥ 1`. -/
theorem ck_g_succ {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) (σ : Fin n → Fin q)
    (m : ℕ) : |ckg q t σ (m + 1) - ckg q t σ m| ≤ ckEll q t := by
  rw [CKBridgeB_ckg_eq, CKBridgeB_ckg_eq, CKBridgeB_PE_succ]
  set p := CKBridgeB_p q t σ with hp_def
  have hp0 : ∀ f, 0 ≤ p f := CKBridgeB_p_nonneg hp hn σ
  have hp1 : ∑ f, p f = 1 := CKBridgeB_p_sum hp hn σ
  have h : CKBridgeB_PE p m (fun e => Real.log (rsSeqF q t e)) =
      ∑ f, p f * CKBridgeB_PE p m (fun e => Real.log (rsSeqF q t e)) := by
    rw [← Finset.sum_mul, hp1, one_mul]
  rw [h, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub, ← CKBridgeB_PE_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ f, |p f * CKBridgeB_PE p m
        (fun e => Real.log (rsSeqF q t (Fin.cons f e)) - Real.log (rsSeqF q t e))|
      ≤ ∑ f, p f * ckEll q t := by
        refine Finset.sum_le_sum fun f _ => ?_
        rw [abs_mul, abs_of_nonneg (hp0 f)]
        refine mul_le_mul_of_nonneg_left ?_ (hp0 f)
        have := CKBridgeB_PE_abs_le hp0 m (B := ckEll q t) (fun e => CKBridgeB_log_cons hp f e)
        rwa [hp1, one_pow, one_mul] at this
    _ = ckEll q t := by rw [← Finset.sum_mul, hp1, one_mul]

/-! ### Replacing one edge -/

private lemma CKBridgeB_prod_update {β : Type*} {m : ℕ} (h : β → ℝ) (e : Fin m → β) (k : Fin m)
    (x : β) : (∏ j, h (Function.update e k x j)) * h (e k) = (∏ j, h (e j)) * h x := by
  rw [← Finset.mul_prod_erase Finset.univ (fun j => h (Function.update e k x j))
      (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ (fun j => h (e j)) (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k, h (Function.update e k x j) =
      ∏ j ∈ Finset.univ.erase k, h (e j) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, Function.update_self]
  ring

private lemma CKBridgeB_prod_update_le {β : Type*} {m : ℕ} {h : β → ℝ} {lo hi : ℝ}
    (h0 : ∀ f, 0 ≤ h f) (hlo : ∀ f, lo ≤ h f) (hhi : ∀ f, h f ≤ hi) (e : Fin m → β)
    (k : Fin m) (x : β) :
    lo * ∏ j, h (Function.update e k x j) ≤ hi * ∏ j, h (e j) := by
  have key := CKBridgeB_prod_update h e k x
  have P0 : 0 ≤ ∏ j, h (Function.update e k x j) := Finset.prod_nonneg fun j _ => h0 _
  have P1 : 0 ≤ ∏ j, h (e j) := Finset.prod_nonneg fun j _ => h0 _
  calc lo * ∏ j, h (Function.update e k x j)
      ≤ h (e k) * ∏ j, h (Function.update e k x j) := mul_le_mul_of_nonneg_right (hlo _) P0
    _ = (∏ j, h (e j)) * h x := by rw [mul_comm]; exact key
    _ ≤ (∏ j, h (e j)) * hi := mul_le_mul_of_nonneg_left (hhi x) P1
    _ = hi * ∏ j, h (e j) := mul_comm _ _

private lemma CKBridgeB_seqF_update_le {q n m : ℕ} {t : ℝ} (hp : CKPar q t)
    (e : Fin m → Fin n × Fin n) (k : Fin m) (x : Fin n × Fin n) :
    ckMm q t * rsSeqF q t (Function.update e k x) ≤ ckMp t * rsSeqF q t e := by
  have hq2 := hp.two_le
  have hq : (0 : ℝ) < q := by positivity
  have hQ : (0 : ℝ) ≤ ((q : ℝ) ^ n)⁻¹ := (inv_pos.mpr (pow_pos hq n)).le
  unfold rsSeqF
  have hmul : ∀ (c : ℝ) (e' : Fin m → Fin n × Fin n), c * (((q : ℝ) ^ n)⁻¹ *
      ∑ τ : Fin n → Fin q, ∏ j, rsM q t (τ (e' j).1) (τ (e' j).2)) =
      ((q : ℝ) ^ n)⁻¹ * ∑ τ : Fin n → Fin q, c * ∏ j, rsM q t (τ (e' j).1) (τ (e' j).2) := by
    intro c e'
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [hmul, hmul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun τ _ => ?_) hQ
  exact CKBridgeB_prod_update_le (h := fun f : Fin n × Fin n => rsM q t (τ f.1) (τ f.2))
    (fun f => (CKBridgeB_rsM_pos hp _ _).le) (fun f => (ck_rsM_mem hp _ _).1)
    (fun f => (ck_rsM_mem hp _ _).2) e k x

private lemma CKBridgeB_log_update {q n m : ℕ} {t : ℝ} (hp : CKPar q t)
    (e : Fin m → Fin n × Fin n) (k : Fin m) (x : Fin n × Fin n) :
    |Real.log (rsSeqF q t (Function.update e k x)) - Real.log (rsSeqF q t e)| ≤
      2 * ckEll q t := by
  have h1 := CKBridgeB_seqF_update_le hp e k x
  have h2 := CKBridgeB_seqF_update_le hp (Function.update e k x) k (e k)
  rw [Function.update_idem, Function.update_eq_self] at h2
  have hF := CKBridgeB_seqF_pos hp e
  have hF' := CKBridgeB_seqF_pos hp (Function.update e k x)
  obtain ⟨hm0, -, hp1, -, -, -, hlogp⟩ := ck_const_bounds hp
  have hmp : 0 < ckMp t := by linarith
  have l1 : Real.log (ckMm q t) + Real.log (rsSeqF q t (Function.update e k x)) ≤
      Real.log (ckMp t) + Real.log (rsSeqF q t e) := by
    rw [← Real.log_mul hm0.ne' hF'.ne', ← Real.log_mul hmp.ne' hF.ne']
    exact Real.log_le_log (mul_pos hm0 hF') h1
  have l2 : Real.log (ckMm q t) + Real.log (rsSeqF q t e) ≤
      Real.log (ckMp t) + Real.log (rsSeqF q t (Function.update e k x)) := by
    rw [← Real.log_mul hm0.ne' hF.ne', ← Real.log_mul hmp.ne' hF'.ne']
    exact Real.log_le_log (mul_pos hm0 hF) h2
  have hell : ckEll q t = -Real.log (ckMm q t) := rfl
  rw [abs_le]
  constructor <;> linarith

/-! ### Recolouring one vertex -/

private lemma CKBridgeB_l1_normalize {ι : Type*} [Fintype ι] (w w' : ι → ℝ)
    (hw' : ∀ i, 0 ≤ w' i) {Z Z' : ℝ} (hZdef : ∑ i, w i = Z) (hZ'def : ∑ i, w' i = Z')
    (hZ : 0 < Z) (hZ' : 0 < Z') :
    ∑ i, |w i / Z - w' i / Z'| ≤ 2 * (∑ i, |w i - w' i|) / Z := by
  have hdiff : |Z' - Z| ≤ ∑ i, |w i - w' i| := by
    rw [← hZdef, ← hZ'def, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun i _ => abs_sub_comm _ _))
  have h1 : ∀ i, |w i / Z - w' i / Z'| ≤ |w i - w' i| / Z + w' i * (|Z' - Z| / (Z * Z')) := by
    intro i
    have e : w i / Z - w' i / Z' = (w i - w' i) / Z + w' i * ((Z' - Z) / (Z * Z')) := by
      field_simp
      ring
    rw [e]
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_div, abs_of_pos hZ, abs_mul, abs_of_nonneg (hw' i), abs_div,
      abs_of_pos (mul_pos hZ hZ')]
  calc ∑ i, |w i / Z - w' i / Z'|
      ≤ ∑ i, (|w i - w' i| / Z + w' i * (|Z' - Z| / (Z * Z'))) :=
        Finset.sum_le_sum fun i _ => h1 i
    _ = (∑ i, |w i - w' i|) / Z + |Z' - Z| / Z := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, hZ'def]
        congr 1
        field_simp
    _ ≤ (∑ i, |w i - w' i|) / Z + (∑ i, |w i - w' i|) / Z := by
        gcongr
    _ = 2 * (∑ i, |w i - w' i|) / Z := by ring

private lemma CKBridgeB_rsM_abs_sub_le {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b c d : Fin q) :
    |rsM q t a b - rsM q t c d| ≤ ckMp t - ckMm q t := by
  have h1 := ck_rsM_mem hp a b
  have h2 := ck_rsM_mem hp c d
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma CKBridgeB_sum_w_update {q n : ℕ} {t : ℝ} (hp : CKPar q t) (σ : Fin n → Fin q)
    (v : Fin n) (b : Fin q) :
    ∑ f : Fin n × Fin n, |rsM q t (σ f.1) (σ f.2) -
      rsM q t (Function.update σ v b f.1) (Function.update σ v b f.2)| ≤
      2 * n * (ckMp t - ckMm q t) := by
  obtain ⟨-, hm1, hp1, -, -, -, -⟩ := ck_const_bounds hp
  have hθ0 : 0 ≤ ckMp t - ckMm q t := by linarith
  have hpt : ∀ f : Fin n × Fin n, |rsM q t (σ f.1) (σ f.2) -
      rsM q t (Function.update σ v b f.1) (Function.update σ v b f.2)| ≤
      (ckMp t - ckMm q t) * ((if f.1 = v then 1 else 0) + (if f.2 = v then 1 else 0)) := by
    intro f
    by_cases h : f.1 = v ∨ f.2 = v
    · have h1 : (1 : ℝ) ≤ (if f.1 = v then 1 else 0) + (if f.2 = v then 1 else 0) := by
        rcases h with h | h
        · rw [if_pos h]
          split_ifs <;> norm_num
        · rw [if_pos h]
          split_ifs <;> norm_num
      have h2 : ckMp t - ckMm q t ≤
          (ckMp t - ckMm q t) * ((if f.1 = v then 1 else 0) + (if f.2 = v then 1 else 0)) := by
        nlinarith
      exact (CKBridgeB_rsM_abs_sub_le hp _ _ _ _).trans h2
    · push Not at h
      rw [Function.update_of_ne h.1, Function.update_of_ne h.2, sub_self, abs_zero,
        if_neg h.1, if_neg h.2]
      simp
  have hs1 : ∑ f : Fin n × Fin n, (if f.1 = v then (1 : ℝ) else 0) = n := by
    rw [Fintype.sum_prod_type]
    have : ∀ a : Fin n, ∑ _b : Fin n, (if a = v then (1 : ℝ) else 0) =
        if a = v then (n : ℝ) else 0 := by
      intro a
      split_ifs <;> simp
    rw [Finset.sum_congr rfl fun a _ => this a]
    simp
  have hs2 : ∑ f : Fin n × Fin n, (if f.2 = v then (1 : ℝ) else 0) = n := by
    rw [Fintype.sum_prod_type]
    have : ∀ _a : Fin n, ∑ b : Fin n, (if b = v then (1 : ℝ) else 0) = 1 := by
      intro a
      simp
    rw [Finset.sum_congr rfl fun a _ => this a]
    simp
  refine (Finset.sum_le_sum fun f _ => hpt f).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hs1, hs2]
  ring

private lemma CKBridgeB_Z_ge {q n : ℕ} {t : ℝ} (hp : CKPar q t) (σ : Fin n → Fin q) :
    (n : ℝ) ^ 2 * ckMm q t ≤ ckZ1 q t σ := by
  unfold ckZ1
  calc (n : ℝ) ^ 2 * ckMm q t = ∑ _f : Fin n × Fin n, ckMm q t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := Finset.sum_le_sum fun f _ => (ck_rsM_mem hp _ _).1

private lemma CKBridgeB_p_update {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) (v : Fin n) (b : Fin q) :
    ∑ f, |CKBridgeB_p q t σ f - CKBridgeB_p q t (Function.update σ v b) f| ≤
      4 * (ckMp t - ckMm q t) / (n * ckMm q t) := by
  unfold CKBridgeB_p
  have h := CKBridgeB_l1_normalize (fun f : Fin n × Fin n => rsM q t (σ f.1) (σ f.2))
    (fun f => rsM q t (Function.update σ v b f.1) (Function.update σ v b f.2))
    (fun f => (CKBridgeB_rsM_pos hp _ _).le) rfl rfl (CKBridgeB_Z_pos hp hn σ)
    (CKBridgeB_Z_pos hp hn _)
  refine h.trans ?_
  have hS := CKBridgeB_sum_w_update hp σ v b
  have hZ := CKBridgeB_Z_ge hp σ
  obtain ⟨hm0, hm1, hp1, -, -, -, -⟩ := ck_const_bounds hp
  have hθ0 : 0 ≤ ckMp t - ckMm q t := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hZpos := CKBridgeB_Z_pos hp hn σ
  calc 2 * (∑ f : Fin n × Fin n, |rsM q t (σ f.1) (σ f.2) -
        rsM q t (Function.update σ v b f.1) (Function.update σ v b f.2)|) / ckZ1 q t σ
      ≤ 2 * (2 * n * (ckMp t - ckMm q t)) / ckZ1 q t σ := by gcongr
    _ ≤ 2 * (2 * n * (ckMp t - ckMm q t)) / ((n : ℝ) ^ 2 * ckMm q t) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hZ
    _ = 4 * (ckMp t - ckMm q t) / (n * ckMm q t) := by
        field_simp
        ring

/-! ### Permutation invariance -/

private lemma CKBridgeB_seqF_perm {q n m : ℕ} (t : ℝ) (π : Equiv.Perm (Fin n))
    (e : Fin m → Fin n × Fin n) :
    rsSeqF q t (fun j => (π (e j).1, π (e j).2)) = rsSeqF q t e := by
  unfold rsSeqF
  congr 1
  exact Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl (Fin q))) _ _
    (fun τ => by simp [Equiv.arrowCongr_apply])

private lemma CKBridgeB_ckZ1_perm {q n : ℕ} (t : ℝ) (σ : Fin n → Fin q)
    (π : Equiv.Perm (Fin n)) : ckZ1 q t (σ ∘ π) = ckZ1 q t σ := by
  unfold ckZ1
  exact Fintype.sum_equiv (Equiv.prodCongr π π) _ _ (fun f => by simp [Equiv.prodCongr_apply])

private lemma CKBridgeB_ckg_perm {q n : ℕ} (t : ℝ) (σ : Fin n → Fin q) (π : Equiv.Perm (Fin n))
    (m : ℕ) : ckg q t (σ ∘ π) m = ckg q t σ m := by
  unfold ckg
  rw [CKBridgeB_ckZ1_perm]
  congr 1
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin m)) (Equiv.prodCongr π π)) _ _
    (fun e => ?_)
  have he : (Equiv.arrowCongr (Equiv.refl (Fin m)) (Equiv.prodCongr π π)) e =
      fun j => (π (e j).1, π (e j).2) := rfl
  rw [he, CKBridgeB_seqF_perm]
  rfl

private lemma CKBridgeB_fiberCard_eq {n q : ℕ} (f : Fin n → Fin q) (c : Fin q) :
    (fiberCard f c : ℝ) = ∑ w, if f w = c then (1 : ℝ) else 0 := by
  unfold fiberCard
  rw [Finset.natCast_card_filter]
  exact Finset.sum_congr rfl fun w _ => by split_ifs <;> rfl

private lemma CKBridgeB_card_subtype {n q : ℕ} (f : Fin n → Fin q) (c : Fin q) :
    Fintype.card {v // f v = c} = fiberCard f c := by
  rw [Fintype.card_subtype]
  unfold fiberCard
  convert rfl

/-- Colourings with the same colour counts differ by a permutation. -/
private lemma CKBridgeB_exists_perm {n q : ℕ} (σ σ' : Fin n → Fin q)
    (h : ∀ c, fiberCard σ c = fiberCard σ' c) : ∃ π : Equiv.Perm (Fin n), σ' = σ ∘ π := by
  have e : ∀ c, {v // σ' v = c} ≃ {v // σ v = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [CKBridgeB_card_subtype, CKBridgeB_card_subtype]
      exact (h c).symm)
  refine ⟨(Equiv.sigmaFiberEquiv σ').symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv σ)), ?_⟩
  funext v
  simp only [Function.comp, Equiv.trans_apply]
  exact ((e (σ' v)) ⟨v, rfl⟩).2.symm

/-! ### Colour counts -/

private lemma CKBridgeB_fiberCard_update {n q : ℕ} (σ : Fin n → Fin q) (v : Fin n)
    (b c : Fin q) :
    (fiberCard (Function.update σ v b) c : ℝ) =
      fiberCard σ c - (if σ v = c then 1 else 0) + (if b = c then 1 else 0) := by
  rw [CKBridgeB_fiberCard_eq, CKBridgeB_fiberCard_eq,
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v),
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ v)]
  have hrest : ∑ w ∈ Finset.univ.erase v,
      (if Function.update σ v b w = c then (1 : ℝ) else 0) =
      ∑ w ∈ Finset.univ.erase v, (if σ w = c then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl fun w hw => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  rw [hrest, Function.update_self]
  ring

private lemma CKBridgeB_sum_fiberCard {n q : ℕ} (σ : Fin n → Fin q) :
    ∑ c, (fiberCard σ c : ℝ) = n := by
  simp_rw [CKBridgeB_fiberCard_eq]
  rw [Finset.sum_comm]
  simp

/-- Induction on `∑_c |N_c(σ) - N_c(σ')|`: recolour one vertex of an over-represented colour
into an under-represented one; equal counts are handled by a permutation. -/
private lemma CKBridgeB_count_induction {n q : ℕ} (g : (Fin n → Fin q) → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hstep : ∀ σ v b, |g σ - g (Function.update σ v b)| ≤ K)
    (hperm : ∀ σ (π : Equiv.Perm (Fin n)), g (σ ∘ π) = g σ) :
    ∀ k : ℕ, ∀ σ σ' : Fin n → Fin q, ∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| ≤ k →
      |g σ - g σ'| ≤ K * ∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| := by
  have heq : ∀ σ σ' : Fin n → Fin q, (∀ c, fiberCard σ c = fiberCard σ' c) →
      |g σ - g σ'| ≤ K * ∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| := by
    intro σ σ' h
    obtain ⟨π, hπ⟩ := CKBridgeB_exists_perm σ σ' h
    rw [hπ, hperm, sub_self, abs_zero]
    exact mul_nonneg hK (Finset.sum_nonneg fun c _ => abs_nonneg _)
  intro k
  induction k with
  | zero =>
    intro σ σ' hD
    apply heq
    intro c
    have h0 : ∀ c ∈ Finset.univ, |(fiberCard σ c : ℝ) - fiberCard σ' c| = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => abs_nonneg _)).mp
        (le_antisymm (by simpa using hD) (Finset.sum_nonneg fun c _ => abs_nonneg _))
    have := h0 c (Finset.mem_univ c)
    rw [abs_eq_zero, sub_eq_zero] at this
    exact_mod_cast this
  | succ k ih =>
    intro σ σ' hD
    by_cases hall : ∀ c, fiberCard σ c = fiberCard σ' c
    · exact heq σ σ' hall
    push Not at hall
    have hs := CKBridgeB_sum_fiberCard σ
    have hs' := CKBridgeB_sum_fiberCard σ'
    have ha : ∃ a, fiberCard σ' a < fiberCard σ a := by
      by_contra hcon
      push Not at hcon
      have hle : ∀ c ∈ Finset.univ, (fiberCard σ c : ℝ) ≤ fiberCard σ' c := fun c _ => by
        exact_mod_cast hcon c
      have := (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hs, hs'])
      obtain ⟨c, hc⟩ := hall
      exact hc (by exact_mod_cast this c (Finset.mem_univ c))
    have hb : ∃ b, fiberCard σ b < fiberCard σ' b := by
      by_contra hcon
      push Not at hcon
      have hle : ∀ c ∈ Finset.univ, (fiberCard σ' c : ℝ) ≤ fiberCard σ c := fun c _ => by
        exact_mod_cast hcon c
      have := (Finset.sum_eq_sum_iff_of_le hle).mp (by rw [hs, hs'])
      obtain ⟨c, hc⟩ := hall
      exact hc (by exact_mod_cast (this c (Finset.mem_univ c)).symm)
    obtain ⟨a, ha⟩ := ha
    obtain ⟨b, hb⟩ := hb
    have hab : a ≠ b := by
      rintro rfl
      omega
    have hpos : 0 < fiberCard σ a := by omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    have hva : σ v = a := by simpa using hv
    have ha' : (fiberCard σ' a : ℝ) + 1 ≤ fiberCard σ a := by exact_mod_cast ha
    have hb' : (fiberCard σ b : ℝ) + 1 ≤ fiberCard σ' b := by exact_mod_cast hb
    have hterm : ∀ c, |(fiberCard (Function.update σ v b) c : ℝ) - fiberCard σ' c| =
        |(fiberCard σ c : ℝ) - fiberCard σ' c| - (if a = c then 1 else 0) -
          (if b = c then 1 else 0) := by
      intro c
      rw [CKBridgeB_fiberCard_update, hva]
      by_cases hca : a = c
      · subst hca
        rw [if_pos rfl, if_neg hab.symm, abs_of_nonneg (by linarith),
          abs_of_nonneg (by linarith)]
        ring
      · by_cases hcb : b = c
        · subst hcb
          rw [if_neg hca, if_pos rfl, abs_of_nonpos (by linarith),
            abs_of_nonpos (by linarith)]
          ring
        · rw [if_neg hca, if_neg hcb]
          ring_nf
    have hD1 : ∑ c, |(fiberCard (Function.update σ v b) c : ℝ) - fiberCard σ' c| =
        ∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| - 2 := by
      rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      simp
      ring
    have hk : ∑ c, |(fiberCard (Function.update σ v b) c : ℝ) - fiberCard σ' c| ≤ k := by
      rw [hD1]
      push_cast at hD
      linarith
    have h1 := ih (Function.update σ v b) σ' hk
    rw [hD1] at h1
    have h2 := hstep σ v b
    calc |g σ - g σ'| = |(g σ - g (Function.update σ v b)) +
          (g (Function.update σ v b) - g σ')| := by ring_nf
      _ ≤ |g σ - g (Function.update σ v b)| + |g (Function.update σ v b) - g σ'| :=
          abs_add_le _ _
      _ ≤ K + K * (∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| - 2) := add_le_add h2 h1
      _ ≤ K * ∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| := by nlinarith

/-- Lemma 3.2(b)–(d): there is `L` such that `|g(σ, m) - g(σ', m)| ≤ L m ‖λ_σ - λ_{σ'}‖₁` for
all `n ≥ 1`, `σ, σ' ∈ [q]^n` and `m`; the proof gives `L = 8 ℓ₀ (m₊ - m₋)/m₋`.  In place of the
maximal coupling of Lemma 3.2(c), it uses a hybrid argument that changes the law of one edge at
a time. -/
theorem ck_g_lip {q : ℕ} {t : ℝ} (hp : CKPar q t) :
    ∃ L : ℝ, ∀ n : ℕ, 0 < n → ∀ (σ σ' : Fin n → Fin q) (m : ℕ),
      |ckg q t σ m - ckg q t σ' m| ≤ L * m * ∑ c, |colorFrac σ c - colorFrac σ' c| := by
  refine ⟨8 * ckEll q t * (ckMp t - ckMm q t) / ckMm q t, ?_⟩
  intro n hn σ σ' m
  obtain ⟨hm0, hm1, hp1, -, -, hell0, -⟩ := ck_const_bounds hp
  have hθ : 0 ≤ ckMp t - ckMm q t := by linarith
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hK0 : 0 ≤ (m : ℝ) * (2 * ckEll q t) * (4 * (ckMp t - ckMm q t) / (n * ckMm q t)) :=
    mul_nonneg (mul_nonneg hm (by linarith)) (div_nonneg (by linarith) (by positivity))
  have hstep : ∀ (τ : Fin n → Fin q) v b, |ckg q t τ m - ckg q t (Function.update τ v b) m| ≤
      (m : ℝ) * (2 * ckEll q t) * (4 * (ckMp t - ckMm q t) / (n * ckMm q t)) := by
    intro τ v b
    rw [CKBridgeB_ckg_eq, CKBridgeB_ckg_eq]
    refine (CKBridgeB_PE_hybrid (CKBridgeB_p_nonneg hp hn τ) (CKBridgeB_p_nonneg hp hn _)
      (CKBridgeB_p_sum hp hn τ) (CKBridgeB_p_sum hp hn _) m _
      (fun e k x => CKBridgeB_log_update hp e k x)).trans ?_
    exact mul_le_mul_of_nonneg_left (CKBridgeB_p_update hp hn τ v b)
      (mul_nonneg hm (by linarith))
  have hperm : ∀ (τ : Fin n → Fin q) (π : Equiv.Perm (Fin n)),
      ckg q t (τ ∘ π) m = ckg q t τ m := fun τ π => CKBridgeB_ckg_perm t τ π m
  have hmain := CKBridgeB_count_induction (fun τ => ckg q t τ m) hK0 hstep hperm
    ⌈∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c|⌉₊ σ σ' (Nat.le_ceil _)
  have hDeq : ∑ c, |(fiberCard σ c : ℝ) - fiberCard σ' c| =
      n * ∑ c, |colorFrac σ c - colorFrac σ' c| := by
    unfold colorFrac
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← sub_div, abs_div, abs_of_pos hnr, mul_div_cancel₀ _ hnr.ne']
  refine hmain.trans (le_of_eq ?_)
  rw [hDeq]
  field_simp
  ring

/-! ### Lemma 3.3: auxiliary facts -/

/-- `‖λ_σ - u‖₁`. -/
private def CKBridgeB_dev {n q : ℕ} (σ : Fin n → Fin q) : ℝ :=
  ∑ c, |colorFrac σ c - 1 / (q : ℝ)|

private lemma CKBridgeB_dev_nonneg {n q : ℕ} (σ : Fin n → Fin q) : 0 ≤ CKBridgeB_dev σ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma CKBridgeB_colorFrac_l1_le {n q : ℕ} (σ σ' : Fin n → Fin q) :
    ∑ c, |colorFrac σ c - colorFrac σ' c| ≤ CKBridgeB_dev σ + CKBridgeB_dev σ' := by
  unfold CKBridgeB_dev
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  refine (abs_sub_le _ (1 / (q : ℝ)) _).trans (le_of_eq ?_)
  rw [abs_sub_comm (1 / (q : ℝ))]

private lemma CKBridgeB_card_fun (q n : ℕ) :
    ((Finset.univ : Finset (Fin n → Fin q)).card : ℝ) = (q : ℝ) ^ n := by
  simp

private lemma CKBridgeB_tele {f : ℕ → ℝ} {B : ℝ} (hf : ∀ k, |f (k + 1) - f k| ≤ B) (m d : ℕ) :
    |f (m + d) - f m| ≤ B * d := by
  induction d with
  | zero => simp
  | succ d ih =>
    calc |f (m + (d + 1)) - f m| = |(f (m + d + 1) - f (m + d)) + (f (m + d) - f m)| := by
          rw [show m + (d + 1) = m + d + 1 from rfl]
          ring_nf
      _ ≤ |f (m + d + 1) - f (m + d)| + |f (m + d) - f m| := abs_add_le _ _
      _ ≤ B + B * d := add_le_add (hf _) ih
      _ = B * ((d + 1 : ℕ) : ℝ) := by push_cast; ring

private lemma CKBridgeB_tele_abs {f : ℕ → ℝ} {B : ℝ} (hf : ∀ k, |f (k + 1) - f k| ≤ B)
    (m m' : ℕ) : |f m - f m'| ≤ B * |(m : ℝ) - m'| := by
  rcases le_total m m' with h | h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : ((m : ℝ) - ((m + d : ℕ) : ℝ)) = -(d : ℝ) := by push_cast; ring
    rw [abs_sub_comm, e, abs_neg, Nat.abs_cast]
    exact CKBridgeB_tele hf m d
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (((m' + d : ℕ) : ℝ) - (m' : ℝ)) = (d : ℝ) := by push_cast; ring
    rw [e, Nat.abs_cast]
    exact CKBridgeB_tele hf m' d

/-- Averaging a pointwise bound over a finite index set with weights `Q` (`Q · #ι = 1`). -/
private lemma CKBridgeB_avg_bound {ι : Type*} [Fintype ι] {F d gap : ι → ℝ}
    {g₀ Q K A E ℓ : ℝ} (hQ : Q * (Fintype.card ι : ℝ) = 1) (hQ0 : 0 ≤ Q)
    (hF : ∀ i, |F i - g₀| ≤ K * (d i + A) + E + ℓ * gap i) :
    |Q * ∑ i, F i - g₀| ≤ K * (Q * ∑ i, d i) + K * A + E + ℓ * (Q * ∑ i, gap i) := by
  have hrw : Q * ∑ i, F i - g₀ = Q * ∑ i, (F i - g₀) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_sub,
      ← mul_assoc, hQ, one_mul]
  rw [hrw, abs_mul, abs_of_nonneg hQ0]
  calc Q * |∑ i, (F i - g₀)| ≤ Q * ∑ i, (K * (d i + A) + E + ℓ * gap i) :=
        mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hF i)) hQ0
    _ = K * (Q * ∑ i, d i) + (K * A + E) * (Q * (Fintype.card ι : ℝ)) +
          ℓ * (Q * ∑ i, gap i) := by
        have e : ∀ i, K * (d i + A) + E + ℓ * gap i = K * d i + (K * A + E) + ℓ * gap i :=
          fun i => by ring
        rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
        ring
    _ = K * (Q * ∑ i, d i) + K * A + E + ℓ * (Q * ∑ i, gap i) := by rw [hQ]; ring

/-- `|g(σ,m) - ḡ| ≤ L m (‖λ_σ - u‖₁ + E‖λ - u‖₁) + ℓ₀ |m - m₀|`, `ḡ = E_σ' g(σ', m₀)`. -/
private lemma CKBridgeB_ref_bound {q n : ℕ} {t L : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (hlip : ∀ (σ σ' : Fin n → Fin q) (m : ℕ),
      |ckg q t σ m - ckg q t σ' m| ≤ L * m * ∑ c, |colorFrac σ c - colorFrac σ' c|)
    (hL : 0 ≤ L) (σ : Fin n → Fin q) (m m₀ : ℕ) :
    |ckg q t σ m - ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, ckg q t σ' m₀| ≤
      L * m * (CKBridgeB_dev σ + ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, CKBridgeB_dev σ') +
        ckEll q t * |(m : ℝ) - m₀| := by
  have hq2 := hp.two_le
  have hqpos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hQ : ((q : ℝ) ^ n)⁻¹ * (Fintype.card (Fin n → Fin q) : ℝ) = 1 := by
    rw [← Finset.card_univ, CKBridgeB_card_fun, inv_mul_cancel₀ hqpos.ne']
  have hpt : ∀ σ' : Fin n → Fin q, |ckg q t σ m - ckg q t σ' m₀| ≤
      L * m * (CKBridgeB_dev σ + CKBridgeB_dev σ') + ckEll q t * |(m : ℝ) - m₀| := by
    intro σ'
    have h1 := hlip σ σ' m
    have h2 := CKBridgeB_tele_abs (f := fun k => ckg q t σ' k)
      (fun k => ck_g_succ hp hn σ' k) m m₀
    have h3 := CKBridgeB_colorFrac_l1_le σ σ'
    have hLm : 0 ≤ L * m := mul_nonneg hL (Nat.cast_nonneg m)
    calc |ckg q t σ m - ckg q t σ' m₀|
        ≤ |ckg q t σ m - ckg q t σ' m| + |ckg q t σ' m - ckg q t σ' m₀| := abs_sub_le _ _ _
      _ ≤ L * m * ∑ c, |colorFrac σ c - colorFrac σ' c| + ckEll q t * |(m : ℝ) - m₀| :=
          add_le_add h1 h2
      _ ≤ L * m * (CKBridgeB_dev σ + CKBridgeB_dev σ') + ckEll q t * |(m : ℝ) - m₀| := by
          gcongr
  have hQ' : ((q : ℝ) ^ n)⁻¹ * ((Finset.univ : Finset (Fin n → Fin q)).card : ℝ) = 1 := by
    rw [CKBridgeB_card_fun, inv_mul_cancel₀ hqpos.ne']
  have hrw : ckg q t σ m - ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, ckg q t σ' m₀ =
      ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, (ckg q t σ m - ckg q t σ' m₀) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub, ← mul_assoc, hQ',
      one_mul]
  rw [hrw, abs_mul, abs_of_pos (inv_pos.mpr hqpos)]
  calc ((q : ℝ) ^ n)⁻¹ * |∑ σ' : Fin n → Fin q, (ckg q t σ m - ckg q t σ' m₀)|
      ≤ ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q,
          (L * m * (CKBridgeB_dev σ + CKBridgeB_dev σ') + ckEll q t * |(m : ℝ) - m₀|) :=
        mul_le_mul_of_nonneg_left
          ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ' _ => hpt σ'))
          (inv_pos.mpr hqpos).le
    _ = L * m * (CKBridgeB_dev σ + ((q : ℝ) ^ n)⁻¹ * ∑ σ' : Fin n → Fin q, CKBridgeB_dev σ') +
          ckEll q t * |(m : ℝ) - m₀| := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
          ← Finset.mul_sum]
        linear_combination (L * m * CKBridgeB_dev σ + ckEll q t * |(m : ℝ) - m₀|) * hQ'

private lemma CKBridgeB_dev_sq_le {n q : ℕ} (σ : Fin n → Fin q) :
    CKBridgeB_dev σ ^ 2 ≤ q * rsDevSq σ := by
  unfold CKBridgeB_dev rsDevSq
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q)))
    (f := fun c => |colorFrac σ c - 1 / (q : ℝ)|)
  simp only [sq_abs, Finset.card_univ, Fintype.card_fin] at this
  exact this

private lemma CKBridgeB_avg_dev {q n : ℕ} (hq : 2 ≤ q) (hn : 0 < n) :
    ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, CKBridgeB_dev σ ≤ Real.sqrt q / Real.sqrt n := by
  have hqpos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  have hq0 : (0 : ℝ) < q := by positivity
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hA0 : 0 ≤ ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, CKBridgeB_dev σ :=
    mul_nonneg (inv_pos.mpr hqpos).le (Finset.sum_nonneg fun σ _ => CKBridgeB_dev_nonneg σ)
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → Fin q)))
    (f := fun σ => CKBridgeB_dev σ)
  rw [CKBridgeB_card_fun] at hCS
  have hsq : ∑ σ : Fin n → Fin q, CKBridgeB_dev σ ^ 2 ≤ q * ∑ σ : Fin n → Fin q, rsDevSq σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ => CKBridgeB_dev_sq_le σ
  have havg := ck_avg_devSq (q := q) (n := n) (by omega) (by omega)
  have hsum : ∑ σ : Fin n → Fin q, rsDevSq σ = (q : ℝ) ^ n * (((q : ℝ) - 1) / (q * n)) := by
    rw [← havg, ← mul_assoc, mul_inv_cancel₀ hqpos.ne', one_mul]
  have hA2 : (((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, CKBridgeB_dev σ) ^ 2 ≤ q / n := by
    rw [mul_pow]
    calc ((q : ℝ) ^ n)⁻¹ ^ 2 * (∑ σ : Fin n → Fin q, CKBridgeB_dev σ) ^ 2
        ≤ ((q : ℝ) ^ n)⁻¹ ^ 2 *
            ((q : ℝ) ^ n * (q * ((q : ℝ) ^ n * (((q : ℝ) - 1) / (q * n))))) := by
          gcongr
          calc (∑ σ : Fin n → Fin q, CKBridgeB_dev σ) ^ 2
              ≤ (q : ℝ) ^ n * ∑ σ : Fin n → Fin q, CKBridgeB_dev σ ^ 2 := hCS
            _ ≤ (q : ℝ) ^ n * (q * ∑ σ : Fin n → Fin q, rsDevSq σ) := by gcongr
            _ = _ := by rw [hsum]
      _ = ((q : ℝ) - 1) / n := by
          field_simp
      _ ≤ q / n := by gcongr; linarith
  have h := Real.abs_le_sqrt hA2
  rw [abs_of_nonneg hA0, Real.sqrt_div' _ hnr.le] at h
  exact h

private lemma CKBridgeB_hasSum_mean {lam : ℝ} (hlam : 0 ≤ lam) :
    HasSum (fun k : ℕ => poisPMF lam k * (k : ℝ)) lam := by
  have hs : Summable (fun k : ℕ => poisPMF lam k * (k : ℝ)) := by
    simpa using summable_poisPMF_mul_pow hlam 1
  have h := hs.hasSum
  have he : ∑' k : ℕ, poisPMF lam k * (k : ℝ) = lam := poisExp_natCast hlam
  rwa [he] at h

private lemma CKBridgeB_pois_tilt (lam y : ℝ) (k : ℕ) :
    poisPMF lam k * y ^ k = Real.exp (lam * (y - 1)) * poisPMF (lam * y) k := by
  unfold poisPMF
  have h : Real.exp (-lam) = Real.exp (lam * (y - 1)) * Real.exp (-(lam * y)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h, mul_pow]
  ring

private lemma CKBridgeB_hasSum_tilt {lam y : ℝ} (hlam : 0 ≤ lam) (hy : 0 ≤ y) :
    HasSum (fun k : ℕ => poisPMF lam k * ((k : ℝ) * y ^ k))
      (lam * y * Real.exp (lam * (y - 1))) := by
  have h := (CKBridgeB_hasSum_mean (mul_nonneg hlam hy)).mul_left (Real.exp (lam * (y - 1)))
  have hf : (fun k : ℕ => poisPMF lam k * ((k : ℝ) * y ^ k)) =
      fun k => Real.exp (lam * (y - 1)) * (poisPMF (lam * y) k * k) := by
    funext k
    rw [show poisPMF lam k * ((k : ℝ) * y ^ k) = (k : ℝ) * (poisPMF lam k * y ^ k) by ring,
      CKBridgeB_pois_tilt]
    ring
  rw [hf, show lam * y * Real.exp (lam * (y - 1)) = Real.exp (lam * (y - 1)) * (lam * y) by ring]
  exact h

/-- A Poisson average of `c` stays within the Poisson average of a pointwise bound of
`|c - g₀|`. -/
private lemma CKBridgeB_pois_series {lam y ℓ a b δ g₀ : ℝ} (hlam : 0 ≤ lam) (hy : 0 ≤ y)
    {c : ℕ → ℝ}
    (hc : ∀ m : ℕ, |c m - g₀| ≤ a * ((m : ℝ) * y ^ m) + b * m + ℓ * (|(m : ℝ) - lam| + δ))
    (hℓ : 0 ≤ ℓ) :
    Summable (fun m => poisPMF lam m * c m) ∧
      |∑' m, poisPMF lam m * c m - g₀| ≤
        a * (lam * y * Real.exp (lam * (y - 1))) + b * lam + ℓ * (Real.sqrt lam + δ) := by
  have hP := hasSum_poisPMF hlam
  have hP0 := poisPMF_nonneg hlam
  have hS := (summable_poisPMF_mul_abs_sub hlam).hasSum
  have hSle : ∑' k : ℕ, poisPMF lam k * |(k : ℝ) - lam| ≤ Real.sqrt lam :=
    poisExp_abs_sub_le hlam
  have hB : HasSum
      (fun m : ℕ => poisPMF lam m * (a * ((m : ℝ) * y ^ m) + b * m + ℓ * (|(m : ℝ) - lam| + δ)))
      (a * (lam * y * Real.exp (lam * (y - 1))) + b * lam +
        ℓ * (∑' k : ℕ, poisPMF lam k * |(k : ℝ) - lam| + δ)) := by
    have := (((CKBridgeB_hasSum_tilt hlam hy).mul_left a).add
      ((CKBridgeB_hasSum_mean hlam).mul_left b)).add ((hS.add (hP.mul_right δ)).mul_left ℓ)
    have hf : (fun m : ℕ => poisPMF lam m *
        (a * ((m : ℝ) * y ^ m) + b * m + ℓ * (|(m : ℝ) - lam| + δ))) =
        fun m : ℕ => a * (poisPMF lam m * ((m : ℝ) * y ^ m)) + b * (poisPMF lam m * m) +
          ℓ * (poisPMF lam m * |(m : ℝ) - lam| + poisPMF lam m * δ) := by
      funext m
      ring
    rw [hf, show a * (lam * y * Real.exp (lam * (y - 1))) + b * lam +
        ℓ * (∑' k : ℕ, poisPMF lam k * |(k : ℝ) - lam| + δ) =
        a * (lam * y * Real.exp (lam * (y - 1))) + b * lam +
        ℓ * (∑' k : ℕ, poisPMF lam k * |(k : ℝ) - lam| + 1 * δ) by ring]
    exact this
  have hbd : ∀ m, ‖poisPMF lam m * (c m - g₀)‖ ≤
      poisPMF lam m * (a * ((m : ℝ) * y ^ m) + b * m + ℓ * (|(m : ℝ) - lam| + δ)) := by
    intro m
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hP0 m)]
    exact mul_le_mul_of_nonneg_left (hc m) (hP0 m)
  have hsum1 : Summable (fun m => poisPMF lam m * (c m - g₀)) :=
    Summable.of_norm_bounded hB.summable hbd
  have hsum2 : Summable (fun m => poisPMF lam m * c m) := by
    have := hsum1.add (hP.summable.mul_right g₀)
    have hf : (fun m => poisPMF lam m * c m) =
        fun m => poisPMF lam m * (c m - g₀) + poisPMF lam m * g₀ := by
      funext m
      ring
    rw [hf]
    exact this
  refine ⟨hsum2, ?_⟩
  have heq : ∑' m, poisPMF lam m * c m - g₀ = ∑' m, poisPMF lam m * (c m - g₀) := by
    have h3 := hsum2.hasSum.sub (hP.mul_right g₀)
    rw [one_mul] at h3
    rw [← h3.tsum_eq]
    congr 1
    funext m
    ring
  rw [heq]
  have h4 := tsum_of_norm_bounded hB hbd
  rw [Real.norm_eq_abs] at h4
  refine h4.trans ?_
  gcongr

/-- Mixture bound for the tilted colouring law `ν_m`. -/
private lemma CKBridgeB_mix_bound {ι : Type*} [Fintype ι] {ν G d : ι → ℝ} {g₀ Q K A E Y : ℝ}
    (hν0 : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) (hνle : ∀ i, ν i ≤ Q * Y)
    (hd0 : ∀ i, 0 ≤ d i) (hK : 0 ≤ K) (hG : ∀ i, |G i - g₀| ≤ K * (d i + A) + E) :
    |∑ i, ν i * G i - g₀| ≤ K * (Y * (Q * ∑ i, d i)) + K * A + E := by
  have hrw : ∑ i, ν i * G i - g₀ = ∑ i, ν i * (G i - g₀) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hν1, one_mul]
  rw [hrw]
  have h1 : ∑ i, ν i * d i ≤ Y * (Q * ∑ i, d i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hνle i) (hd0 i)).trans (le_of_eq (by ring))
  calc |∑ i, ν i * (G i - g₀)| ≤ ∑ i, ν i * (K * (d i + A) + E) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (hν0 i)]
        exact mul_le_mul_of_nonneg_left (hG i) (hν0 i)
    _ = K * ∑ i, ν i * d i + (K * A + E) * ∑ i, ν i := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ K * (Y * (Q * ∑ i, d i)) + K * A + E := by
        rw [hν1, mul_one]
        have := mul_le_mul_of_nonneg_left h1 hK
        linarith

private lemma CKBridgeB_Z_eq {q n : ℕ} (t : ℝ) (σ : Fin n → Fin q) :
    ckZ1 q t σ = (n : ℝ) ^ 2 + ckS q t σ := by
  unfold ckZ1 ckS
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

private lemma CKBridgeB_avg_gap {q n : ℕ} {t s : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (hs : 0 ≤ s) :
    ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, (s * n / 2 - s * ckZ1 q t σ / (2 * n)) ≤ s / 2 := by
  have hq2 := hp.two_le
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < q := by positivity
  have e : ∀ σ : Fin n → Fin q, s * n / 2 - s * ckZ1 q t σ / (2 * n) =
      -(s * t * q * n / 2) * rsDevSq σ := by
    intro σ
    rw [CKBridgeB_Z_eq, ck_S_eq (by omega)]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun σ _ => e σ, ← Finset.mul_sum, mul_left_comm,
    ck_avg_devSq (by omega) (by omega)]
  have hgt := hp.gt
  have h2 : -(s * t * q * n / 2) * (((q : ℝ) - 1) / (q * n)) = -(s * (t * ((q : ℝ) - 1))) / 2 := by
    field_simp
  rw [h2]
  nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ 1 + t * ((q : ℝ) - 1))]

private lemma CKBridgeB_nu_sum {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) (m : ℕ) :
    ∑ σ : Fin n → Fin q, ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) = 1 := by
  have hq2 := hp.two_le
  have : Nonempty (Fin n → Fin q) := ⟨fun _ => ⟨0, by omega⟩⟩
  have hS : 0 < ∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m :=
    Finset.sum_pos (fun σ' _ => pow_pos (CKBridgeB_Z_pos hp hn σ') m) Finset.univ_nonempty
  rw [← Finset.sum_div, div_self hS.ne']

private lemma CKBridgeB_nu_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (σ : Fin n → Fin q) (m : ℕ) :
    0 ≤ ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) :=
  div_nonneg (pow_pos (CKBridgeB_Z_pos hp hn σ) m).le
    (Finset.sum_nonneg fun σ' _ => (pow_pos (CKBridgeB_Z_pos hp hn σ') m).le)

/-- The final arithmetic of Lemma 3.3. -/
private lemma CKBridgeB_combine {L A ℓ s X Y g₀ : ℝ} {n q : ℕ} (hn2 : 2 ≤ n) (hs : 0 < s)
    (hL : 0 ≤ L) (hA0 : 0 ≤ A) (hℓ0 : 0 ≤ ℓ) (hAle : A ≤ Real.sqrt q / Real.sqrt n)
    (hlit : |X - g₀| ≤ L * A * (s * n / 2 * (1 - (n : ℝ)⁻¹)⁻¹ *
        Real.exp (s * n / 2 * ((1 - (n : ℝ)⁻¹)⁻¹ - 1))) + L * A * (s * n / 2) +
        ℓ * (Real.sqrt (s * n / 2) + 1))
    (hpl : |Y - g₀| ≤ 2 * L * (s * n / 2) * A + ℓ * (Real.sqrt (s * n / 2) + 1) + ℓ * (s / 2)) :
    |X - Y| ≤ (L * Real.sqrt q * (s * Real.exp s + 2 * s) + ℓ * (2 * Real.sqrt s + s + 2)) *
      Real.sqrt n := by
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  set Λ := s * n / 2 with hΛdef
  set y := (1 - (n : ℝ)⁻¹)⁻¹ with hydef
  have hyv : y = n / (n - 1) := by
    rw [hydef]
    field_simp
  have hr0 := Real.sqrt_nonneg (n : ℝ)
  have hr1 : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    linarith
  have hrr : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
  have hrpos : 0 < Real.sqrt n := by linarith
  have hAn : A * n ≤ Real.sqrt q * Real.sqrt n := by
    calc A * n ≤ Real.sqrt q / Real.sqrt n * n := mul_le_mul_of_nonneg_right hAle hnpos.le
      _ = Real.sqrt q / Real.sqrt n * (Real.sqrt n * Real.sqrt n) := by rw [hrr]
      _ = Real.sqrt q * Real.sqrt n := by field_simp
  have hT : Λ * y * Real.exp (Λ * (y - 1)) ≤ s * Real.exp s * n := by
    have hy2 : y ≤ 2 := by
      rw [hyv, div_le_iff₀ hn1]
      linarith
    have hΛy : Λ * (y - 1) ≤ s := by
      have e : Λ * (y - 1) = s * n / (2 * (n - 1)) := by
        rw [hΛdef, hyv]
        field_simp
        ring
      rw [e, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left (show (n : ℝ) ≤ 2 * (n - 1) by linarith) hs.le
      linarith
    have he : Real.exp (Λ * (y - 1)) ≤ Real.exp s := Real.exp_le_exp.mpr hΛy
    have hΛy2 : Λ * y ≤ s * n := by
      calc Λ * y ≤ Λ * 2 := mul_le_mul_of_nonneg_left hy2 (by positivity)
        _ = s * n := by rw [hΛdef]; ring
    calc Λ * y * Real.exp (Λ * (y - 1)) ≤ (s * n) * Real.exp s :=
          mul_le_mul hΛy2 he (Real.exp_pos _).le (by positivity)
      _ = s * Real.exp s * n := by ring
  have hsqΛ : Real.sqrt Λ ≤ Real.sqrt s * Real.sqrt n := by
    rw [← Real.sqrt_mul hs.le]
    refine Real.sqrt_le_sqrt ?_
    rw [hΛdef]
    have : 0 ≤ s * n := by positivity
    linarith
  have hcomb := abs_sub_le X g₀ Y
  rw [abs_sub_comm g₀ Y] at hcomb
  have T1 : L * A * (Λ * y * Real.exp (Λ * (y - 1))) ≤
      L * s * Real.exp s * (Real.sqrt q * Real.sqrt n) := by
    calc L * A * (Λ * y * Real.exp (Λ * (y - 1))) ≤ L * A * (s * Real.exp s * n) :=
          mul_le_mul_of_nonneg_left hT (mul_nonneg hL hA0)
      _ = L * s * Real.exp s * (A * n) := by ring
      _ ≤ L * s * Real.exp s * (Real.sqrt q * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hAn (by positivity)
  have T2 : L * A * Λ ≤ L * (s / 2) * (Real.sqrt q * Real.sqrt n) := by
    calc L * A * Λ = L * (s / 2) * (A * n) := by rw [hΛdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAn (by positivity)
  have T3 : 2 * L * Λ * A ≤ L * s * (Real.sqrt q * Real.sqrt n) := by
    calc 2 * L * Λ * A = L * s * (A * n) := by rw [hΛdef]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAn (by positivity)
  have T4 : ℓ * (Real.sqrt Λ + 1) ≤ ℓ * (Real.sqrt s * Real.sqrt n + Real.sqrt n) := by
    gcongr
  have T5 : ℓ * (s / 2) ≤ ℓ * (s * Real.sqrt n) := by
    gcongr
    have := mul_le_mul_of_nonneg_left hr1 hs.le
    linarith
  have T6 : 0 ≤ L * s * (Real.sqrt q * Real.sqrt n) := by positivity
  have E : (L * Real.sqrt q * (s * Real.exp s + 2 * s) + ℓ * (2 * Real.sqrt s + s + 2)) *
      Real.sqrt n = L * s * Real.exp s * (Real.sqrt q * Real.sqrt n) +
        2 * (L * s * (Real.sqrt q * Real.sqrt n)) +
        2 * (ℓ * (Real.sqrt s * Real.sqrt n + Real.sqrt n)) + ℓ * (s * Real.sqrt n) := by
    ring
  have E2 : L * (s / 2) * (Real.sqrt q * Real.sqrt n) =
      (1 / 2) * (L * s * (Real.sqrt q * Real.sqrt n)) := by ring
  rw [E]
  linarith

/-- Lemma 3.3 for a general parameter `t`, with the two representations of Lemma 3.1(b),(c)
as hypotheses. -/
private lemma CKBridgeB_core {q n : ℕ} {t s L : ℝ} (hp : CKPar q t) (hn2 : 2 ≤ n) (hs : 0 < s)
    (hL : 0 ≤ L)
    (hlip : ∀ (σ σ' : Fin n → Fin q) (m : ℕ),
      |ckg q t σ m - ckg q t σ' m| ≤ L * m * ∑ c, |colorFrac σ c - colorFrac σ' c|)
    (c : ℕ → ℝ)
    (hc : ∀ m, c m = ∑ σ : Fin n → Fin q,
      ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m) * ckg q t σ m)
    (fbar : ℝ)
    (hfbar : fbar = ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
      ∑' m : ℕ, poisPMF (s * ckZ1 q t σ / (2 * n)) m * ckg q t σ m) :
    Summable (fun m : ℕ => poisPMF (s * n / 2) m * c m) ∧
      |∑' m : ℕ, poisPMF (s * n / 2) m * c m - fbar| ≤
        (L * Real.sqrt q * (s * Real.exp s + 2 * s) + ckEll q t * (2 * Real.sqrt s + s + 2)) *
          Real.sqrt n := by
  have hn : 0 < n := by omega
  have hq2 := hp.two_le
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hqpos : (0 : ℝ) < (q : ℝ) ^ n := by positivity
  obtain ⟨hm0, hm1, hmp1, -, -, hℓ0, -⟩ := ck_const_bounds hp
  set ℓ := ckEll q t with hℓdef
  set Q := ((q : ℝ) ^ n)⁻¹ with hQdef
  have hQ0 : 0 ≤ Q := (inv_pos.mpr hqpos).le
  have hQcard : Q * (Fintype.card (Fin n → Fin q) : ℝ) = 1 := by
    rw [← Finset.card_univ, CKBridgeB_card_fun, hQdef, inv_mul_cancel₀ hqpos.ne']
  set Λ := s * n / 2 with hΛdef
  have hΛ0 : 0 ≤ Λ := by positivity
  set m₀ := ⌊Λ⌋₊ with hm₀def
  have hm₀ : |Λ - m₀| ≤ 1 := by
    have h1 := Nat.floor_le hΛ0
    have h2 := Nat.lt_floor_add_one Λ
    rw [abs_le]
    constructor <;> linarith
  set A := Q * ∑ σ : Fin n → Fin q, CKBridgeB_dev σ with hAdef
  have hA0 : 0 ≤ A := mul_nonneg hQ0 (Finset.sum_nonneg fun σ _ => CKBridgeB_dev_nonneg σ)
  have hAle : A ≤ Real.sqrt q / Real.sqrt n := CKBridgeB_avg_dev hq2 hn
  set g₀ := Q * ∑ σ : Fin n → Fin q, ckg q t σ m₀ with hg₀def
  set y := (1 - (n : ℝ)⁻¹)⁻¹ with hydef
  have hn1 : (0 : ℝ) < n - 1 := by linarith
  have hyv : y = n / (n - 1) := by
    rw [hydef]
    field_simp
  have hy0 : 0 ≤ y := by
    rw [hyv]
    positivity
  have href : ∀ (σ : Fin n → Fin q) (m : ℕ),
      |ckg q t σ m - g₀| ≤ L * m * (CKBridgeB_dev σ + A) + ℓ * |(m : ℝ) - m₀| :=
    fun σ m => CKBridgeB_ref_bound hp hn hlip hL σ m m₀
  -- the literal side
  have hlitc : ∀ m : ℕ, |c m - g₀| ≤
      (L * A) * ((m : ℝ) * y ^ m) + (L * A) * m + ℓ * (|(m : ℝ) - Λ| + 1) := by
    intro m
    rw [hc m]
    have hmix := CKBridgeB_mix_bound
      (ν := fun σ : Fin n → Fin q => ckZ1 q t σ ^ m / (∑ σ' : Fin n → Fin q, ckZ1 q t σ' ^ m))
      (G := fun σ => ckg q t σ m) (d := CKBridgeB_dev) (g₀ := g₀) (Q := Q) (K := L * m)
      (A := A) (E := ℓ * |(m : ℝ) - m₀|) (Y := y ^ m)
      (fun σ => CKBridgeB_nu_nonneg hp hn σ m) (CKBridgeB_nu_sum hp hn m)
      (fun σ => by
        have := ck_nu_le hp hn2 σ m
        rwa [← inv_pow (1 - (n : ℝ)⁻¹) m] at this)
      CKBridgeB_dev_nonneg (mul_nonneg hL (Nat.cast_nonneg m)) (fun σ => href σ m)
    rw [← hAdef] at hmix
    refine hmix.trans ?_
    have hmm : |(m : ℝ) - m₀| ≤ |(m : ℝ) - Λ| + 1 := by
      calc |(m : ℝ) - m₀| ≤ |(m : ℝ) - Λ| + |Λ - m₀| := abs_sub_le _ _ _
        _ ≤ |(m : ℝ) - Λ| + 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hmm hℓ0.le
    have h2 : L * m * (y ^ m * A) = L * A * (m * y ^ m) := by ring
    have h3 : L * m * A = L * A * m := by ring
    linarith
  obtain ⟨hsum, hlit⟩ := CKBridgeB_pois_series hΛ0 hy0 hlitc hℓ0.le
  refine ⟨hsum, ?_⟩
  -- the planted side
  have hZle : ∀ σ : Fin n → Fin q, ckZ1 q t σ ≤ (n : ℝ) ^ 2 := fun σ => by
    rw [CKBridgeB_Z_eq]
    linarith [(ck_S_mem hp σ).2]
  have hpl : ∀ σ : Fin n → Fin q,
      |∑' m : ℕ, poisPMF (s * ckZ1 q t σ / (2 * n)) m * ckg q t σ m - g₀| ≤
        L * Λ * (CKBridgeB_dev σ + A) + ℓ * (Real.sqrt Λ + 1) +
          ℓ * (Λ - s * ckZ1 q t σ / (2 * n)) := by
    intro σ
    have hZσ := CKBridgeB_Z_pos hp hn σ
    have hlam0 : 0 ≤ s * ckZ1 q t σ / (2 * n) := by positivity
    have hlamΛ : s * ckZ1 q t σ / (2 * n) ≤ Λ := by
      rw [hΛdef, div_le_div_iff₀ (by positivity) (by positivity)]
      have := hZle σ
      have h1 : s * ckZ1 q t σ ≤ s * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left this hs.le
      nlinarith
    have hcσ : ∀ m : ℕ, |ckg q t σ m - g₀| ≤ 0 * ((m : ℝ) * 1 ^ m) +
        (L * (CKBridgeB_dev σ + A)) * m +
          ℓ * (|(m : ℝ) - s * ckZ1 q t σ / (2 * n)| + ((Λ - s * ckZ1 q t σ / (2 * n)) + 1)) := by
      intro m
      have h1 := href σ m
      have hmm : |(m : ℝ) - m₀| ≤
          |(m : ℝ) - s * ckZ1 q t σ / (2 * n)| + ((Λ - s * ckZ1 q t σ / (2 * n)) + 1) := by
        have ha := abs_sub_le (m : ℝ) (s * ckZ1 q t σ / (2 * n)) m₀
        have hb := abs_sub_le (s * ckZ1 q t σ / (2 * n)) Λ m₀
        have hc' : |s * ckZ1 q t σ / (2 * n) - Λ| = Λ - s * ckZ1 q t σ / (2 * n) := by
          rw [abs_of_nonpos (by linarith)]
          ring
        linarith
      have h2 := mul_le_mul_of_nonneg_left hmm hℓ0.le
      have h3 : L * m * (CKBridgeB_dev σ + A) = L * (CKBridgeB_dev σ + A) * m := by ring
      linarith
    obtain ⟨-, hb⟩ := CKBridgeB_pois_series hlam0 zero_le_one hcσ hℓ0.le
    refine hb.trans ?_
    have h1 : Real.sqrt (s * ckZ1 q t σ / (2 * n)) ≤ Real.sqrt Λ := Real.sqrt_le_sqrt hlamΛ
    have h2 : L * (CKBridgeB_dev σ + A) * (s * ckZ1 q t σ / (2 * n)) ≤
        L * (CKBridgeB_dev σ + A) * Λ :=
      mul_le_mul_of_nonneg_left hlamΛ
        (mul_nonneg hL (add_nonneg (CKBridgeB_dev_nonneg σ) hA0))
    have h3 := mul_le_mul_of_nonneg_left h1 hℓ0.le
    have h4 : L * Λ * (CKBridgeB_dev σ + A) = L * (CKBridgeB_dev σ + A) * Λ := by ring
    nlinarith
  have hplbound : |fbar - g₀| ≤ 2 * L * Λ * A + ℓ * (Real.sqrt Λ + 1) + ℓ * (s / 2) := by
    rw [hfbar]
    have hav := CKBridgeB_avg_bound
      (F := fun σ => ∑' m : ℕ, poisPMF (s * ckZ1 q t σ / (2 * n)) m * ckg q t σ m)
      (d := CKBridgeB_dev) (gap := fun σ => Λ - s * ckZ1 q t σ / (2 * n)) (g₀ := g₀) (Q := Q)
      (K := L * Λ) (A := A) (E := ℓ * (Real.sqrt Λ + 1)) (ℓ := ℓ) hQcard hQ0 hpl
    rw [← hAdef] at hav
    refine hav.trans ?_
    have hgap := CKBridgeB_avg_gap hp hn hs.le
    rw [← hQdef, ← hΛdef] at hgap
    have h1 := mul_le_mul_of_nonneg_left hgap hℓ0.le
    have h2 : L * Λ * A + L * Λ * A = 2 * L * Λ * A := by ring
    linarith
  -- combine
  exact CKBridgeB_combine hn2 hs hL hA0 hℓ0.le hAle hlit hplbound

/-- Lemma 3.3 (bridge): for `q ≥ 2`, `x ∈ (0,1)` and `s > 0` there is `C` such that for every
`n ≥ 2` the series `f^lit_n = ∑_m Pois(sn/2)(m) c̄_m(n)` is summable and
`|f^lit_n - f̄_n| ≤ C √n`, where `f̄_n` is taken at `t = t(x)`.  The proof gives
`C = L √q (s e^s + 2s) + ℓ₀ (2√s + s + 2)`, with `L ≥ 0` the constant of Lemma 3.2. -/
theorem ck_bridge {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) {s : ℝ}
    (hs : 0 < s) :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      Summable (fun m : ℕ => poisPMF (s * n / 2) m * rsCbar q n m x) ∧
        |∑' m : ℕ, poisPMF (s * n / 2) m * rsCbar q n m x - rsFbar q n s (tRe q x)| ≤
          C * Real.sqrt n := by
  have hp : CKPar q (tRe q x) := ckPar_tRe hq hx0 hx1
  obtain ⟨L₀, hL₀⟩ := ck_g_lip hp
  refine ⟨max L₀ 0 * Real.sqrt q * (s * Real.exp s + 2 * s) +
    ckEll q (tRe q x) * (2 * Real.sqrt s + s + 2), fun n hn2 => ?_⟩
  have hn : 0 < n := by omega
  refine CKBridgeB_core hp hn2 hs (le_max_right L₀ 0) (fun σ σ' m => ?_)
    (fun m => rsCbar q n m x) (fun m => ck_cbar_eq hq hn hx0 hx1 m) _
    (ck_fbar_eq hp hn hs.le)
  refine (hL₀ n hn σ σ' m).trans ?_
  have h0 : 0 ≤ (m : ℝ) * ∑ c, |colorFrac σ c - colorFrac σ' c| :=
    mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg fun c _ => abs_nonneg _)
  calc L₀ * m * ∑ c, |colorFrac σ c - colorFrac σ' c| =
        L₀ * (m * ∑ c, |colorFrac σ c - colorFrac σ' c|) := by ring
    _ ≤ max L₀ 0 * (m * ∑ c, |colorFrac σ c - colorFrac σ' c|) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ = max L₀ 0 * m * ∑ c, |colorFrac σ c - colorFrac σ' c| := by ring

end

end ERZeroFreeness
