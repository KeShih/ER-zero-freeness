/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.CKInfo
import ERZeroFreeness.CKBern
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: §4 (the planted triple law and the Nishimori identities)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`.

The planted triple law `𝖰 = 𝖰_{[n],ϱ,π}` (Definition 4.1) draws a uniform colouring `σ`, then a
multigraph `G ∼ 𝖯^σ_ϱ` with independent `Pois(ϱ M(σ_u, σ_v))` edge counts, and independent pins
`U ∼ Bern(π)^{[n]}`; `E_𝖰` (`ckQExp`) is a finite sum over `σ` and `U` of `tsum`s over
multigraphs.  On functions dominated by `A c^{|G|}` (`CKDom`) these series converge, and `E_𝖰` is
linear and monotone.  Pin probabilities are constant (`π : ℝ`).  Vertex sets are `Fin n`, so
Lemma 4.7 (relabelling) is not needed.

* Definition 4.1 and Lemma 4.2: `ck_pl_eq` (`𝖯^σ_ϱ = 𝖯_ϱ · L_ϱ(·, σ)`), `ck_L_add`, `ck_L_mem`,
  `ck_Ft_pos`, `ck_abs_log_Ft_le`, `ck_post_isPMF`, `ck_post_eq_cond`.
* Rules for `E_𝖰`: `ck_QExp_add`, `ck_QExp_smul`, `ck_QExp_const`, `ck_QExp_mono`, and Jensen's
  inequality for `√` (`ck_QExp_sqrt_le`).
* Lemma 4.3 (Nishimori identity): `ck_nishimori`, and `ck_nishimori_free` with the unpinned
  posterior, the form of Lemma 4.4(a) used for Corollary 6.2.
* Lemma 4.4(b) (magnetization): `ck_magnetization`, `ck_mean_dev_le`.  Lemma 4.4(c) (predictive
  law of an extra observation): `ck_predictive`.
* Lemma 4.5 (`ck_fbar_le_K`), Lemma 4.6 (pin cost, `ck_pin_cost`) and Corollary 4.9
  (`ck_A_zero_le`, `ck_abs_A_le`).
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### The likelihood ratio `L_ϱ` (Definition 4.1, Lemma 4.2(a)) -/

private lemma CKPlantedA_rsM_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    0 < rsM q t a b :=
  lt_of_lt_of_le (ck_const_bounds hp).1 (ck_rsM_mem hp a b).1

private lemma CKPlantedA_rate_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (e : Fin n × Fin n) : 0 ≤ ckPl q t ϱ σ e :=
  mul_nonneg hϱ (CKPlantedA_rsM_pos hp _ _).le

private lemma CKPlantedA_rsW_ge {q n : ℕ} {t : ℝ} (hp : CKPar q t) (G : RSGraph n)
    (τ : Fin n → Fin q) : ckMm q t ^ rsEdges G ≤ rsW q t G τ := by
  unfold rsW rsEdges
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => pow_nonneg (ck_const_bounds hp).1.le _)
    (fun uv _ => pow_le_pow_left₀ (ck_const_bounds hp).1.le (ck_rsM_mem hp _ _).1 _)

private lemma CKPlantedA_rsW_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) (G : RSGraph n)
    (τ : Fin n → Fin q) : rsW q t G τ ≤ ckMp t ^ rsEdges G := by
  unfold rsW rsEdges
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun _ _ => pow_nonneg (CKPlantedA_rsM_pos hp _ _).le _)
    (fun uv _ => pow_le_pow_left₀ (CKPlantedA_rsM_pos hp _ _).le (ck_rsM_mem hp _ _).2 _)

private lemma CKPlantedA_exp_ge_one {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (τ : Fin n → Fin q) : 1 ≤ Real.exp (-(ϱ * ckS q t τ)) := by
  apply Real.one_le_exp
  have h := (ck_S_mem hp τ).2
  nlinarith

private lemma CKPlantedA_exp_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (τ : Fin n → Fin q) : Real.exp (-(ϱ * ckS q t τ)) ≤ Real.exp (ϱ * (n : ℝ) ^ 2) := by
  rw [Real.exp_le_exp]
  have h := (ck_S_mem hp τ).1
  nlinarith

/-- Definition 4.1: the planted law is the null law weighted by the likelihood ratio,
`𝖯^σ_ϱ(G) = 𝖯_ϱ(G) L_ϱ(G, σ)` (by `rs_poisPi_mul_prod_pow`). -/
theorem ck_pl_eq {q n : ℕ} (t ϱ : ℝ) (σ : Fin n → Fin q) (G : RSGraph n) :
    poisPi (ckPl q t ϱ σ) G = poisPi (fun _ => ϱ) G * ckL q t ϱ G σ := by
  have h := rs_poisPi_mul_prod_pow (fun _ : Fin n × Fin n => ϱ)
    (fun e => rsM q t (σ e.1) (σ e.2)) G
  have hS : ϱ * ckS q t σ = ∑ e : Fin n × Fin n, ϱ * (rsM q t (σ e.1) (σ e.2) - 1) := by
    unfold ckS
    rw [Finset.mul_sum]
  have hpl : ckPl q t ϱ σ = fun e => ϱ * rsM q t (σ e.1) (σ e.2) := rfl
  unfold ckL rsW
  rw [hS, hpl]
  calc poisPi (fun e => ϱ * rsM q t (σ e.1) (σ e.2)) G
      = Real.exp (-∑ e : Fin n × Fin n, ϱ * (rsM q t (σ e.1) (σ e.2) - 1)) *
          (Real.exp (∑ e : Fin n × Fin n, ϱ * (rsM q t (σ e.1) (σ e.2) - 1)) *
            poisPi (fun e => ϱ * rsM q t (σ e.1) (σ e.2)) G) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ = Real.exp (-∑ e : Fin n × Fin n, ϱ * (rsM q t (σ e.1) (σ e.2) - 1)) *
          (poisPi (fun _ => ϱ) G * ∏ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) ^ G uv) := by
        rw [h]
    _ = _ := by ring

/-- The likelihood ratio factorizes under superposition:
`L_{ϱ+δ}(G + H, τ) = L_ϱ(G, τ) L_δ(H, τ)` (by `rs_rsW_add`). -/
theorem ck_L_add {q n : ℕ} (t ϱ δ : ℝ) (G H : RSGraph n) (τ : Fin n → Fin q) :
    ckL q t (ϱ + δ) (G + H) τ = ckL q t ϱ G τ * ckL q t δ H τ := by
  unfold ckL
  rw [rs_rsW_add, add_mul, neg_add, Real.exp_add]
  ring

/-- Lemma 4.2(a): `m₋^{|G|} ≤ L_ϱ(G, τ) ≤ e^{ϱn²} m₊^{|G|}` and `w_G(τ) ≤ L_ϱ(G, τ)`. -/
theorem ck_L_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (G : RSGraph n)
    (τ : Fin n → Fin q) :
    ckMm q t ^ rsEdges G ≤ ckL q t ϱ G τ ∧
      ckL q t ϱ G τ ≤ Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G ∧
        rsW q t G τ ≤ ckL q t ϱ G τ := by
  have hE1 := CKPlantedA_exp_ge_one hp hϱ τ
  have hE2 := CKPlantedA_exp_le hp hϱ τ
  have hW1 := CKPlantedA_rsW_ge hp G τ
  have hW2 := CKPlantedA_rsW_le hp G τ
  have hm : 0 ≤ ckMm q t ^ rsEdges G := pow_nonneg (ck_const_bounds hp).1.le _
  have hW0 : 0 ≤ rsW q t G τ := hm.trans hW1
  have hWL : rsW q t G τ ≤ ckL q t ϱ G τ := by
    unfold ckL
    nlinarith
  refine ⟨hW1.trans hWL, ?_, hWL⟩
  unfold ckL
  exact mul_le_mul hE2 hW2 hW0 (Real.exp_pos _).le

/-! ### The pinned partition function and the posterior (Lemma 4.2(b)) -/

private lemma CKPlantedA_L_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (τ : Fin n → Fin q) : 0 < ckL q t ϱ G τ :=
  lt_of_lt_of_le (pow_pos (ck_const_bounds hp).1 _) (ck_L_mem hp hϱ G τ).1

private lemma CKPlantedA_agree_self {n q : ℕ} (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    ckAgree U ς ς := fun _ _ => rfl

private lemma CKPlantedA_mem_filter_self {n q : ℕ} (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    ς ∈ Finset.univ.filter (fun τ => ckAgree U ς τ) :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, CKPlantedA_agree_self U ς⟩

private lemma CKPlantedA_Z_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    0 < ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ :=
  Finset.sum_pos (fun τ _ => CKPlantedA_L_pos hp hϱ G τ) ⟨ς, CKPlantedA_mem_filter_self U ς⟩

private lemma CKPlantedA_q_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) : (0 : ℝ) < q := by
  have h := hp.two_le
  exact_mod_cast (show 0 < q by omega)

private lemma CKPlantedA_qpow_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (n : ℕ) :
    (0 : ℝ) < (q : ℝ) ^ n :=
  pow_pos (CKPlantedA_q_pos hp) n

/-- Lemma 4.2(b): the pinned partition function is positive, `F̃_ϱ(G, U, ς) > 0`. -/
theorem ck_Ft_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (G : RSGraph n)
    (U : Finset (Fin n)) (ς : Fin n → Fin q) : 0 < ckFt q t ϱ G U ς := by
  unfold ckFt
  exact mul_pos (inv_pos.2 (CKPlantedA_qpow_pos hp n)) (CKPlantedA_Z_pos hp hϱ G U ς)

/-- Lemma 4.2(b): `|log F̃_ϱ(G, U, ς)| ≤ n log q + ϱn² + |G| ℓ₀`. -/
theorem ck_abs_log_Ft_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    |Real.log (ckFt q t ϱ G U ς)| ≤
      n * Real.log q + ϱ * (n : ℝ) ^ 2 + rsEdges G * ckEll q t := by
  have hQ := CKPlantedA_qpow_pos hp n
  have hFpos := ck_Ft_pos hp hϱ G U ς
  have hcb := ck_const_bounds hp
  have hlow : ((q : ℝ) ^ n)⁻¹ * ckMm q t ^ rsEdges G ≤ ckFt q t ϱ G U ς := by
    unfold ckFt
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hQ.le)
    calc ckMm q t ^ rsEdges G ≤ ckL q t ϱ G ς := (ck_L_mem hp hϱ G ς).1
      _ ≤ ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ :=
        Finset.single_le_sum (f := fun τ => ckL q t ϱ G τ)
          (fun τ _ => (CKPlantedA_L_pos hp hϱ G τ).le) (CKPlantedA_mem_filter_self U ς)
  have hup : ckFt q t ϱ G U ς ≤ Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G := by
    unfold ckFt
    rw [inv_mul_le_iff₀ hQ]
    calc ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ ≤ ∑ τ : Fin n → Fin q, ckL q t ϱ G τ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun τ _ _ => (CKPlantedA_L_pos hp hϱ G τ).le)
      _ ≤ ∑ _τ : Fin n → Fin q, Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G :=
          Finset.sum_le_sum fun τ _ => (ck_L_mem hp hϱ G τ).2.1
      _ = (q : ℝ) ^ n * (Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by
    have h := hp.two_le
    exact_mod_cast (show 1 ≤ q by omega))
  have hlow' : -((n : ℝ) * Real.log q) + rsEdges G * Real.log (ckMm q t) ≤
      Real.log (ckFt q t ϱ G U ς) := by
    have h1 := Real.log_le_log (by have := pow_pos hcb.1 (rsEdges G); positivity) hlow
    rw [Real.log_mul (inv_ne_zero hQ.ne') (pow_ne_zero _ hcb.1.ne'), Real.log_inv,
      Real.log_pow, Real.log_pow] at h1
    exact h1
  have hup' : Real.log (ckFt q t ϱ G U ς) ≤ ϱ * (n : ℝ) ^ 2 + rsEdges G * Real.log (ckMp t) := by
    have h1 := Real.log_le_log hFpos hup
    rw [Real.log_mul (Real.exp_pos _).ne' (pow_ne_zero _ (by linarith [hcb.2.2.1])),
      Real.log_exp, Real.log_pow] at h1
    exact h1
  have hE : (rsEdges G : ℝ) * Real.log (ckMp t) ≤ rsEdges G * ckEll q t :=
    mul_le_mul_of_nonneg_left hcb.2.2.2.2.2.2.le (Nat.cast_nonneg _)
  have hE' : (rsEdges G : ℝ) * Real.log (ckMm q t) = -(rsEdges G * ckEll q t) := by
    unfold ckEll
    ring
  have hϱn : 0 ≤ ϱ * (n : ℝ) ^ 2 := by positivity
  have hnlog : 0 ≤ (n : ℝ) * Real.log q := mul_nonneg (Nat.cast_nonneg _) hlogq
  rw [abs_le]
  constructor <;> linarith

/-- The pinned posterior `post_{G,U,ς}` is a probability vector. -/
theorem ck_post_isPMF {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (G : RSGraph n)
    (U : Finset (Fin n)) (ς : Fin n → Fin q) : IsPMF (ckPost q t ϱ G U ς) := by
  have hZ := CKPlantedA_Z_pos hp hϱ G U ς
  refine ⟨fun τ => ?_, ?_⟩
  · unfold ckPost
    split_ifs
    · exact div_nonneg (CKPlantedA_L_pos hp hϱ G τ).le hZ.le
    · exact le_refl 0
  · unfold ckPost
    rw [← Finset.sum_filter, ← Finset.sum_div]
    exact div_self hZ.ne'

/-- `post_{G,U,ς} = μ_G(· | τ_U = ς_U)`: the pinned posterior is the unpinned posterior
`μ_G = post_{G,∅,ς}` conditioned on the pins (Definition 4.1). -/
theorem ck_post_eq_cond {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    ckPost q t ϱ G U ς = ckCond (ckPost q t ϱ G ∅ ς) U ς := by
  have hZ0 := CKPlantedA_Z_pos hp hϱ G ∅ ς
  have hE : ∀ τ : Fin n → Fin q, ckAgree (∅ : Finset (Fin n)) ς τ :=
    fun τ v hv => absurd hv (Finset.notMem_empty v)
  have hpost0 : ∀ τ, ckPost q t ϱ G ∅ ς τ =
      ckL q t ϱ G τ / ∑ τ' with ckAgree (∅ : Finset (Fin n)) ς τ', ckL q t ϱ G τ' := by
    intro τ
    unfold ckPost
    rw [if_pos (hE τ)]
  have hcyl : ckCyl (ckPost q t ϱ G ∅ ς) U ς =
      (∑ τ' with ckAgree U ς τ', ckL q t ϱ G τ') /
        ∑ τ' with ckAgree (∅ : Finset (Fin n)) ς τ', ckL q t ϱ G τ' := by
    unfold ckCyl
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun τ' _ => hpost0 τ'
  funext τ
  rw [ckCond, hcyl, hpost0]
  unfold ckPost
  split_ifs
  · rw [div_div_div_cancel_right₀ hZ0.ne']
  · rfl

/-! ### Expectations under `𝖰` of dominated functions -/

private lemma CKPlantedA_summable {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} (hf : CKDom f)
    (σ : Fin n → Fin q) (U : Finset (Fin n)) :
    Summable fun G => poisPi (ckPl q t ϱ σ) G * f σ G U := by
  obtain ⟨A, c, hc, hb⟩ := hf
  exact rs_summable_poisPi_of_abs_le (CKPlantedA_rate_nonneg hp hϱ σ) hc (fun G => hb σ G U)

private lemma CKPlantedA_dom_add {n q : ℕ}
    {f g : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} (hf : CKDom f) (hg : CKDom g) :
    CKDom (fun σ G U => f σ G U + g σ G U) := by
  obtain ⟨A, c, hc, hfb⟩ := hf
  obtain ⟨B, d, hd, hgb⟩ := hg
  refine ⟨|A| + |B|, max c d, le_max_of_le_left hc, fun σ G U => ?_⟩
  have h1 : c ^ rsEdges G ≤ (max c d) ^ rsEdges G := pow_le_pow_left₀ hc (le_max_left c d) _
  have h2 : d ^ rsEdges G ≤ (max c d) ^ rsEdges G := pow_le_pow_left₀ hd (le_max_right c d) _
  have h3 : A * c ^ rsEdges G ≤ |A| * (max c d) ^ rsEdges G :=
    mul_le_mul (le_abs_self A) h1 (pow_nonneg hc _) (abs_nonneg A)
  have h4 : B * d ^ rsEdges G ≤ |B| * (max c d) ^ rsEdges G :=
    mul_le_mul (le_abs_self B) h2 (pow_nonneg hd _) (abs_nonneg B)
  calc |f σ G U + g σ G U| ≤ |f σ G U| + |g σ G U| := abs_add_le _ _
    _ ≤ A * c ^ rsEdges G + B * d ^ rsEdges G := add_le_add (hfb σ G U) (hgb σ G U)
    _ ≤ (|A| + |B|) * (max c d) ^ rsEdges G := by rw [add_mul]; exact add_le_add h3 h4

private lemma CKPlantedA_dom_smul {n q : ℕ}
    {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} (c : ℝ) (hf : CKDom f) :
    CKDom (fun σ G U => c * f σ G U) := by
  obtain ⟨A, d, hd, hfb⟩ := hf
  refine ⟨|c| * A, d, hd, fun σ G U => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hfb σ G U) (abs_nonneg c)

private lemma CKPlantedA_dom_const {n q : ℕ} (c : ℝ) :
    CKDom (fun (_ : Fin n → Fin q) (_ : RSGraph n) (_ : Finset (Fin n)) => c) :=
  ⟨|c|, 1, zero_le_one, fun _ _ _ => by rw [one_pow, mul_one]⟩

/-- `√x ≤ x/(2a) + a/2` (AM–GM). -/
private lemma CKPlantedA_sqrt_le {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.sqrt x ≤ 1 / (2 * a) * x + a / 2 := by
  have h1 := Real.sq_sqrt hx
  have h2 := sq_nonneg (Real.sqrt x - a)
  have h3 : 1 / (2 * a) * x + a / 2 = (x + a ^ 2) / (2 * a) := by
    field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  nlinarith

private lemma CKPlantedA_dom_sqrt {n q : ℕ}
    {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} (hf0 : ∀ σ G U, 0 ≤ f σ G U)
    (hf : CKDom f) : CKDom (fun σ G U => Real.sqrt (f σ G U)) := by
  obtain ⟨A, c, hc, hb⟩ :=
    CKPlantedA_dom_add (CKPlantedA_dom_smul (1 / (2 * 1)) hf)
      (CKPlantedA_dom_const (n := n) (q := q) (1 / 2))
  refine ⟨A, c, hc, fun σ G U => ?_⟩
  have hs := CKPlantedA_sqrt_le (hf0 σ G U) one_pos
  have hb' := hb σ G U
  have habs := le_abs_self (1 / (2 * 1) * f σ G U + 1 / 2)
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  linarith

/-- `E_𝖰` is additive on dominated functions. -/
theorem ck_QExp_add {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (π : ℝ)
    {f g : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} (hf : CKDom f) (hg : CKDom g) :
    ckQExp q t ϱ π n (fun σ G U => f σ G U + g σ G U) =
      ckQExp q t ϱ π n f + ckQExp q t ϱ π n g := by
  have hsf := CKPlantedA_summable hp hϱ hf
  have hsg := CKPlantedA_summable hp hϱ hg
  have h : ∀ σ U, ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * (f σ G U + g σ G U) =
      ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * f σ G U +
        ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * g σ G U := by
    intro σ U
    rw [← mul_add, ← (hsf σ U).tsum_add (hsg σ U)]
    congr 1
    exact tsum_congr fun G => by ring
  simp only [ckQExp]
  simp only [h]
  simp only [Finset.sum_add_distrib, mul_add]

/-- `E_𝖰` commutes with multiplication by a constant; no hypotheses are needed
(`tsum_mul_left`). -/
theorem ck_QExp_smul {q n : ℕ} (t ϱ π c : ℝ)
    (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) :
    ckQExp q t ϱ π n (fun σ G U => c * f σ G U) = c * ckQExp q t ϱ π n f := by
  have h : ∀ σ U, ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * (c * f σ G U) =
      c * (ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * f σ G U) := by
    intro σ U
    rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun G => by ring
  simp only [ckQExp, h, ← Finset.mul_sum]
  ring

/-- `E_𝖰` of a constant is that constant. -/
theorem ck_QExp_const {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (π c : ℝ) :
    ckQExp q t ϱ π n (fun _ _ _ => c) = c := by
  have h1 : ∀ σ : Fin n → Fin q, ∑' G, poisPi (ckPl q t ϱ σ) G * c = c := by
    intro σ
    rw [tsum_mul_right, (rs_hasSum_poisPi (CKPlantedA_rate_nonneg hp hϱ σ)).tsum_eq, one_mul]
  have h2 : ∑ U : Finset (Fin n), ckBern π U * c = c := by
    rw [← Finset.sum_mul, ck_bern_sum, one_mul]
  simp only [ckQExp, h1, h2]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, ← mul_assoc, inv_mul_cancel₀ (CKPlantedA_qpow_pos hp n).ne',
    one_mul]

/-- `E_𝖰` is monotone on dominated functions. -/
theorem ck_QExp_mono {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ} (hϱ : 0 ≤ ϱ) (hπ0 : 0 ≤ π)
    (hπ1 : π ≤ 1) {f g : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ} (hf : CKDom f)
    (hg : CKDom g) (hfg : ∀ σ G U, f σ G U ≤ g σ G U) :
    ckQExp q t ϱ π n f ≤ ckQExp q t ϱ π n g := by
  have hsf := CKPlantedA_summable hp hϱ hf
  have hsg := CKPlantedA_summable hp hϱ hg
  unfold ckQExp
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg q) n))
  refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun U _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ (ck_bern_nonneg hπ0 hπ1 U)
  exact Summable.tsum_le_tsum (fun G => mul_le_mul_of_nonneg_left (hfg σ G U)
    (rs_poisPi_nonneg (CKPlantedA_rate_nonneg hp hϱ σ) G)) (hsf σ U) (hsg σ U)

/-- Jensen's inequality for `√`: `E_𝖰 √f ≤ √(E_𝖰 f)` for nonnegative dominated `f`.  Proof:
`E_𝖰 √f ≤ E_𝖰 f/(2a) + a/2` for every `a > 0` (`√x ≤ x/(2a) + a/2`); take `a = √(E_𝖰 f)` if
`E_𝖰 f > 0`, and `a = E_𝖰 √f` to rule out `E_𝖰 √f > 0` otherwise. -/
theorem ck_QExp_sqrt_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ} (hϱ : 0 ≤ ϱ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ}
    (hf0 : ∀ σ G U, 0 ≤ f σ G U) (hf : CKDom f) :
    ckQExp q t ϱ π n (fun σ G U => Real.sqrt (f σ G U)) ≤ Real.sqrt (ckQExp q t ϱ π n f) := by
  have hdq := CKPlantedA_dom_sqrt hf0 hf
  have key : ∀ a : ℝ, 0 < a → ckQExp q t ϱ π n (fun σ G U => Real.sqrt (f σ G U)) ≤
      1 / (2 * a) * ckQExp q t ϱ π n f + a / 2 := by
    intro a ha
    have hd1 := CKPlantedA_dom_smul (1 / (2 * a)) hf
    have hd2 := CKPlantedA_dom_const (n := n) (q := q) (a / 2)
    calc ckQExp q t ϱ π n (fun σ G U => Real.sqrt (f σ G U))
        ≤ ckQExp q t ϱ π n (fun σ G U => 1 / (2 * a) * f σ G U + a / 2) :=
          ck_QExp_mono hp hϱ hπ0 hπ1 hdq (CKPlantedA_dom_add hd1 hd2)
            (fun σ G U => CKPlantedA_sqrt_le (hf0 σ G U) ha)
      _ = ckQExp q t ϱ π n (fun σ G U => 1 / (2 * a) * f σ G U) +
            ckQExp q t ϱ π n (fun _ _ _ => a / 2) := ck_QExp_add hp hϱ π hd1 hd2
      _ = 1 / (2 * a) * ckQExp q t ϱ π n f + a / 2 := by
          rw [ck_QExp_smul, ck_QExp_const hp hϱ]
  set E := ckQExp q t ϱ π n f with hEdef
  set X := ckQExp q t ϱ π n (fun σ G U => Real.sqrt (f σ G U)) with hXdef
  rcases lt_or_ge 0 E with hE | hE
  · set s := Real.sqrt E with hsdef
    have hs : 0 < s := Real.sqrt_pos.2 hE
    have hsq : s ^ 2 = E := Real.sq_sqrt hE.le
    have h1 := key s hs
    have h2 : 1 / (2 * s) * E = s / 2 := by
      rw [← hsq]
      field_simp
    linarith
  · rw [Real.sqrt_eq_zero'.2 hE]
    by_contra hcon
    have hX : 0 < X := not_le.mp hcon
    have h1 := key X hX
    have h2 : 1 / (2 * X) * E ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hE
    linarith

/-! ### Basic positivity and summability helpers -/

private lemma CKPlantedB_Mm_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) : 0 < ckMm q t :=
  (ck_const_bounds hp).1

private lemma CKPlantedB_pl_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (e : Fin n × Fin n) : 0 ≤ ckPl q t ϱ σ e :=
  mul_nonneg hϱ ((CKPlantedB_Mm_pos hp).le.trans (ck_rsM_mem hp _ _).1)

private lemma CKPlantedB_summable {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) {F : RSGraph n → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hF : ∀ G, |F G| ≤ A * c ^ rsEdges G) :
    Summable (fun G => poisPi (ckPl q t ϱ σ) G * F G) :=
  rs_summable_poisPi_of_abs_le (CKPlantedB_pl_nonneg hp hϱ σ) hc hF

private lemma CKPlantedB_L_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (τ : Fin n → Fin q) : 0 < ckL q t ϱ G τ :=
  lt_of_lt_of_le (pow_pos (CKPlantedB_Mm_pos hp) _) (ck_L_mem hp hϱ G τ).1

private lemma CKPlantedB_agree_symm {n q : ℕ} {W : Finset (Fin n)} {σ τ : Fin n → Fin q} :
    ckAgree W σ τ ↔ ckAgree W τ σ := by
  unfold ckAgree
  exact ⟨fun h v hv => (h v hv).symm, fun h v hv => (h v hv).symm⟩

private lemma CKPlantedB_agree_trans_iff {n q : ℕ} {W : Finset (Fin n)} {σ τ : Fin n → Fin q}
    (h : ckAgree W σ τ) (τ' : Fin n → Fin q) : ckAgree W σ τ' ↔ ckAgree W τ τ' := by
  unfold ckAgree at *
  constructor
  · intro h' v hv; rw [h' v hv, h v hv]
  · intro h' v hv; rw [h' v hv, h v hv]

private lemma CKPlantedB_agree_refl {n q : ℕ} (W : Finset (Fin n)) (σ : Fin n → Fin q) :
    ckAgree W σ σ := fun _ _ => rfl

private lemma CKPlantedB_Z_congr {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) {W : Finset (Fin n)}
    {σ τ : Fin n → Fin q} (h : ckAgree W σ τ) :
    (∑ τ' with ckAgree W σ τ', ckL q t ϱ G τ') = ∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ' := by
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext τ'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact CKPlantedB_agree_trans_iff h τ'

private lemma CKPlantedB_Z_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (W : Finset (Fin n)) (τ : Fin n → Fin q) :
    0 < ∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ' := by
  apply Finset.sum_pos (fun τ' _ => CKPlantedB_L_pos hp hϱ G τ')
  exact ⟨τ, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact
    CKPlantedB_agree_refl W τ⟩

private lemma CKPlantedB_post_of_not {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (W : Finset (Fin n))
    {σ τ : Fin n → Fin q} (h : ¬ ckAgree W σ τ) : ckPost q t ϱ G W σ τ = 0 := by
  unfold ckPost
  rw [if_neg h]

/-! ### The Nishimori identity and the predictive law (Lemmas 4.3 and 4.4(c)) -/

/-- The Nishimori identity for a fixed multigraph `G` and pin set `W` (finite sums):
`∑_σ L(σ) ∑_τ post_{G,W,σ}(τ) g(τ, σ) = ∑_σ L(σ) g(σ, σ)` when `g(τ, ς)` depends on `ς` only
through `ς_W`. -/
private lemma CKPlantedB_pointwise {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (W : Finset (Fin n)) (g : (Fin n → Fin q) → (Fin n → Fin q) → ℝ)
    (hg : ∀ τ ς ς', ckAgree W ς ς' → g τ ς = g τ ς') :
    ∑ σ, ckL q t ϱ G σ * ∑ τ, ckPost q t ϱ G W σ τ * g τ σ =
      ∑ σ, ckL q t ϱ G σ * g σ σ := by
  have step1 : ∀ σ τ, ckL q t ϱ G σ * (ckPost q t ϱ G W σ τ * g τ σ) =
      if ckAgree W τ σ then ckL q t ϱ G σ *
        (ckL q t ϱ G τ / (∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ') * g τ τ) else 0 := by
    intro σ τ
    unfold ckPost
    by_cases h : ckAgree W σ τ
    · have h' : ckAgree W τ σ := CKPlantedB_agree_symm.mp h
      rw [if_pos h, if_pos h', CKPlantedB_Z_congr t ϱ G h, hg τ σ τ h]
    · have h' : ¬ ckAgree W τ σ := fun h' => h (CKPlantedB_agree_symm.mp h')
      rw [if_neg h, if_neg h']
      ring
  calc ∑ σ, ckL q t ϱ G σ * ∑ τ, ckPost q t ϱ G W σ τ * g τ σ
      = ∑ σ, ∑ τ, (if ckAgree W τ σ then ckL q t ϱ G σ *
          (ckL q t ϱ G τ / (∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ') * g τ τ) else 0) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => step1 σ τ
    _ = ∑ τ, ∑ σ, (if ckAgree W τ σ then ckL q t ϱ G σ *
          (ckL q t ϱ G τ / (∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ') * g τ τ) else 0) :=
        Finset.sum_comm
    _ = ∑ τ, (∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ') *
          (ckL q t ϱ G τ / (∑ τ' with ckAgree W τ τ', ckL q t ϱ G τ') * g τ τ) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [Finset.sum_filter, Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        split_ifs <;> ring
    _ = ∑ τ, ckL q t ϱ G τ * g τ τ := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        have := (CKPlantedB_Z_pos hp hϱ G W τ).ne'
        field_simp

/-- A posterior average of a function bounded by `B` on the pinned class is bounded by `B`. -/
private lemma CKPlantedB_post_bound {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (W : Finset (Fin n)) (σ : Fin n → Fin q) (g : (Fin n → Fin q) → ℝ) {B : ℝ}
    (hg : ∀ τ, ckAgree W σ τ → |g τ| ≤ B) :
    |∑ τ, ckPost q t ϱ G W σ τ * g τ| ≤ B := by
  obtain ⟨h0, h1⟩ := ck_post_isPMF hp hϱ G W σ
  calc |∑ τ, ckPost q t ϱ G W σ τ * g τ| ≤ ∑ τ, |ckPost q t ϱ G W σ τ * g τ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ τ, ckPost q t ϱ G W σ τ * B := by
        refine Finset.sum_le_sum fun τ _ => ?_
        rw [abs_mul, abs_of_nonneg (h0 τ)]
        by_cases h : ckAgree W σ τ
        · exact mul_le_mul_of_nonneg_left (hg τ h) (h0 τ)
        · rw [CKPlantedB_post_of_not t ϱ G W h]
          simp
    _ = B := by rw [← Finset.sum_mul, h1, one_mul]

/-- The Nishimori identity for a fixed pin set `W`, summed over `σ` and the multigraph. -/
private lemma CKPlantedB_inner {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (W : Finset (Fin n)) (g : RSGraph n → (Fin n → Fin q) → (Fin n → Fin q) → ℝ)
    (hg : ∀ G τ ς ς', ckAgree W ς ς' → g G τ ς = g G τ ς')
    {A c : ℝ} (hc : 0 ≤ c) (hgb : ∀ G τ ς, ckAgree W ς τ → |g G τ ς| ≤ A * c ^ rsEdges G) :
    ∑ σ, ∑' G, poisPi (ckPl q t ϱ σ) G * g G σ σ =
      ∑ σ, ∑' G, poisPi (ckPl q t ϱ σ) G * ∑ τ, ckPost q t ϱ G W σ τ * g G τ σ := by
  have hs1 : ∀ σ, Summable (fun G => poisPi (ckPl q t ϱ σ) G * g G σ σ) := fun σ =>
    CKPlantedB_summable hp hϱ σ hc (fun G => hgb G σ σ (CKPlantedB_agree_refl W σ))
  have hs2 : ∀ σ, Summable (fun G => poisPi (ckPl q t ϱ σ) G *
      ∑ τ, ckPost q t ϱ G W σ τ * g G τ σ) := fun σ =>
    CKPlantedB_summable hp hϱ σ hc
      (fun G => CKPlantedB_post_bound hp hϱ G W σ _ (fun τ h => hgb G τ σ h))
  rw [← Summable.tsum_finsetSum (fun σ _ => hs1 σ),
    ← Summable.tsum_finsetSum (fun σ _ => hs2 σ)]
  refine tsum_congr fun G => ?_
  simp_rw [ck_pl_eq, mul_assoc, ← Finset.mul_sum]
  congr 1
  exact (CKPlantedB_pointwise hp hϱ G W (g G) (hg G)).symm

/-- Two `E_𝖰`-expectations agree if their `σ`-sums agree for every pin set. -/
private lemma CKPlantedB_QExp_congr {q n : ℕ} (t ϱ π : ℝ)
    (F1 F2 : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ)
    (h : ∀ U, ∑ σ, ∑' G, poisPi (ckPl q t ϱ σ) G * F1 σ G U =
      ∑ σ, ∑' G, poisPi (ckPl q t ϱ σ) G * F2 σ G U) :
    ckQExp q t ϱ π n F1 = ckQExp q t ϱ π n F2 := by
  unfold ckQExp
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun U _ => ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, h U]

/-- Lemma 4.3 (Nishimori identity):
`E_𝖰 f(σ, G, U, σ) = E_𝖰 ∑_τ post_{G,U,σ}(τ) f(τ, G, U, σ)` for `f(τ, G, U, ς)` that depends on
`ς` only through `ς_U` and is bounded by `A c^{|G|}` where `τ_U = ς_U`.  The values of `f` with
`τ_U ≠ ς_U` are not used: the posterior vanishes there. -/
theorem ck_nishimori {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (π : ℝ)
    (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → (Fin n → Fin q) → ℝ)
    (hfU : ∀ τ G U ς ς', ckAgree U ς ς' → f τ G U ς = f τ G U ς')
    {A c : ℝ} (hc : 0 ≤ c)
    (hfb : ∀ τ G U ς, ckAgree U ς τ → |f τ G U ς| ≤ A * c ^ rsEdges G) :
    ckQExp q t ϱ π n (fun σ G U => f σ G U σ) =
      ckQExp q t ϱ π n (fun σ G U => ∑ τ, ckPost q t ϱ G U σ τ * f τ G U σ) :=
  CKPlantedB_QExp_congr t ϱ π _ _ fun U =>
    CKPlantedB_inner hp hϱ U (fun G τ ς => f τ G U ς) (fun G τ ς ς' h => hfU τ G U ς ς' h) hc
      (fun G τ ς h => hfb τ G U ς h)

/-- Lemma 4.3 with the unpinned posterior `μ_G = post_{G,∅,σ}`, for `f(τ, G, U)` bounded by
`A c^{|G|}`: `E_𝖰 f(σ, G, U) = E_𝖰 ∑_τ μ_G(τ) f(τ, G, U)`.  This is the form of Lemma 4.4(a)
used for Corollary 6.2. -/
theorem ck_nishimori_free {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (π : ℝ)
    (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) {A c : ℝ} (hc : 0 ≤ c)
    (hfb : ∀ τ G U, |f τ G U| ≤ A * c ^ rsEdges G) :
    ckQExp q t ϱ π n f =
      ckQExp q t ϱ π n (fun σ G U => ∑ τ, ckPost q t ϱ G ∅ σ τ * f τ G U) :=
  CKPlantedB_QExp_congr t ϱ π _ _ fun U =>
    CKPlantedB_inner hp hϱ ∅ (fun G τ _ => f τ G U) (fun _ _ _ _ _ => rfl) hc
      (fun G τ _ _ => hfb τ G U)

/-- Lemma 4.4(c) (predictive law of an extra observation), dominated form.  Let
`R(h, τ) ≥ 0` (this is `R⁰(h) ℓ(h, τ)` in Lemma 4.4(c)), let `φ(h, G, U, ς)` depend on `ς` only
through `ς_U`, and let `|φ(h, ·)| ≤ Φ(h)` with `∑_h R(h, τ) Φ(h) < ∞` for every `τ`.  Then
`E_𝖰 ∑_h R(h, σ) φ(h, G, U, σ) = E_𝖰 ∑_h ⟨R(h, ·)⟩_{post_{G,U,σ}} φ(h, G, U, σ)`; no
normalization of `R` is needed.  Proof: Lemma 4.3 for the bounded
`f(τ, G, U, ς) = ∑_h R(h, τ) φ(h, G, U, ς)`. -/
theorem ck_predictive {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (π : ℝ)
    {H : Type*} (R : H → (Fin n → Fin q) → ℝ) (hR : ∀ h τ, 0 ≤ R h τ)
    (φ : H → RSGraph n → Finset (Fin n) → (Fin n → Fin q) → ℝ)
    (hφU : ∀ h G U ς ς', ckAgree U ς ς' → φ h G U ς = φ h G U ς')
    (Φ : H → ℝ) (hφ : ∀ h G U ς, |φ h G U ς| ≤ Φ h)
    (hΦ : ∀ τ, Summable fun h => R h τ * Φ h) :
    ckQExp q t ϱ π n (fun σ G U => ∑' h, R h σ * φ h G U σ) =
      ckQExp q t ϱ π n
        (fun σ G U => ∑' h, (∑ τ, ckPost q t ϱ G U σ τ * R h τ) * φ h G U σ) := by
  have hnorm : ∀ τ G U ς h, ‖R h τ * φ h G U ς‖ ≤ R h τ * Φ h := fun τ G U ς h => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hR h τ)]
    exact mul_le_mul_of_nonneg_left (hφ h G U ς) (hR h τ)
  have hsum : ∀ τ G U ς, Summable fun h => R h τ * φ h G U ς := fun τ G U ς =>
    Summable.of_norm_bounded (hΦ τ) (hnorm τ G U ς)
  have hbd : ∀ τ G U ς, |∑' h, R h τ * φ h G U ς| ≤ ∑' h, R h τ * Φ h := fun τ G U ς =>
    tsum_of_norm_bounded (hΦ τ).hasSum (hnorm τ G U ς)
  have key := ck_nishimori hp hϱ π (fun τ G U ς => ∑' h, R h τ * φ h G U ς)
    (fun τ G U ς ς' hag => tsum_congr fun h => by rw [hφU h G U ς ς' hag])
    (A := ∑ τ, |∑' h, R h τ * Φ h|) (c := 1) zero_le_one
    (fun τ G U ς _ => by
      rw [one_pow, mul_one]
      exact (hbd τ G U ς).trans ((le_abs_self _).trans
        (Finset.single_le_sum (f := fun τ => |∑' h, R h τ * Φ h|)
          (fun τ _ => abs_nonneg _) (Finset.mem_univ τ))))
  rw [key]
  congr 1
  funext σ G U
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun τ _ => (hsum τ G U σ).mul_left _)]
  refine tsum_congr fun h => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  ring

/-! ### Bounds on `log F̃` and `log F`; Lemma 4.5 -/

private lemma CKPlantedB_q_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) : (0 : ℝ) < q := by
  have := hp.two_le
  exact_mod_cast (show 0 < q by omega)

private lemma CKPlantedB_qn_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (n : ℕ) :
    (0 : ℝ) < (q : ℝ) ^ n :=
  pow_pos (CKPlantedB_q_pos hp) n

private lemma CKPlantedB_logq_nonneg {q : ℕ} {t : ℝ} (hp : CKPar q t) : 0 ≤ Real.log q := by
  have := hp.two_le
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))

private lemma CKPlantedB_ell_nonneg {q : ℕ} {t : ℝ} (hp : CKPar q t) : 0 ≤ ckEll q t :=
  (ck_const_bounds hp).2.2.2.2.2.1.le

private lemma CKPlantedB_lin_le_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    a + k * b ≤ (a + b) * 2 ^ k := by
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  nlinarith

/-- The constant part `n log q + ϱ n²` of Lemma 4.2(b) is nonnegative. -/
private lemma CKPlantedB_a_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    0 ≤ (n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 :=
  add_nonneg (mul_nonneg (Nat.cast_nonneg _) (CKPlantedB_logq_nonneg hp))
    (mul_nonneg hϱ (sq_nonneg _))

private lemma CKPlantedB_logFt_dom {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    |Real.log (ckFt q t ϱ G U ς)| ≤
      ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + ckEll q t) * 2 ^ rsEdges G := by
  have h := ck_abs_log_Ft_le hp hϱ G U ς
  have := CKPlantedB_lin_le_pow (CKPlantedB_a_nonneg (n := n) hp hϱ) (CKPlantedB_ell_nonneg hp)
    (rsEdges G)
  linarith

private lemma CKPlantedB_rsW_ge {q n : ℕ} {t : ℝ} (hp : CKPar q t) (G : RSGraph n)
    (τ : Fin n → Fin q) : ckMm q t ^ rsEdges G ≤ rsW q t G τ := by
  have h := (ck_L_mem hp le_rfl G τ).1
  unfold ckL at h
  simpa using h

private lemma CKPlantedB_rsF_ge {q n : ℕ} {t : ℝ} (hp : CKPar q t) (G : RSGraph n) :
    ckMm q t ^ rsEdges G ≤ rsF q t G := by
  unfold rsF
  have hsum : ∑ _σ : Fin n → Fin q, ckMm q t ^ rsEdges G ≤ ∑ σ : Fin n → Fin q, rsW q t G σ :=
    Finset.sum_le_sum fun σ _ => CKPlantedB_rsW_ge hp G σ
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun] at hsum
  simp only [Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum
  rw [le_inv_mul_iff₀ (CKPlantedB_qn_pos hp n)]
  exact hsum

private lemma CKPlantedB_rsF_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) (G : RSGraph n) :
    0 < rsF q t G :=
  lt_of_lt_of_le (pow_pos (CKPlantedB_Mm_pos hp) _) (CKPlantedB_rsF_ge hp G)

private lemma CKPlantedB_rsF_le_Ft {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (σ : Fin n → Fin q) : rsF q t G ≤ ckFt q t ϱ G ∅ σ := by
  unfold rsF ckFt
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (CKPlantedB_qn_pos hp n).le)
  rw [Finset.filter_true_of_mem (fun τ _ => by simp [ckAgree])]
  exact Finset.sum_le_sum fun τ _ => (ck_L_mem hp hϱ G τ).2.2

private lemma CKPlantedB_logF_dom {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (σ : Fin n → Fin q) :
    |Real.log (rsF q t G)| ≤
      ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + ckEll q t) * 2 ^ rsEdges G := by
  have hF := CKPlantedB_rsF_pos hp G
  have hup : Real.log (rsF q t G) ≤ Real.log (ckFt q t ϱ G ∅ σ) :=
    Real.log_le_log hF (CKPlantedB_rsF_le_Ft hp hϱ G σ)
  have hlo : Real.log (ckMm q t ^ rsEdges G) ≤ Real.log (rsF q t G) :=
    Real.log_le_log (pow_pos (CKPlantedB_Mm_pos hp) _) (CKPlantedB_rsF_ge hp G)
  rw [Real.log_pow] at hlo
  have hFt := ck_abs_log_Ft_le hp hϱ G ∅ σ
  have hlin := CKPlantedB_lin_le_pow (CKPlantedB_a_nonneg (n := n) hp hϱ)
    (CKPlantedB_ell_nonneg hp) (rsEdges G)
  have ha := CKPlantedB_a_nonneg (n := n) hp hϱ
  have hell : ckEll q t = -Real.log (ckMm q t) := rfl
  rw [abs_le] at hFt ⊢
  rw [hell] at hlin hFt ⊢
  constructor
  · nlinarith
  · linarith

/-- Lemma 4.5: `f̄_n ≤ 𝒦_{[n]}(s/(2n), 0)` for `n ≥ 1` and `s ≥ 0`.  Without pins,
`F̃_ϱ(G, ∅, ·) ≥ F_G` by Lemma 4.2(a), and both sides are expectations under the same law of
`(σ, G)`. -/
theorem ck_fbar_le_K {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) {s : ℝ} (hs : 0 ≤ s) :
    rsFbar q n s t ≤ ckK q t (s / (2 * n)) 0 n := by
  set ϱ : ℝ := s / (2 * n) with hϱdef
  have hϱ : 0 ≤ ϱ := by positivity
  have hmean : ∀ σ : Fin n → Fin q, cpMean (fun a b => s * rsM q t a b) σ = ckPl q t ϱ σ := by
    intro σ
    funext e
    simp only [cpMean, ckPl, hϱdef]
    ring
  have hL : rsFbar q n s t = ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
      ∑' G, poisPi (ckPl q t ϱ σ) G * Real.log (rsF q t G) := by
    unfold rsFbar cpExp poisPiExp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hmean σ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  have hR : ckK q t ϱ 0 n = ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
      ∑' G, poisPi (ckPl q t ϱ σ) G * Real.log (ckFt q t ϱ G ∅ σ) := by
    unfold ckK ckQExp
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp_rw [ck_bern_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (∅ : Finset (Fin n))]
    simp
  rw [hL, hR]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (CKPlantedB_qn_pos hp n).le)
  refine Finset.sum_le_sum fun σ _ => ?_
  refine Summable.tsum_le_tsum (fun G => ?_)
    (CKPlantedB_summable hp hϱ σ (by norm_num : (0 : ℝ) ≤ 2)
      (fun G => CKPlantedB_logF_dom hp hϱ G σ))
    (CKPlantedB_summable hp hϱ σ (by norm_num : (0 : ℝ) ≤ 2)
      (fun G => CKPlantedB_logFt_dom hp hϱ G ∅ σ))
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (CKPlantedB_rsF_pos hp G) (CKPlantedB_rsF_le_Ft hp hϱ G σ))
    (rs_poisPi_nonneg (CKPlantedB_pl_nonneg hp hϱ σ) G)

/-! ### Magnetization (Lemma 4.4(b)) -/

/-- `E_𝖰` of a function of `σ` alone is its average over uniform `σ`. -/
private lemma CKPlantedB_QExp_sigma {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (π : ℝ) (φ : (Fin n → Fin q) → ℝ) :
    ckQExp q t ϱ π n (fun σ _ _ => φ σ) = ((q : ℝ) ^ n)⁻¹ * ∑ σ, φ σ := by
  unfold ckQExp
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  dsimp only
  rw [tsum_mul_right, (rs_hasSum_poisPi (CKPlantedB_pl_nonneg hp hϱ σ)).tsum_eq, one_mul,
    ← Finset.sum_mul, ck_bern_sum, one_mul]

/-- Jensen for `√` against a probability vector. -/
private lemma CKPlantedB_sum_mul_sqrt_le {ι : Type*} [Fintype ι] {w x : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (hx : ∀ i, 0 ≤ x i) :
    ∑ i, w i * Real.sqrt (x i) ≤ Real.sqrt (∑ i, w i * x i) := by
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset ι)
    (r := fun i => w i * Real.sqrt (x i)) (f := w) (g := fun i => w i * x i)
    (fun i _ => hw0 i) (fun i _ => mul_nonneg (hw0 i) (hx i)) (fun i _ => by
      rw [mul_pow, Real.sq_sqrt (hx i)]
      exact le_of_eq (by ring))
  rwa [hw1, one_mul] at h

/-- Lemma 4.4(b) (magnetization): `E_𝖰 dev(post_{G,U,σ}) ≤ n^{-1/2}`.  Proof:
`dev(μ) ≤ ⟨‖λ_τ - u‖²⟩_μ^{1/2}` and Jensen's inequality for `√` under `𝖰`; Lemma 4.3 turns
`E_𝖰 ⟨‖λ_τ - u‖²⟩_post` into `E_σ ‖λ_σ - u‖² = (q-1)/(qn) ≤ 1/n` (Lemma 1.4(d)). -/
theorem ck_magnetization {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n) {ϱ π : ℝ}
    (hϱ : 0 ≤ ϱ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    ckQExp q t ϱ π n (fun σ G U => ckDev (ckPost q t ϱ G U σ)) ≤ 1 / Real.sqrt n := by
  set D : ℝ := ∑ τ : Fin n → Fin q, rsDevSq τ with hD
  have hdev0 : ∀ τ : Fin n → Fin q, 0 ≤ rsDevSq τ := fun τ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hdevD : ∀ τ, rsDevSq τ ≤ D := fun τ =>
    Finset.single_le_sum (f := fun τ => rsDevSq τ) (fun τ _ => hdev0 τ) (Finset.mem_univ τ)
  have hpost := fun (G : RSGraph n) (U : Finset (Fin n)) (σ : Fin n → Fin q) =>
    ck_post_isPMF hp hϱ G U σ
  have hg0 : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), 0 ≤ ∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ := fun σ G U =>
    Finset.sum_nonneg fun τ _ => mul_nonneg ((hpost G U σ).1 τ) (hdev0 τ)
  have hgD : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), ∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ ≤ D := by
    intro σ G U
    calc ∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ ≤ ∑ τ, ckPost q t ϱ G U σ τ * D :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hdevD τ) ((hpost G U σ).1 τ)
      _ = D := by rw [← Finset.sum_mul, (hpost G U σ).2, one_mul]
  have hjensen : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), ckDev (ckPost q t ϱ G U σ) ≤
      Real.sqrt (∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ) := fun σ G U =>
    CKPlantedB_sum_mul_sqrt_le (hpost G U σ).1 (hpost G U σ).2 hdev0
  have hdev_nonneg : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)), 0 ≤ ckDev (ckPost q t ϱ G U σ) := fun σ G U =>
    Finset.sum_nonneg fun τ _ => mul_nonneg ((hpost G U σ).1 τ) (Real.sqrt_nonneg _)
  have hdom_g : CKDom (fun σ G U => ∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ) :=
    ⟨D, 1, zero_le_one, fun σ G U => by
      rw [one_pow, mul_one, abs_of_nonneg (hg0 σ G U)]
      exact hgD σ G U⟩
  have hdom_sqrt : CKDom (fun σ G U => Real.sqrt (∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ)) :=
    ⟨Real.sqrt D, 1, zero_le_one, fun σ G U => by
      rw [one_pow, mul_one, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hgD σ G U)⟩
  have hdom_dev : CKDom (fun σ G U => ckDev (ckPost q t ϱ G U σ)) :=
    ⟨Real.sqrt D, 1, zero_le_one, fun σ G U => by
      rw [one_pow, mul_one, abs_of_nonneg (hdev_nonneg σ G U)]
      exact (hjensen σ G U).trans (Real.sqrt_le_sqrt (hgD σ G U))⟩
  have hnish := ck_nishimori hp hϱ π (fun τ _ _ _ => rsDevSq τ) (fun _ _ _ _ _ _ => rfl)
    (A := D) (c := 1) zero_le_one (fun τ G U ς _ => by
      rw [one_pow, mul_one, abs_of_nonneg (hdev0 τ)]
      exact hdevD τ)
  have hq0 : (q : ℝ) ≠ 0 := (CKPlantedB_q_pos hp).ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hEdev : ckQExp q t ϱ π n (fun σ _ _ => rsDevSq σ) = ((q : ℝ) - 1) / (q * n) := by
    rw [CKPlantedB_QExp_sigma hp hϱ π]
    exact ck_avg_devSq (by exact_mod_cast hq0) hn.ne'
  have hfin : Real.sqrt (((q : ℝ) - 1) / (q * n)) ≤ 1 / Real.sqrt n := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : ((q : ℝ) - 1) / (q * n) ≤ 1 / n := by
      rw [div_le_div_iff₀ (mul_pos (CKPlantedB_q_pos hp) hnpos) hnpos]
      nlinarith
    calc Real.sqrt (((q : ℝ) - 1) / (q * n)) ≤ Real.sqrt (1 / n) := Real.sqrt_le_sqrt hle
      _ = 1 / Real.sqrt n := by rw [Real.sqrt_div zero_le_one, Real.sqrt_one]
  calc ckQExp q t ϱ π n (fun σ G U => ckDev (ckPost q t ϱ G U σ))
      ≤ ckQExp q t ϱ π n (fun σ G U => Real.sqrt (∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ)) :=
        ck_QExp_mono hp hϱ hπ0 hπ1 hdom_dev hdom_sqrt hjensen
    _ ≤ Real.sqrt (ckQExp q t ϱ π n (fun σ G U => ∑ τ, ckPost q t ϱ G U σ τ * rsDevSq τ)) :=
        ck_QExp_sqrt_le hp hϱ hπ0 hπ1 hg0 hdom_g
    _ = Real.sqrt (((q : ℝ) - 1) / (q * n)) := by
        rw [← hEdev]
        exact congrArg Real.sqrt hnish.symm
    _ ≤ 1 / Real.sqrt n := hfin

/-- Minkowski: `‖∑_i w_i x_i‖₂ ≤ ∑_i w_i ‖x_i‖₂` for nonnegative weights. -/
private lemma CKPlantedB_minkowski {ι κ : Type*} [Fintype ι] [Fintype κ] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (x : ι → κ → ℝ) (y : κ → ℝ) (hy : ∀ c, y c = ∑ i, w i * x i c) :
    Real.sqrt (∑ c, y c ^ 2) ≤ ∑ i, w i * Real.sqrt (∑ c, x i c ^ 2) := by
  have hN0 : 0 ≤ Real.sqrt (∑ c, y c ^ 2) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (∑ c, y c ^ 2) ^ 2 = ∑ c, y c ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hyy : ∀ c, y c ^ 2 = ∑ i, w i * x i c * y c := fun c => by
    rw [sq, ← Finset.sum_mul, ← hy c]
  have h1 : ∑ c, y c ^ 2 = ∑ i, w i * ∑ c, x i c * y c := by
    calc ∑ c, y c ^ 2 = ∑ c, ∑ i, w i * x i c * y c := Finset.sum_congr rfl fun c _ => hyy c
      _ = ∑ i, ∑ c, w i * x i c * y c := Finset.sum_comm
      _ = ∑ i, w i * ∑ c, x i c * y c := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∀ i, ∑ c, x i c * y c ≤ Real.sqrt (∑ c, x i c ^ 2) * Real.sqrt (∑ c, y c ^ 2) :=
    fun i => Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h3 : Real.sqrt (∑ c, y c ^ 2) * Real.sqrt (∑ c, y c ^ 2) ≤
      (∑ i, w i * Real.sqrt (∑ c, x i c ^ 2)) * Real.sqrt (∑ c, y c ^ 2) := by
    have e : Real.sqrt (∑ c, y c ^ 2) * Real.sqrt (∑ c, y c ^ 2) =
        ∑ i, w i * ∑ c, x i c * y c := by
      rw [← sq, hsq, h1]
    rw [e, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ => by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (h2 i) (hw i)
  rcases hN0.eq_or_lt with h | h
  · rw [← h]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _)
  · exact le_of_mul_le_mul_right h3 h

/-- The bound `‖m̄_μ - u‖₂ ≤ dev(μ)` of Lemma 4.4(b), for the mean marginal
`m̄_μ = n⁻¹ ∑_v μ_v`: `m̄_μ - u = ⟨λ_τ - u⟩_μ`, and the norm is convex (Minkowski).  The
hypothesis `0 < n` is not used. -/
theorem ck_mean_dev_le {q n : ℕ} (hn : 0 < n) {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    Real.sqrt (∑ c, ((n : ℝ)⁻¹ * ∑ v, ckMarg μ v c - (q : ℝ)⁻¹) ^ 2) ≤ ckDev μ := by
  obtain ⟨h0, h1⟩ := hμ
  have hmarg : ∀ c : Fin q, ∑ v, ckMarg μ v c = ∑ τ, μ τ * (fiberCard τ c : ℝ) := by
    intro c
    unfold ckMarg
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    unfold fiberCard
    congr 2
    congr 1
    ext v
    simp
  have hy : ∀ c : Fin q, (n : ℝ)⁻¹ * ∑ v, ckMarg μ v c - (q : ℝ)⁻¹ =
      ∑ τ, μ τ * (colorFrac τ c - 1 / (q : ℝ)) := by
    intro c
    rw [hmarg c]
    calc (n : ℝ)⁻¹ * ∑ τ, μ τ * (fiberCard τ c : ℝ) - (q : ℝ)⁻¹
        = ∑ τ, μ τ * colorFrac τ c - (∑ τ, μ τ) * (1 / (q : ℝ)) := by
          rw [h1, one_mul, one_div, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun τ _ => ?_
          unfold colorFrac
          ring
      _ = ∑ τ, μ τ * (colorFrac τ c - 1 / (q : ℝ)) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun τ _ => by ring
  exact CKPlantedB_minkowski μ h0 (fun τ c => colorFrac τ c - 1 / (q : ℝ)) _ hy

/-! ### Pin cost (Lemma 4.6) -/

private lemma CKPlantedB_agree_union {n q : ℕ} (U X : Finset (Fin n)) (σ τ : Fin n → Fin q) :
    ckAgree (U ∪ X) σ τ ↔ ckAgree U σ τ ∧ ckAgree X σ τ := by
  unfold ckAgree
  simp only [Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun v hv => h v (Or.inl hv), fun v hv => h v (Or.inr hv)⟩
  · rintro ⟨h1, h2⟩ v (hv | hv)
    exacts [h1 v hv, h2 v hv]

/-- The posterior mass of the cylinder `{τ' : τ'_X = σ_X}` is `Z_{U ∪ X}(σ) / Z_U(σ)`. -/
private lemma CKPlantedB_cyl_post {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (U X : Finset (Fin n))
    (σ : Fin n → Fin q) :
    ckCyl (ckPost q t ϱ G U σ) X σ =
      (∑ τ' with ckAgree (U ∪ X) σ τ', ckL q t ϱ G τ') /
        ∑ τ' with ckAgree U σ τ', ckL q t ϱ G τ' := by
  unfold ckCyl ckPost
  generalize (∑ τ' with ckAgree U σ τ', ckL q t ϱ G τ') = Z
  rw [Finset.sum_div, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [CKPlantedB_agree_union]
  by_cases hX : ckAgree X σ τ <;> by_cases hU : ckAgree U σ τ <;> simp [hX, hU]

/-- `F̃(G, U ∪ X, σ) = F̃(G, U, σ) · post_{G,U,σ}(τ_X = σ_X)`. -/
private lemma CKPlantedB_Ft_union {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U X : Finset (Fin n)) (σ : Fin n → Fin q) :
    ckFt q t ϱ G (U ∪ X) σ = ckFt q t ϱ G U σ * ckCyl (ckPost q t ϱ G U σ) X σ := by
  rw [CKPlantedB_cyl_post]
  unfold ckFt
  have := (CKPlantedB_Z_pos hp hϱ G U σ).ne'
  field_simp

private lemma CKPlantedB_post_congr {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (U : Finset (Fin n))
    {ς ς' : Fin n → Fin q} (h : ckAgree U ς ς') :
    ckPost q t ϱ G U ς = ckPost q t ϱ G U ς' := by
  funext τ
  unfold ckPost
  rw [CKPlantedB_Z_congr t ϱ G h]
  by_cases h1 : ckAgree U ς τ
  · have h2 : ckAgree U ς' τ := (CKPlantedB_agree_trans_iff h τ).mp h1
    rw [if_pos h1, if_pos h2]
  · have h2 : ¬ ckAgree U ς' τ := fun h2 => h1 ((CKPlantedB_agree_trans_iff h τ).mpr h2)
    rw [if_neg h1, if_neg h2]

private lemma CKPlantedB_post_eq {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (U : Finset (Fin n))
    {ς τ : Fin n → Fin q} (h : ckAgree U ς τ) :
    ckPost q t ϱ G U ς τ = ckL q t ϱ G τ / ∑ τ' with ckAgree U ς τ', ckL q t ϱ G τ' := by
  unfold ckPost
  rw [if_pos h]

private lemma CKPlantedB_post_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) {ς τ : Fin n → Fin q} (h : ckAgree U ς τ) :
    0 < ckPost q t ϱ G U ς τ := by
  rw [CKPlantedB_post_eq t ϱ G U h]
  exact div_pos (CKPlantedB_L_pos hp hϱ G τ) (CKPlantedB_Z_pos hp hϱ G U ς)

private lemma CKPlantedB_post_le_cyl {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U X : Finset (Fin n)) (ς τ : Fin n → Fin q) :
    ckPost q t ϱ G U ς τ ≤ ckCyl (ckPost q t ϱ G U ς) X τ := by
  unfold ckCyl
  refine Finset.single_le_sum (f := ckPost q t ϱ G U ς)
    (fun τ' _ => (ck_post_isPMF hp hϱ G U ς).1 τ') ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact CKPlantedB_agree_refl X τ

private lemma CKPlantedB_cyl_le_one {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U X : Finset (Fin n)) (ς τ : Fin n → Fin q) :
    ckCyl (ckPost q t ϱ G U ς) X τ ≤ 1 := by
  obtain ⟨h0, h1⟩ := ck_post_isPMF hp hϱ G U ς
  unfold ckCyl
  rw [← h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun τ' _ _ => h0 τ')

private lemma CKPlantedB_cyl_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U X : Finset (Fin n)) {ς τ : Fin n → Fin q} (h : ckAgree U ς τ) :
    0 < ckCyl (ckPost q t ϱ G U ς) X τ :=
  lt_of_lt_of_le (CKPlantedB_post_pos hp hϱ G U h) (CKPlantedB_post_le_cyl hp hϱ G U X ς τ)

private lemma CKPlantedB_abs_log_le_inv {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hx1 : x ≤ 1) :
    |Real.log x| ≤ a⁻¹ := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  rw [abs_of_nonpos (Real.log_nonpos hx.le hx1)]
  have h1 : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h1
  have h2 : x⁻¹ ≤ a⁻¹ := inv_anti₀ ha hax
  linarith

private lemma CKPlantedB_sum_L_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    (∑ τ' with ckAgree U ς τ', ckL q t ϱ G τ') ≤
      (q : ℝ) ^ n * (Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G) := by
  calc (∑ τ' with ckAgree U ς τ', ckL q t ϱ G τ') ≤ ∑ τ', ckL q t ϱ G τ' :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun τ' _ _ => (CKPlantedB_L_pos hp hϱ G τ').le)
    _ ≤ ∑ _τ' : Fin n → Fin q, Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G :=
        Finset.sum_le_sum fun τ' _ => (ck_L_mem hp hϱ G τ').2.1
    _ = (q : ℝ) ^ n * (Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp only [Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- `|log post_{G,U,ς}(τ'_X = τ_X)| ≤ q^n e^{ϱn²} (m₊/m₋)^{|G|}` on the pinned class. -/
private lemma CKPlantedB_log_cyl_bound {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U X : Finset (Fin n)) {ς τ : Fin n → Fin q} (h : ckAgree U ς τ) :
    |Real.log (ckCyl (ckPost q t ϱ G U ς) X τ)| ≤
      ((q : ℝ) ^ n * Real.exp (ϱ * (n : ℝ) ^ 2)) * (ckMp t / ckMm q t) ^ rsEdges G := by
  refine (CKPlantedB_abs_log_le_inv (CKPlantedB_post_pos hp hϱ G U h)
    (CKPlantedB_post_le_cyl hp hϱ G U X ς τ) (CKPlantedB_cyl_le_one hp hϱ G U X ς τ)).trans ?_
  rw [CKPlantedB_post_eq t ϱ G U h, inv_div, div_pow]
  have hZle := CKPlantedB_sum_L_le hp hϱ G U ς
  have hLge := (ck_L_mem hp hϱ G τ).1
  have hMm := CKPlantedB_Mm_pos hp
  calc (∑ τ' with ckAgree U ς τ', ckL q t ϱ G τ') / ckL q t ϱ G τ
      ≤ ((q : ℝ) ^ n * (Real.exp (ϱ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges G)) /
          ckMm q t ^ rsEdges G :=
        div_le_div₀ (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (mul_nonneg
          (Real.exp_pos _).le (pow_nonneg (by linarith [(ck_const_bounds hp).2.2.1]) _)))
          hZle (pow_pos hMm _) hLge
    _ = ((q : ℝ) ^ n * Real.exp (ϱ * (n : ℝ) ^ 2)) *
          (ckMp t ^ rsEdges G / ckMm q t ^ rsEdges G) := by ring

private lemma CKPlantedB_dom_const {q n : ℕ} (c : ℝ) :
    CKDom (fun (_ : Fin n → Fin q) (_ : RSGraph n) (_ : Finset (Fin n)) => c) :=
  ⟨|c|, 1, zero_le_one, fun _ _ _ => by rw [one_pow, mul_one]⟩

private lemma CKPlantedB_dom_logFt {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    CKDom (fun (σ : Fin n → Fin q) G U => Real.log (ckFt q t ϱ G U σ)) :=
  ⟨_, 2, by norm_num, fun σ G U => CKPlantedB_logFt_dom hp hϱ G U σ⟩

private lemma CKPlantedB_dom_logCyl {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (X : Finset (Fin n)) :
    CKDom (fun (σ : Fin n → Fin q) G U => Real.log (ckCyl (ckPost q t ϱ G U σ) X σ)) :=
  ⟨_, ckMp t / ckMm q t,
    div_nonneg (by linarith [(ck_const_bounds hp).2.2.1]) (CKPlantedB_Mm_pos hp).le,
    fun σ G U => CKPlantedB_log_cyl_bound hp hϱ G U X (CKPlantedB_agree_refl U σ)⟩

/-- Lemma 1.3(a) inside `E_𝖰`: pins `U' ∼ Bern(π')` with `1 - π' = (1 - π)(1 - π_x)` are
realized as `U ∪ X`, with independent `U ∼ Bern(π)` and `X ∼ Bern(π_x)`. -/
private lemma CKPlantedB_QExp_union {q n : ℕ} (t ϱ π πx : ℝ)
    (F : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) :
    ckQExp q t ϱ (1 - (1 - π) * (1 - πx)) n F =
      ∑ X, ckBern πx X * ckQExp q t ϱ π n (fun σ G U => F σ G (U ∪ X)) := by
  unfold ckQExp
  have hT : ∀ σ : Fin n → Fin q,
      ∑ U, ckBern (1 - (1 - π) * (1 - πx)) U * ∑' G, poisPi (ckPl q t ϱ σ) G * F σ G U =
        ∑ A, ∑ W, ckBern π A * ckBern πx W *
          ∑' G, poisPi (ckPl q t ϱ σ) G * F σ G (A ∪ W) :=
    fun σ => (ck_bern_union π πx (fun U => ∑' G, poisPi (ckPl q t ϱ σ) G * F σ G U)).symm
  simp_rw [hT, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

/-- For a fixed extra pin set `X`: `E log F̃(U ∪ X) ∈ [𝒦(π) - |X| log q, 𝒦(π)]`. -/
private lemma CKPlantedB_pin_fixed {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ} (hϱ : 0 ≤ ϱ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (X : Finset (Fin n)) :
    ckK q t ϱ π n - X.card * Real.log q ≤
        ckQExp q t ϱ π n (fun σ G U => Real.log (ckFt q t ϱ G (U ∪ X) σ)) ∧
      ckQExp q t ϱ π n (fun σ G U => Real.log (ckFt q t ϱ G (U ∪ X) σ)) ≤ ckK q t ϱ π n := by
  have hsplit : ckQExp q t ϱ π n (fun σ G U => Real.log (ckFt q t ϱ G (U ∪ X) σ)) =
      ckK q t ϱ π n +
        ckQExp q t ϱ π n (fun σ G U => Real.log (ckCyl (ckPost q t ϱ G U σ) X σ)) := by
    unfold ckK
    rw [← ck_QExp_add hp hϱ π (CKPlantedB_dom_logFt hp hϱ) (CKPlantedB_dom_logCyl hp hϱ X)]
    congr 1
    funext σ G U
    rw [CKPlantedB_Ft_union hp hϱ G U X σ, Real.log_mul (ck_Ft_pos hp hϱ G U σ).ne'
      (CKPlantedB_cyl_pos hp hϱ G U X (CKPlantedB_agree_refl U σ)).ne']
  have hc : 0 ≤ ckMp t / ckMm q t :=
    div_nonneg (by linarith [(ck_const_bounds hp).2.2.1]) (CKPlantedB_Mm_pos hp).le
  have hnish : ckQExp q t ϱ π n (fun σ G U => Real.log (ckCyl (ckPost q t ϱ G U σ) X σ)) =
      ckQExp q t ϱ π n (fun σ G U => -ckH (ckPost q t ϱ G U σ) X) := by
    refine (ck_nishimori hp hϱ π
      (fun τ G U ς => Real.log (ckCyl (ckPost q t ϱ G U ς) X τ))
      (fun τ G U ς ς' h => by rw [CKPlantedB_post_congr t ϱ G U h]) hc
      (fun τ G U ς h => CKPlantedB_log_cyl_bound hp hϱ G U X h)).trans ?_
    congr 1
    funext σ G U
    unfold ckH
    rw [neg_neg]
  have hdomH : CKDom (fun (σ : Fin n → Fin q) G U => -ckH (ckPost q t ϱ G U σ) X) :=
    ⟨X.card * Real.log q, 1, zero_le_one, fun σ G U => by
      have hP := ck_post_isPMF hp hϱ G U σ
      rw [one_pow, mul_one, abs_neg, abs_of_nonneg (ck_H_nonneg hP X)]
      exact ck_H_le hP X⟩
  have hlow : -(X.card * Real.log q) ≤
      ckQExp q t ϱ π n (fun σ G U => Real.log (ckCyl (ckPost q t ϱ G U σ) X σ)) := by
    rw [hnish]
    have h := ck_QExp_mono hp hϱ hπ0 hπ1 (CKPlantedB_dom_const (q := q) (n := n)
      (-(X.card * Real.log q))) hdomH
      (fun σ G U => neg_le_neg (ck_H_le (ck_post_isPMF hp hϱ G U σ) X))
    rwa [ck_QExp_const hp hϱ π] at h
  have hup : ckQExp q t ϱ π n (fun σ G U => Real.log (ckCyl (ckPost q t ϱ G U σ) X σ)) ≤ 0 := by
    have h := ck_QExp_mono hp hϱ hπ0 hπ1 (CKPlantedB_dom_logCyl hp hϱ X)
      (CKPlantedB_dom_const (q := q) (n := n) 0)
      (fun σ G U => Real.log_nonpos
        (CKPlantedB_cyl_pos hp hϱ G U X (CKPlantedB_agree_refl U σ)).le
        (CKPlantedB_cyl_le_one hp hϱ G U X σ σ))
    rwa [ck_QExp_const hp hϱ π] at h
  rw [hsplit]
  constructor <;> linarith

/-- Lemma 4.6 (pin cost), for constant pin probabilities: if `1 - π' = (1 - π)(1 - π_x)`, then
`𝒦(ϱ, π) - n π_x log q ≤ 𝒦(ϱ, π') ≤ 𝒦(ϱ, π)`.  Proof: realize the pins as `U ∪ X`; then
`F̃(G, U ∪ X, σ) = F̃(G, U, σ) post_{G,U,σ}(τ_X = σ_X)`.  For fixed `X`, Lemma 4.3 turns the
expected logarithm of the last factor into `-E_𝖰 h_post(X) ∈ [-|X| log q, 0]`, and
`E|X| = n π_x`. -/
theorem ck_pin_cost {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π πx : ℝ} (hϱ : 0 ≤ ϱ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (hx0 : 0 ≤ πx) (hx1 : πx ≤ 1) :
    ckK q t ϱ π n - n * πx * Real.log q ≤ ckK q t ϱ (1 - (1 - π) * (1 - πx)) n ∧
      ckK q t ϱ (1 - (1 - π) * (1 - πx)) n ≤ ckK q t ϱ π n := by
  have hcomb : ckK q t ϱ (1 - (1 - π) * (1 - πx)) n = ∑ X, ckBern πx X *
      ckQExp q t ϱ π n (fun σ G U => Real.log (ckFt q t ϱ G (U ∪ X) σ)) :=
    CKPlantedB_QExp_union t ϱ π πx _
  have hB0 : ∀ X : Finset (Fin n), 0 ≤ ckBern πx X := ck_bern_nonneg hx0 hx1
  have hfix := CKPlantedB_pin_fixed hp hϱ hπ0 hπ1 (n := n)
  rw [hcomb]
  constructor
  · have e1 : ∑ X : Finset (Fin n), ckBern πx X * (ckK q t ϱ π n - X.card * Real.log q) =
        ckK q t ϱ π n - n * πx * Real.log q := by
      have e2 : ∑ X : Finset (Fin n), ckBern πx X * (ckK q t ϱ π n - X.card * Real.log q) =
          (∑ X : Finset (Fin n), ckBern πx X) * ckK q t ϱ π n -
            (∑ X : Finset (Fin n), ckBern πx X * X.card) * Real.log q := by
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun X _ => by ring
      rw [e2, ck_bern_sum, ck_bern_card]
      ring
    rw [← e1]
    exact Finset.sum_le_sum fun X _ => mul_le_mul_of_nonneg_left (hfix X).1 (hB0 X)
  · calc ∑ X, ckBern πx X *
          ckQExp q t ϱ π n (fun σ G U => Real.log (ckFt q t ϱ G (U ∪ X) σ))
        ≤ ∑ X : Finset (Fin n), ckBern πx X * ckK q t ϱ π n :=
          Finset.sum_le_sum fun X _ => mul_le_mul_of_nonneg_left (hfix X).2 (hB0 X)
      _ = ckK q t ϱ π n := by rw [← Finset.sum_mul, ck_bern_sum, one_mul]

/-! ### Corollary 4.9 -/

private lemma CKPlantedB_pin_mem {s : ℝ} (hs : 0 ≤ s) (k N : ℕ) :
    0 ≤ ckPin s k N ∧ ckPin s k N ≤ 1 := by
  unfold ckPin
  have h0 : 0 ≤ (k : ℝ) * s / N := by positivity
  have h1 : Real.exp (-((k : ℝ) * s / N)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.exp_pos (-((k : ℝ) * s / N))
  constructor <;> linarith

private lemma CKPlantedB_pin_zero (s : ℝ) (N : ℕ) : ckPin s 0 N = 0 := by
  unfold ckPin
  simp

private lemma CKPlantedB_N_mul_pin_le {s : ℝ} {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (N : ℝ) * ckPin s k N ≤ k * s := by
  unfold ckPin
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h := Real.add_one_le_exp (-((k : ℝ) * s / N))
  have h2 : 1 - Real.exp (-((k : ℝ) * s / N)) ≤ k * s / N := by linarith
  calc (N : ℝ) * (1 - Real.exp (-((k : ℝ) * s / N))) ≤ N * (k * s / N) :=
        mul_le_mul_of_nonneg_left h2 hNpos.le
    _ = k * s := by field_simp

/-- Corollary 4.9(a): `a_N(0) ≤ a_N(k) + ks log q`, by Lemma 4.6 with `π = 0` and
`π_x = π_k(N) ≤ ks/N`. -/
theorem ck_A_zero_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 ≤ s) {N : ℕ}
    (hN : 0 < N) (k : ℕ) : ckA q t s N 0 ≤ ckA q t s N k + k * s * Real.log q := by
  have hϱ : 0 ≤ s / (2 * (N : ℝ)) := by positivity
  obtain ⟨hx0, hx1⟩ := CKPlantedB_pin_mem hs k N
  have h := (ck_pin_cost (n := N) (π := 0) hp hϱ le_rfl zero_le_one hx0 hx1).1
  rw [show (1 - (1 - (0 : ℝ)) * (1 - ckPin s k N)) = ckPin s k N by ring] at h
  have hb := mul_le_mul_of_nonneg_right (CKPlantedB_N_mul_pin_le (s := s) hN k)
    (CKPlantedB_logq_nonneg hp)
  unfold ckA
  rw [CKPlantedB_pin_zero]
  linarith

/-- The mean number of edges of a Poisson multigraph: `E_{𝖯_lam} |G| = ∑_e lam_e`. -/
private lemma CKPlantedB_hasSum_edges {n : ℕ} {lam : Fin n × Fin n → ℝ} (hlam : ∀ e, 0 ≤ lam e) :
    HasSum (fun G : RSGraph n => poisPi lam G * (rsEdges G : ℝ)) (∑ e, lam e) := by
  have hone : ∀ e, HasSum (fun G : RSGraph n => poisPi lam G * (G e : ℝ)) (lam e) := by
    intro e
    have h1 : HasSum (fun k : ℕ => poisPMF (lam e) k * (k : ℝ)) (lam e) := by
      have hs := summable_poisPMF_mul_pow (hlam e) 1
      simp only [pow_one] at hs
      have h := hs.hasSum
      rwa [show (∑' k : ℕ, poisPMF (lam e) k * (k : ℝ)) = lam e from
        poisExp_natCast (hlam e)] at h
    have H := rs_hasSum_poisPi_mul_prod hlam (fun i k => if i = e then (k : ℝ) else 1)
      (fun i k => by split_ifs <;> positivity) (fun i => if i = e then lam e else 1)
      (fun i => by
        by_cases h : i = e
        · simpa [h] using h1
        · simp only [h, if_false, mul_one]
          exact hasSum_poisPMF (hlam i))
    simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true] at H
    exact H
  have hsum := hasSum_sum (s := Finset.univ) (fun e _ => hone e)
  refine hsum.congr_fun fun G => ?_
  unfold rsEdges
  push_cast
  rw [Finset.mul_sum]

private lemma CKPlantedB_abs_inner_logFt {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (U : Finset (Fin n)) :
    |∑' G, poisPi (ckPl q t ϱ σ) G * Real.log (ckFt q t ϱ G U σ)| ≤
      n * Real.log q + ϱ * (n : ℝ) ^ 2 + ckEll q t * (ϱ * (n : ℝ) ^ 2 * ckMp t) := by
  have hlam := CKPlantedB_pl_nonneg hp hϱ σ
  have hE := CKPlantedB_hasSum_edges hlam
  have h1 := rs_hasSum_poisPi hlam
  have hg0 := (h1.mul_right ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2)).add
    (hE.mul_right (ckEll q t))
  have hg : HasSum (fun G => poisPi (ckPl q t ϱ σ) G *
      ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + rsEdges G * ckEll q t))
      ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + ckEll q t * ∑ e, ckPl q t ϱ σ e) := by
    rw [show (n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + ckEll q t * ∑ e, ckPl q t ϱ σ e =
      1 * ((n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2) + (∑ e, ckPl q t ϱ σ e) * ckEll q t by ring]
    exact hg0.congr_fun fun G => by ring
  have hle := tsum_of_norm_bounded
    (f := fun G => poisPi (ckPl q t ϱ σ) G * Real.log (ckFt q t ϱ G U σ)) hg (fun G => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rs_poisPi_nonneg hlam G)]
    exact mul_le_mul_of_nonneg_left (ck_abs_log_Ft_le hp hϱ G U σ) (rs_poisPi_nonneg hlam G))
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hsum : ∑ e, ckPl q t ϱ σ e ≤ ϱ * (n : ℝ) ^ 2 * ckMp t := by
    calc ∑ e, ckPl q t ϱ σ e ≤ ∑ _e : Fin n × Fin n, ϱ * ckMp t :=
          Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (ck_rsM_mem hp _ _).2 hϱ
      _ = ϱ * (n : ℝ) ^ 2 * ckMp t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  have hell := CKPlantedB_ell_nonneg hp
  nlinarith [mul_le_mul_of_nonneg_left hsum hell]

/-- `|E_𝖰 f| ≤ C` when every inner multigraph expectation is bounded by `C`. -/
private lemma CKPlantedB_abs_QExp_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ π : ℝ}
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ)
    {C : ℝ} (h : ∀ σ U, |∑' G, poisPi (ckPl q t ϱ σ) G * f σ G U| ≤ C) :
    |ckQExp q t ϱ π n f| ≤ C := by
  unfold ckQExp
  have hq := CKPlantedB_qn_pos hp n
  rw [abs_mul, abs_of_pos (inv_pos.mpr hq), inv_mul_le_iff₀ hq]
  calc |∑ σ, ∑ U, ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * f σ G U|
      ≤ ∑ σ : Fin n → Fin q, ∑ U : Finset (Fin n),
          |ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * f σ G U| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun σ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _σ : Fin n → Fin q, ∑ U : Finset (Fin n), ckBern π U * C := by
        refine Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun U _ => ?_
        rw [abs_mul, abs_of_nonneg (ck_bern_nonneg hπ0 hπ1 U)]
        exact mul_le_mul_of_nonneg_left (h σ U) (ck_bern_nonneg hπ0 hπ1 U)
    _ = (q : ℝ) ^ n * C := by
        simp_rw [← Finset.sum_mul, ck_bern_sum]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp only [Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- Corollary 4.9(b): `|a_N(k)| ≤ N log q + (sN/2)(1 + m₊ ℓ₀)`, by Lemma 4.2(b) and
`E|G| ≤ ϱN² m₊`, with `ϱN² = sN/2`. -/
theorem ck_abs_A_le {q : ℕ} {t : ℝ} (hp : CKPar q t) {s : ℝ} (hs : 0 ≤ s) {N : ℕ}
    (hN : 0 < N) (k : ℕ) :
    |ckA q t s N k| ≤ N * Real.log q + s * N / 2 * (1 + ckMp t * ckEll q t) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hϱ : 0 ≤ s / (2 * (N : ℝ)) := by positivity
  obtain ⟨hx0, hx1⟩ := CKPlantedB_pin_mem hs k N
  have hρN : s / (2 * (N : ℝ)) * (N : ℝ) ^ 2 = s * N / 2 := by
    field_simp
  unfold ckA ckK
  refine CKPlantedB_abs_QExp_le hp hx0 hx1 _ fun σ U => ?_
  refine (CKPlantedB_abs_inner_logFt hp hϱ σ U).trans (le_of_eq ?_)
  rw [hρN]
  ring

end

end ERZeroFreeness
