/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKMatrix
import ERZeroFreeness.CKAnalysis
import ERZeroFreeness.CKInfo
import ERZeroFreeness.CKPlanted
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Stage B of Appendix C: Lemmas 5.1–5.4 of the self-contained proof of [CKPZ, Prop. 3.6]

Proof of `CKPZProp36 q` (the Potts specialization of Coja-Oghlan–Krzakala–Perkins–Zdeborová,
Proposition 3.6) from first principles.  The mathematics, with every lemma, constant and limit
order, is in `docs/appendixC/ckpz-proof.md` (Lemmas 5.1–5.4; its §12 is the Lean plan these frozen
statements come from).  Frozen statements must not be changed; provers add helpers freely.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section


/-! ### Part A helpers (Lemmas 5.1–5.2) -/

private lemma CKEdgeA_Mm_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) : 0 < ckMm q t :=
  (ck_const_bounds hp).1

private lemma CKEdgeA_one_le_Mp {q : ℕ} {t : ℝ} (hp : CKPar q t) : 1 ≤ ckMp t :=
  (ck_const_bounds hp).2.2.1.le

private lemma CKEdgeA_rsM_pos {q : ℕ} {t : ℝ} (hp : CKPar q t) (a b : Fin q) :
    0 < rsM q t a b :=
  lt_of_lt_of_le (CKEdgeA_Mm_pos hp) (ck_rsM_mem hp a b).1

private lemma CKEdgeA_L_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ : ℝ) (G : RSGraph n)
    (τ : Fin n → Fin q) : 0 < ckL q t ϱ G τ := by
  unfold ckL rsW
  exact mul_pos (Real.exp_pos _)
    (Finset.prod_pos fun e _ => pow_pos (CKEdgeA_rsM_pos hp _ _) _)

private lemma CKEdgeA_Pl_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (e : Fin n × Fin n) : 0 ≤ ckPl q t ϱ σ e :=
  mul_nonneg hϱ (CKEdgeA_rsM_pos hp _ _).le

private lemma CKEdgeA_Pl_add {q n : ℕ} (t ϱ δ : ℝ) (σ : Fin n → Fin q) :
    ckPl q t (ϱ + δ) σ = ckPl q t ϱ σ + ckPl q t δ σ := by
  funext e
  simp only [ckPl, Pi.add_apply]
  ring

private lemma CKEdgeA_hasSum_Pl {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    (τ : Fin n → Fin q) : HasSum (fun H : RSGraph n => poisPi (ckPl q t δ τ) H) 1 :=
  rs_hasSum_poisPi (CKEdgeA_Pl_nonneg hp hδ τ)

private lemma CKEdgeA_hasSum_PL {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    (τ : Fin n → Fin q) :
    HasSum (fun H : RSGraph n => poisPi (fun _ => δ) H * ckL q t δ H τ) 1 :=
  (CKEdgeA_hasSum_Pl hp hδ τ).congr_fun fun H => (ck_pl_eq t δ τ H).symm

private lemma CKEdgeA_avgL_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (H : RSGraph n) :
    ckMm q t ^ rsEdges H ≤ ∑ τ, μ τ * ckL q t δ H τ ∧
      ∑ τ, μ τ * ckL q t δ H τ ≤ Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H := by
  constructor
  · calc ckMm q t ^ rsEdges H = ∑ τ, μ τ * ckMm q t ^ rsEdges H := by
          rw [← Finset.sum_mul, hμ.2, one_mul]
      _ ≤ ∑ τ, μ τ * ckL q t δ H τ :=
          Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (ck_L_mem hp hδ H τ).1 (hμ.1 τ)
  · calc ∑ τ, μ τ * ckL q t δ H τ
        ≤ ∑ τ, μ τ * (Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H) :=
          Finset.sum_le_sum fun τ _ =>
            mul_le_mul_of_nonneg_left (ck_L_mem hp hδ H τ).2.1 (hμ.1 τ)
      _ = Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H := by
          rw [← Finset.sum_mul, hμ.2, one_mul]

private lemma CKEdgeA_avgL_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (H : RSGraph n) :
    0 < ∑ τ, μ τ * ckL q t δ H τ :=
  lt_of_lt_of_le (pow_pos (CKEdgeA_Mm_pos hp) _) (CKEdgeA_avgL_mem hp hδ hμ H).1

private lemma CKEdgeA_abs_lam_le {y : ℝ} (hy : 0 ≤ y) : |ckLam y| ≤ 1 + y ^ 2 := by
  unfold ckLam
  rcases le_or_gt y 1 with h | h
  · rcases hy.eq_or_lt with h0 | h0
    · subst h0; simp
    · have h1 := Real.abs_log_mul_self_lt y h0 h
      rw [mul_comm] at h1
      nlinarith [sq_nonneg y]
  · have hlog0 : 0 ≤ Real.log y := Real.log_nonneg h.le
    have hlog1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [abs_of_nonneg (mul_nonneg (by linarith) hlog0)]
    nlinarith

private lemma CKEdgeA_lam_ge {y : ℝ} (hy : 0 ≤ y) : y - 1 ≤ ckLam y := by
  have h := InformationTheory.klFun_nonneg hy
  unfold InformationTheory.klFun at h
  unfold ckLam
  linarith

/-- The dominating function `1 + (e^{δ n²} m₊^{|H|})²` of `|Λ(⟨L_δ(H)⟩_μ)|`. -/
private def CKEdgeA_g (t δ : ℝ) {n : ℕ} (H : RSGraph n) : ℝ :=
  1 + (Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H) ^ 2

private lemma CKEdgeA_g_nonneg (t δ : ℝ) {n : ℕ} (H : RSGraph n) : 0 ≤ CKEdgeA_g t δ H := by
  unfold CKEdgeA_g; positivity

private lemma CKEdgeA_g_summable {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ) :
    Summable (fun H : RSGraph n => poisPi (fun _ => δ) H * CKEdgeA_g t δ H) := by
  refine rs_summable_poisPi_of_abs_le (fun _ => hδ)
    (A := 1 + Real.exp (δ * (n : ℝ) ^ 2) ^ 2) (c := ckMp t ^ 2) (by positivity) fun H => ?_
  have h1 : 1 ≤ (ckMp t ^ 2) ^ (∑ i, H i) := one_le_pow₀ (one_le_pow₀ (CKEdgeA_one_le_Mp hp))
  have h2 : (ckMp t ^ rsEdges H) ^ 2 = (ckMp t ^ 2) ^ (∑ i, H i) := by
    rw [← pow_mul, ← pow_mul, mul_comm]; rfl
  rw [abs_of_nonneg (CKEdgeA_g_nonneg t δ H)]
  unfold CKEdgeA_g
  rw [mul_pow, h2]
  nlinarith [sq_nonneg (Real.exp (δ * (n : ℝ) ^ 2))]

private lemma CKEdgeA_abs_lam_le_g {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (H : RSGraph n) :
    |ckLam (∑ τ, μ τ * ckL q t δ H τ)| ≤ CKEdgeA_g t δ H := by
  have hm := CKEdgeA_avgL_mem hp hδ hμ H
  have hpos := CKEdgeA_avgL_pos hp hδ hμ H
  refine (CKEdgeA_abs_lam_le hpos.le).trans ?_
  unfold CKEdgeA_g
  have := pow_le_pow_left₀ hpos.le hm.2 2
  linarith

private lemma CKEdgeA_xi_summable {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    Summable (fun H : RSGraph n =>
      poisPi (fun _ => δ) H * ckLam (∑ τ, μ τ * ckL q t δ H τ)) := by
  refine Summable.of_norm_bounded (CKEdgeA_g_summable hp hδ) fun H => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rs_poisPi_nonneg (fun _ => hδ) H)]
  exact mul_le_mul_of_nonneg_left (CKEdgeA_abs_lam_le_g hp hδ hμ H)
    (rs_poisPi_nonneg (fun _ => hδ) H)

private lemma CKEdgeA_hasSum_avgL {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    HasSum (fun H : RSGraph n => poisPi (fun _ => δ) H * ∑ τ, μ τ * ckL q t δ H τ) 1 := by
  have h := hasSum_sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
    (CKEdgeA_hasSum_PL hp hδ τ).mul_left (μ τ)
  simp only [mul_one, hμ.2] at h
  refine h.congr_fun fun H => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

private lemma CKEdgeA_xi_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) : 0 ≤ ckXi q t δ μ := by
  have h1 := CKEdgeA_hasSum_avgL hp hδ hμ
  have h2 : HasSum (fun H : RSGraph n => poisPi (fun _ => δ) H) 1 :=
    rs_hasSum_poisPi (fun _ => hδ)
  have h3 := h1.sub h2
  rw [sub_self] at h3
  unfold ckXi
  rw [← h3.tsum_eq]
  refine Summable.tsum_le_tsum (fun H => ?_) h3.summable (CKEdgeA_xi_summable hp hδ hμ)
  rw [← mul_sub_one]
  exact mul_le_mul_of_nonneg_left (CKEdgeA_lam_ge (CKEdgeA_avgL_pos hp hδ hμ H).le)
    (rs_poisPi_nonneg (fun _ => hδ) H)

private lemma CKEdgeA_xi_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    ckXi q t δ μ ≤ ∑' H : RSGraph n, poisPi (fun _ => δ) H * CKEdgeA_g t δ H := by
  unfold ckXi
  refine Summable.tsum_le_tsum (fun H => ?_) (CKEdgeA_xi_summable hp hδ hμ)
    (CKEdgeA_g_summable hp hδ)
  exact mul_le_mul_of_nonneg_left (le_of_abs_le (CKEdgeA_abs_lam_le_g hp hδ hμ H))
    (rs_poisPi_nonneg (fun _ => hδ) H)

private lemma CKEdgeA_lin_le_two_pow {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (k : ℕ) :
    a + k * b ≤ (a + b) * 2 ^ k := by
  have h1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have h2 : (k : ℝ) ≤ 2 ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  nlinarith

/-- Superposition of the planted edge law: `𝖯^σ_{ϱ+Δ} = 𝖯^σ_ϱ ⊛ 𝖯^σ_Δ` inside `E_𝖰`. -/
private lemma CKEdgeA_QExp_superpose {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ Δ : ℝ}
    (hϱ : 0 ≤ ϱ) (hΔ : 0 ≤ Δ) (π : ℝ)
    (f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) {A c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ σ G U, |f σ G U| ≤ A * c ^ rsEdges G) :
    ckQExp q t (ϱ + Δ) π n f =
      ckQExp q t ϱ π n (fun σ G U => ∑' G', poisPi (ckPl q t Δ σ) G' * f σ (G + G') U) := by
  unfold ckQExp
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun U _ => ?_
  congr 1
  rw [CKEdgeA_Pl_add]
  exact ck_poisPi_superpose (CKEdgeA_Pl_nonneg hp hϱ σ) (CKEdgeA_Pl_nonneg hp hΔ σ) hc
    (fun N => hf σ N U)

private lemma CKEdgeA_sum_post_mul {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (U : Finset (Fin n))
    (ς : Fin n → Fin q) (f : (Fin n → Fin q) → ℝ) :
    ∑ τ, ckPost q t ϱ G U ς τ * f τ =
      (∑ τ with ckAgree U ς τ, ckL q t ϱ G τ * f τ) / ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ := by
  unfold ckPost
  set Z := ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ with hZ
  rw [Finset.sum_div, Finset.sum_filter]
  refine Finset.sum_congr rfl fun τ _ => ?_
  split_ifs <;> ring

private lemma CKEdgeA_Z_pos {q n : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ : ℝ) (G : RSGraph n)
    (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    0 < ∑ τ with ckAgree U ς τ, ckL q t ϱ G τ :=
  Finset.sum_pos (fun τ _ => CKEdgeA_L_pos hp ϱ G τ)
    ⟨ς, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ => rfl⟩⟩

/-- Factorization `F̃_{ϱ+δ}(G+H) = F̃_ϱ(G) ⟨L_δ(H)⟩_post`. -/
private lemma CKEdgeA_Ft_add {q n : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ δ : ℝ) (G H : RSGraph n)
    (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    ckFt q t (ϱ + δ) (G + H) U ς =
      ckFt q t ϱ G U ς * ∑ τ, ckPost q t ϱ G U ς τ * ckL q t δ H τ := by
  rw [CKEdgeA_sum_post_mul]
  have hZ := (CKEdgeA_Z_pos hp ϱ G U ς).ne'
  unfold ckFt
  simp only [ck_L_add]
  field_simp

private lemma CKEdgeA_log_Ft_add {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ δ : ℝ} (hϱ : 0 ≤ ϱ)
    (hδ : 0 ≤ δ) (G H : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q) :
    Real.log (ckFt q t (ϱ + δ) (G + H) U ς) =
      Real.log (ckFt q t ϱ G U ς) +
        Real.log (∑ τ, ckPost q t ϱ G U ς τ * ckL q t δ H τ) := by
  rw [CKEdgeA_Ft_add hp, Real.log_mul (ck_Ft_pos hp hϱ G U ς).ne'
    (CKEdgeA_avgL_pos hp hδ (ck_post_isPMF hp hϱ G U ς) H).ne']

private lemma CKEdgeA_abs_log_avgL_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (H : RSGraph n) :
    |Real.log (∑ τ, μ τ * ckL q t δ H τ)| ≤ δ * (n : ℝ) ^ 2 + rsEdges H * ckEll q t := by
  have hm := CKEdgeA_avgL_mem hp hδ hμ H
  have hpos := CKEdgeA_avgL_pos hp hδ hμ H
  have hMm := CKEdgeA_Mm_pos hp
  have hMp : 0 < ckMp t := lt_of_lt_of_le one_pos (CKEdgeA_one_le_Mp hp)
  have hb := ck_const_bounds hp
  have hlo : Real.log (ckMm q t ^ rsEdges H) ≤ Real.log (∑ τ, μ τ * ckL q t δ H τ) :=
    Real.log_le_log (pow_pos hMm _) hm.1
  have hhi : Real.log (∑ τ, μ τ * ckL q t δ H τ) ≤
      Real.log (Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H) :=
    Real.log_le_log hpos hm.2
  rw [Real.log_pow] at hlo
  rw [Real.log_mul (Real.exp_pos _).ne' (pow_pos hMp _).ne', Real.log_exp, Real.log_pow] at hhi
  have hE : ckEll q t = -Real.log (ckMm q t) := rfl
  have hk : (0 : ℝ) ≤ rsEdges H := Nat.cast_nonneg _
  have hδn : 0 ≤ δ * (n : ℝ) ^ 2 := by positivity
  have h1 : (rsEdges H : ℝ) * Real.log (ckMp t) ≤ rsEdges H * ckEll q t :=
    mul_le_mul_of_nonneg_left hb.2.2.2.2.2.2.le hk
  rw [abs_le]
  constructor
  · rw [hE] at *
    nlinarith
  · linarith

private lemma CKEdgeA_agree_iff {n q : ℕ} {U : Finset (Fin n)} {ς ς' : Fin n → Fin q}
    (h : ckAgree U ς ς') (τ : Fin n → Fin q) : ckAgree U ς τ ↔ ckAgree U ς' τ := by
  unfold ckAgree at *
  constructor
  · intro hτ v hv
    rw [hτ v hv, h v hv]
  · intro hτ v hv
    rw [hτ v hv, h v hv]

private lemma CKEdgeA_post_congr {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) {U : Finset (Fin n)}
    {ς ς' : Fin n → Fin q} (h : ckAgree U ς ς') : ckPost q t ϱ G U ς = ckPost q t ϱ G U ς' := by
  funext τ
  unfold ckPost
  have hfilt : (Finset.univ.filter fun τ' => ckAgree U ς τ') =
      Finset.univ.filter fun τ' => ckAgree U ς' τ' :=
    Finset.filter_congr fun τ' _ => CKEdgeA_agree_iff h τ'
  rw [hfilt]
  by_cases hτ : ckAgree U ς τ
  · rw [if_pos hτ, if_pos ((CKEdgeA_agree_iff h τ).mp hτ)]
  · rw [if_neg hτ, if_neg (fun h' => hτ ((CKEdgeA_agree_iff h τ).mpr h'))]

private lemma CKEdgeA_abs_tsum_le {ι : Type*} {f g : ι → ℝ} (hg : Summable g)
    (h : ∀ i, |f i| ≤ g i) : |∑' i, f i| ≤ ∑' i, g i := by
  have := tsum_of_norm_bounded hg.hasSum (f := f) (fun i => by rw [Real.norm_eq_abs]; exact h i)
  rwa [Real.norm_eq_abs] at this

/-- `post^{ϱ+Δ}_{G+G'} ∝ post^ϱ_G · L_Δ(G', ·)`. -/
private lemma CKEdgeA_post_add {q n : ℕ} {t : ℝ} (hp : CKPar q t) (ϱ Δ : ℝ) (G G' : RSGraph n)
    (U : Finset (Fin n)) (ς τ : Fin n → Fin q) :
    ckPost q t (ϱ + Δ) (G + G') U ς τ =
      ckPost q t ϱ G U ς τ * ckL q t Δ G' τ /
        ∑ τ', ckPost q t ϱ G U ς τ' * ckL q t Δ G' τ' := by
  rw [CKEdgeA_sum_post_mul]
  have hZ := (CKEdgeA_Z_pos hp ϱ G U ς).ne'
  have hZ' := (CKEdgeA_Z_pos hp (ϱ + Δ) (G + G') U ς).ne'
  simp only [ck_L_add] at hZ'
  unfold ckPost
  simp only [ck_L_add]
  split_ifs with h
  · field_simp
  · simp

/-- Lemma 5.2(i): convexity of `Ξ_δ` under countable mixtures. -/
private lemma CKEdgeA_xi_mix {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {ι : Type*} {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hw1 : HasSum w 1)
    {ν : ι → (Fin n → Fin q) → ℝ} (hν : ∀ i, IsPMF (ν i))
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (hmix : ∀ τ, HasSum (fun i => w i * ν i τ) (μ τ)) :
    ckXi q t δ μ ≤ ∑' i, w i * ckXi q t δ (ν i) := by
  have hY : ∀ H : RSGraph n, HasSum (fun i => w i * ∑ τ, ν i τ * ckL q t δ H τ)
      (∑ τ, μ τ * ckL q t δ H τ) := by
    intro H
    have h := hasSum_sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
      (hmix τ).mul_right (ckL q t δ H τ)
    refine h.congr_fun fun i => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  have hJ : ∀ H : RSGraph n, ckLam (∑ τ, μ τ * ckL q t δ H τ) ≤
      ∑' i, w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ) := by
    intro H
    have h := ck_lam_tsum_le (w := w) (y := fun i => ∑ τ, ν i τ * ckL q t δ H τ)
      (pow_pos (CKEdgeA_Mm_pos hp) (rsEdges H)) hw0 hw1
      (fun i => CKEdgeA_avgL_mem hp hδ (hν i) H)
    rw [← (hY H).tsum_eq]
    exact h.2.2
  have hin : ∀ H : RSGraph n, |∑' i, w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ)| ≤
      CKEdgeA_g t δ H := by
    intro H
    have h := CKEdgeA_abs_tsum_le (hw1.summable.mul_right (CKEdgeA_g t δ H))
      (f := fun i => w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ)) (fun i => by
        rw [abs_mul, abs_of_nonneg (hw0 i)]
        exact mul_le_mul_of_nonneg_left (CKEdgeA_abs_lam_le_g hp hδ (hν i) H) (hw0 i))
    rwa [tsum_mul_right, hw1.tsum_eq, one_mul] at h
  have hsum2 : Summable fun H : RSGraph n =>
      poisPi (fun _ => δ) H * ∑' i, w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ) := by
    refine Summable.of_norm_bounded (CKEdgeA_g_summable hp hδ) fun H => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rs_poisPi_nonneg (fun _ => hδ) H)]
    exact mul_le_mul_of_nonneg_left (hin H) (rs_poisPi_nonneg (fun _ => hδ) H)
  have hdouble : Summable (Function.uncurry fun (H : RSGraph n) (i : ι) =>
      poisPi (fun _ => δ) H * (w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ))) := by
    have hprod := Summable.mul_of_nonneg (CKEdgeA_g_summable hp hδ (n := n)) hw1.summable
      (fun H => mul_nonneg (rs_poisPi_nonneg (fun _ => hδ) H) (CKEdgeA_g_nonneg t δ H)) hw0
    refine Summable.of_norm_bounded hprod fun z => ?_
    obtain ⟨H, i⟩ := z
    simp only [Function.uncurry_apply_pair, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (rs_poisPi_nonneg (fun _ => hδ) H),
      abs_of_nonneg (hw0 i)]
    have h := CKEdgeA_abs_lam_le_g hp hδ (hν i) H
    have hP := rs_poisPi_nonneg (fun _ : Fin n × Fin n => hδ) H
    calc poisPi (fun _ => δ) H * (w i * |ckLam (∑ τ, ν i τ * ckL q t δ H τ)|)
        ≤ poisPi (fun _ => δ) H * (w i * CKEdgeA_g t δ H) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (hw0 i)) hP
      _ = poisPi (fun _ => δ) H * CKEdgeA_g t δ H * w i := by ring
  calc ckXi q t δ μ ≤ ∑' H : RSGraph n,
        poisPi (fun _ => δ) H * ∑' i, w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ) := by
        unfold ckXi
        exact Summable.tsum_le_tsum
          (fun H => mul_le_mul_of_nonneg_left (hJ H) (rs_poisPi_nonneg (fun _ => hδ) H))
          (CKEdgeA_xi_summable hp hδ hμ) hsum2
    _ = ∑' H : RSGraph n, ∑' i,
        poisPi (fun _ => δ) H * (w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ)) := by
        refine tsum_congr fun H => ?_
        rw [tsum_mul_left]
    _ = ∑' i, ∑' H : RSGraph n,
        poisPi (fun _ => δ) H * (w i * ckLam (∑ τ, ν i τ * ckL q t δ H τ)) :=
        hdouble.tsum_comm.symm
    _ = ∑' i, w i * ckXi q t δ (ν i) := by
        refine tsum_congr fun i => ?_
        unfold ckXi
        rw [← tsum_mul_left]
        refine tsum_congr fun H => ?_
        ring

private lemma CKEdgeA_hasSum_omega {q n : ℕ} {t : ℝ} (hp : CKPar q t) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    HasSum (fun G' : RSGraph n => ∑ τ, μ τ * poisPi (ckPl q t Δ τ) G') 1 := by
  have h := hasSum_sum (s := Finset.univ) fun τ (_ : τ ∈ Finset.univ) =>
    (CKEdgeA_hasSum_Pl hp hΔ τ).mul_left (μ τ)
  simp only [mul_one, hμ.2] at h
  exact h

private lemma CKEdgeA_mix_term {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ Δ : ℝ} (hϱ : 0 ≤ ϱ)
    (hΔ : 0 ≤ Δ) (G G' : RSGraph n) (U : Finset (Fin n)) (σ τ : Fin n → Fin q) :
    (∑ τ', ckPost q t ϱ G U σ τ' * poisPi (ckPl q t Δ τ') G') *
        ckPost q t (ϱ + Δ) (G + G') U σ τ =
      ckPost q t ϱ G U σ τ * poisPi (ckPl q t Δ τ) G' := by
  have hY := (CKEdgeA_avgL_pos hp hΔ (ck_post_isPMF hp hϱ G U σ) G').ne'
  have hsum : ∑ τ', ckPost q t ϱ G U σ τ' * poisPi (ckPl q t Δ τ') G' =
      poisPi (fun _ => Δ) G' * ∑ τ', ckPost q t ϱ G U σ τ' * ckL q t Δ G' τ' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ' _ => by rw [ck_pl_eq]; ring
  rw [hsum, CKEdgeA_post_add hp, ck_pl_eq]
  field_simp

private lemma CKEdgeA_tsum_mix_mem {ι : Type*} {w x : ι → ℝ} {B : ℝ} (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : HasSum w 1) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ B) :
    0 ≤ ∑' i, w i * x i ∧ ∑' i, w i * x i ≤ B := by
  have hs : Summable fun i => w i * x i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (hx i).1)
      (fun i => mul_le_mul_of_nonneg_left (hx i).2 (hw0 i)) (hw1.summable.mul_right B)
  constructor
  · exact tsum_nonneg fun i => mul_nonneg (hw0 i) (hx i).1
  · calc ∑' i, w i * x i ≤ ∑' i, w i * B :=
          Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (hx i).2 (hw0 i)) hs
            (hw1.summable.mul_right B)
      _ = B := by rw [tsum_mul_right, hw1.tsum_eq, one_mul]

-- Lemma 5.1(a)
theorem ck_xi_bdd {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ B : ℝ, ∀ μ : (Fin n → Fin q) → ℝ, IsPMF μ → 0 ≤ ckXi q t δ μ ∧ ckXi q t δ μ ≤ B :=
  ⟨_, fun _ hμ => ⟨CKEdgeA_xi_nonneg hp hδ hμ, CKEdgeA_xi_le hp hδ hμ⟩⟩

-- Lemma 5.1(b)
theorem ck_superpose {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ δ π : ℝ} (hϱ : 0 ≤ ϱ) (hδ : 0 ≤ δ)
    (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    ckK q t (ϱ + δ) π n =
      ckK q t ϱ π n + ckQExp q t ϱ π n (fun σ G U => ckXi q t δ (ckPost q t ϱ G U σ)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (by norm_num) hp.two_le
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hℓ : 0 < ckEll q t := (ck_const_bounds hp).2.2.2.2.2.1
  have hϱδ : 0 ≤ ϱ + δ := by linarith
  -- superposition `𝖯^σ_{ϱ+δ} = 𝖯^σ_ϱ ⊛ 𝖯^σ_δ`
  have hbd1 : ∀ σ (G : RSGraph n) U, |Real.log (ckFt q t (ϱ + δ) G U σ)| ≤
      ((n : ℝ) * Real.log q + (ϱ + δ) * (n : ℝ) ^ 2 + ckEll q t) * 2 ^ rsEdges G := by
    intro σ G U
    have h := ck_abs_log_Ft_le hp hϱδ G U σ
    have h2 := CKEdgeA_lin_le_two_pow (a := (n : ℝ) * Real.log q + (ϱ + δ) * (n : ℝ) ^ 2)
      (b := ckEll q t) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogq)
        (mul_nonneg hϱδ (by positivity))) hℓ.le (rsEdges G)
    linarith
  have h1 : ckK q t (ϱ + δ) π n = ckQExp q t ϱ π n (fun σ G U =>
      ∑' H, poisPi (ckPl q t δ σ) H * Real.log (ckFt q t (ϱ + δ) (G + H) U σ)) :=
    CKEdgeA_QExp_superpose hp hϱ hδ π (fun σ G U => Real.log (ckFt q t (ϱ + δ) G U σ))
      (by norm_num : (0 : ℝ) ≤ 2) hbd1
  -- the domination `|log ⟨L_δ(H)⟩_post| ≤ δ n² + |H| ℓ₀`
  have hΦsum : ∀ τ : Fin n → Fin q, Summable fun H : RSGraph n =>
      poisPi (ckPl q t δ τ) H * (δ * (n : ℝ) ^ 2 + rsEdges H * ckEll q t) := by
    intro τ
    refine rs_summable_poisPi_of_abs_le (CKEdgeA_Pl_nonneg hp hδ τ)
      (A := δ * (n : ℝ) ^ 2 + ckEll q t) (c := 2) (by norm_num) fun H => ?_
    have h := CKEdgeA_lin_le_two_pow (a := δ * (n : ℝ) ^ 2) (b := ckEll q t) (by positivity)
      hℓ.le (rsEdges H)
    rw [abs_of_nonneg (by positivity)]
    exact h
  have hφb : ∀ (H G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q),
      |Real.log (∑ τ, ckPost q t ϱ G U ς τ * ckL q t δ H τ)| ≤
        δ * (n : ℝ) ^ 2 + rsEdges H * ckEll q t :=
    fun H G U ς => CKEdgeA_abs_log_avgL_le hp hδ (ck_post_isPMF hp hϱ G U ς) H
  have hsumφ : ∀ σ (G : RSGraph n) U, Summable fun H : RSGraph n =>
      poisPi (ckPl q t δ σ) H * Real.log (∑ τ, ckPost q t ϱ G U σ τ * ckL q t δ H τ) := by
    intro σ G U
    refine Summable.of_norm_bounded (hΦsum σ) fun H => ?_
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hδ σ) H)]
    exact mul_le_mul_of_nonneg_left (hφb H G U σ)
      (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hδ σ) H)
  -- factorization of `F̃`, pointwise in `(σ, G, U)`
  have hpt : ∀ σ (G : RSGraph n) U,
      ∑' H, poisPi (ckPl q t δ σ) H * Real.log (ckFt q t (ϱ + δ) (G + H) U σ) =
        Real.log (ckFt q t ϱ G U σ) + ∑' H, poisPi (ckPl q t δ σ) H *
          Real.log (∑ τ, ckPost q t ϱ G U σ τ * ckL q t δ H τ) := by
    intro σ G U
    simp only [CKEdgeA_log_Ft_add hp hϱ hδ, mul_add]
    rw [Summable.tsum_add ((CKEdgeA_hasSum_Pl hp hδ σ).summable.mul_right _) (hsumφ σ G U),
      tsum_mul_right, (CKEdgeA_hasSum_Pl hp hδ σ).tsum_eq, one_mul]
  have h2 : ckK q t (ϱ + δ) π n = ckQExp q t ϱ π n (fun σ G U =>
      Real.log (ckFt q t ϱ G U σ) + ∑' H, poisPi (ckPl q t δ σ) H *
        Real.log (∑ τ, ckPost q t ϱ G U σ τ * ckL q t δ H τ)) := by
    rw [h1]
    congr 1
    funext σ G U
    exact hpt σ G U
  have hdom1 : CKDom (fun σ (G : RSGraph n) (U : Finset (Fin n)) =>
      Real.log (ckFt q t ϱ G U σ)) := by
    refine ⟨(n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2 + ckEll q t, 2, by norm_num,
      fun σ G U => ?_⟩
    have h := ck_abs_log_Ft_le hp hϱ G U σ
    have h2 := CKEdgeA_lin_le_two_pow (a := (n : ℝ) * Real.log q + ϱ * (n : ℝ) ^ 2)
      (b := ckEll q t) (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogq)
        (mul_nonneg hϱ (by positivity))) hℓ.le (rsEdges G)
    linarith
  have hdom2 : CKDom (fun σ (G : RSGraph n) (U : Finset (Fin n)) =>
      ∑' H, poisPi (ckPl q t δ σ) H * Real.log (∑ τ, ckPost q t ϱ G U σ τ * ckL q t δ H τ)) := by
    refine ⟨∑ σ' : Fin n → Fin q, ∑' H : RSGraph n,
      poisPi (ckPl q t δ σ') H * (δ * (n : ℝ) ^ 2 + rsEdges H * ckEll q t), 1, zero_le_one,
      fun σ G U => ?_⟩
    rw [one_pow, mul_one]
    refine (CKEdgeA_abs_tsum_le (hΦsum σ) fun H => ?_).trans ?_
    · rw [abs_mul, abs_of_nonneg (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hδ σ) H)]
      exact mul_le_mul_of_nonneg_left (hφb H G U σ)
        (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hδ σ) H)
    · refine Finset.single_le_sum (f := fun σ' : Fin n → Fin q => ∑' H : RSGraph n,
        poisPi (ckPl q t δ σ') H * (δ * (n : ℝ) ^ 2 + rsEdges H * ckEll q t))
        (fun σ' _ => tsum_nonneg fun H => mul_nonneg
          (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hδ σ') H) (by positivity))
        (Finset.mem_univ σ)
  rw [h2, ck_QExp_add hp hϱ π hdom1 hdom2]
  congr 1
  rw [ck_predictive hp hϱ π (fun H τ => poisPi (ckPl q t δ τ) H)
    (fun H τ => rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hδ τ) H)
    (fun H G U ς => Real.log (∑ τ, ckPost q t ϱ G U ς τ * ckL q t δ H τ))
    (fun H G U ς ς' h => by simp only [CKEdgeA_post_congr t ϱ G h])
    (fun H => δ * (n : ℝ) ^ 2 + rsEdges H * ckEll q t) hφb hΦsum]
  congr 1
  funext σ G U
  unfold ckXi
  refine tsum_congr fun H => ?_
  have hR : ∑ τ, ckPost q t ϱ G U σ τ * poisPi (ckPl q t δ τ) H =
      poisPi (fun _ => δ) H * ∑ τ, ckPost q t ϱ G U σ τ * ckL q t δ H τ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by rw [ck_pl_eq]; ring
  rw [hR, ckLam]
  ring

-- Lemma 5.2
theorem ck_K_increment_mono {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ₀ ϱ₁ δ π : ℝ}
    (h0 : 0 ≤ ϱ₀) (h01 : ϱ₀ ≤ ϱ₁) (hδ : 0 ≤ δ) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    ckK q t (ϱ₀ + δ) π n - ckK q t ϱ₀ π n ≤ ckK q t (ϱ₁ + δ) π n - ckK q t ϱ₁ π n := by
  obtain ⟨Δ, hΔ, rfl⟩ : ∃ Δ, 0 ≤ Δ ∧ ϱ₁ = ϱ₀ + Δ := ⟨ϱ₁ - ϱ₀, by linarith, by ring⟩
  have hϱ₁ : 0 ≤ ϱ₀ + Δ := by linarith
  rw [ck_superpose hp h0 hδ hπ0 hπ1, ck_superpose hp hϱ₁ hδ hπ0 hπ1, add_sub_cancel_left,
    add_sub_cancel_left]
  obtain ⟨B, hB⟩ := ck_xi_bdd (n := n) hp hδ
  have hxi : ∀ ϱ : ℝ, 0 ≤ ϱ → ∀ (G : RSGraph n) (U : Finset (Fin n)) (ς : Fin n → Fin q),
      0 ≤ ckXi q t δ (ckPost q t ϱ G U ς) ∧ ckXi q t δ (ckPost q t ϱ G U ς) ≤ B :=
    fun ϱ hϱ G U ς => hB _ (ck_post_isPMF hp hϱ G U ς)
  -- (ii) realize `𝖰_{ϱ₁}` by superposition
  have h1 : ckQExp q t (ϱ₀ + Δ) π n (fun σ G U => ckXi q t δ (ckPost q t (ϱ₀ + Δ) G U σ)) =
      ckQExp q t ϱ₀ π n (fun σ G U => ∑' G', poisPi (ckPl q t Δ σ) G' *
        ckXi q t δ (ckPost q t (ϱ₀ + Δ) (G + G') U σ)) :=
    CKEdgeA_QExp_superpose hp h0 hΔ π (fun σ G U => ckXi q t δ (ckPost q t (ϱ₀ + Δ) G U σ))
      zero_le_one (fun σ G U => by
        rw [one_pow, mul_one, abs_of_nonneg (hxi _ hϱ₁ G U σ).1]
        exact (hxi _ hϱ₁ G U σ).2)
  -- (iii) predictive law of the extra graph `G'`
  have h2 := ck_predictive (n := n) hp h0 π (fun G' τ => poisPi (ckPl q t Δ τ) G')
    (fun G' τ => rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hΔ τ) G')
    (fun G' G U ς => ckXi q t δ (ckPost q t (ϱ₀ + Δ) (G + G') U ς))
    (fun G' G U ς ς' h => by simp only [CKEdgeA_post_congr t (ϱ₀ + Δ) (G + G') h])
    (fun _ => B)
    (fun G' G U ς => by
      rw [abs_of_nonneg (hxi _ hϱ₁ _ U ς).1]
      exact (hxi _ hϱ₁ _ U ς).2)
    (fun τ => (CKEdgeA_hasSum_Pl hp hΔ τ).summable.mul_right B)
  rw [h1, h2]
  -- (iv) Jensen
  have hdomA : CKDom (fun σ (G : RSGraph n) (U : Finset (Fin n)) =>
      ckXi q t δ (ckPost q t ϱ₀ G U σ)) :=
    ⟨B, 1, zero_le_one, fun σ G U => by
      rw [one_pow, mul_one, abs_of_nonneg (hxi _ h0 G U σ).1]
      exact (hxi _ h0 G U σ).2⟩
  have hmem : ∀ σ (G : RSGraph n) (U : Finset (Fin n)),
      0 ≤ ∑' G', (∑ τ, ckPost q t ϱ₀ G U σ τ * poisPi (ckPl q t Δ τ) G') *
          ckXi q t δ (ckPost q t (ϱ₀ + Δ) (G + G') U σ) ∧
        ∑' G', (∑ τ, ckPost q t ϱ₀ G U σ τ * poisPi (ckPl q t Δ τ) G') *
          ckXi q t δ (ckPost q t (ϱ₀ + Δ) (G + G') U σ) ≤ B :=
    fun σ G U => CKEdgeA_tsum_mix_mem
      (fun G' => Finset.sum_nonneg fun τ _ => mul_nonneg ((ck_post_isPMF hp h0 G U σ).1 τ)
        (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hΔ τ) G'))
      (CKEdgeA_hasSum_omega hp hΔ (ck_post_isPMF hp h0 G U σ))
      (fun G' => hxi _ hϱ₁ _ U σ)
  have hdomB : CKDom (fun σ (G : RSGraph n) (U : Finset (Fin n)) =>
      ∑' G', (∑ τ, ckPost q t ϱ₀ G U σ τ * poisPi (ckPl q t Δ τ) G') *
        ckXi q t δ (ckPost q t (ϱ₀ + Δ) (G + G') U σ)) :=
    ⟨B, 1, zero_le_one, fun σ G U => by
      rw [one_pow, mul_one, abs_of_nonneg (hmem σ G U).1]
      exact (hmem σ G U).2⟩
  refine ck_QExp_mono hp h0 hπ0 hπ1 hdomA hdomB fun σ G U => ?_
  exact CKEdgeA_xi_mix hp hδ
    (w := fun G' => ∑ τ, ckPost q t ϱ₀ G U σ τ * poisPi (ckPl q t Δ τ) G')
    (fun G' => Finset.sum_nonneg fun τ _ => mul_nonneg ((ck_post_isPMF hp h0 G U σ).1 τ)
      (rs_poisPi_nonneg (CKEdgeA_Pl_nonneg hp hΔ τ) G'))
    (CKEdgeA_hasSum_omega hp hΔ (ck_post_isPMF hp h0 G U σ))
    (fun G' => ck_post_isPMF hp hϱ₁ (G + G') U σ) (ck_post_isPMF hp h0 G U σ)
    (fun τ => by
      have h := (CKEdgeA_hasSum_Pl hp hΔ τ).mul_left (ckPost q t ϱ₀ G U σ τ)
      rw [mul_one] at h
      exact h.congr_fun fun G' => CKEdgeA_mix_term hp h0 hΔ G G' U σ τ)

/-! ### Part B helpers (Lemmas 5.3–5.4) -/

/-! ### Elementary helpers -/

/-- A `μ`-average of values in `[a, b]` lies in `[a, b]`. -/
private lemma CKEdgeB_avg_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    {f : (Fin n → Fin q) → ℝ} {a b : ℝ} (hf : ∀ τ, a ≤ f τ ∧ f τ ≤ b) :
    a ≤ ∑ τ, μ τ * f τ ∧ ∑ τ, μ τ * f τ ≤ b := by
  constructor
  · calc a = ∑ τ, μ τ * a := by rw [← Finset.sum_mul, hμ.2, one_mul]
      _ ≤ ∑ τ, μ τ * f τ :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hf τ).1 (hμ.1 τ)
  · calc ∑ τ, μ τ * f τ ≤ ∑ τ, μ τ * b :=
        Finset.sum_le_sum fun τ _ => mul_le_mul_of_nonneg_left (hf τ).2 (hμ.1 τ)
      _ = b := by rw [← Finset.sum_mul, hμ.2, one_mul]

/-- `kl(y) = Λ(y) + 1 - y`. -/
private lemma CKEdgeB_klFun_eq (y : ℝ) : InformationTheory.klFun y = ckLam y + 1 - y := by
  unfold InformationTheory.klFun ckLam; ring

/-- The number of ordered pairs is `n²`. -/
private lemma CKEdgeB_sum_const_pairs {n : ℕ} (c : ℝ) :
    ∑ _e : Fin n × Fin n, c = (n : ℝ) ^ 2 * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `|log m₋| = ℓ₀` (since `0 < m₋ < 1`). -/
private lemma CKEdgeB_abs_log_Mm {q : ℕ} {t : ℝ} (hp : CKPar q t) :
    |Real.log (ckMm q t)| = ckEll q t := by
  have hb := ck_const_bounds hp
  rw [abs_of_neg (Real.log_neg hb.1 hb.2.1)]
  rfl

/-- `|log m₊| ≤ ℓ₀` (since `1 < m₊` and `m₋ m₊ < 1`). -/
private lemma CKEdgeB_abs_log_Mp {q : ℕ} {t : ℝ} (hp : CKPar q t) :
    |Real.log (ckMp t)| ≤ ckEll q t := by
  have hb := ck_const_bounds hp
  rw [abs_of_pos (Real.log_pos hb.2.2.1)]
  exact hb.2.2.2.2.2.2.le

/-- `kl` is `ℓ₀`-Lipschitz on `[m₋, m₊]`. -/
private lemma CKEdgeB_kl_lip {q : ℕ} {t : ℝ} (hp : CKPar q t) {y y' : ℝ}
    (hy : ckMm q t ≤ y ∧ y ≤ ckMp t) (hy' : ckMm q t ≤ y' ∧ y' ≤ ckMp t) :
    |InformationTheory.klFun y - InformationTheory.klFun y'| ≤ ckEll q t * |y - y'| :=
  ck_klFun_lip (ck_const_bounds hp).1 (CKEdgeB_abs_log_Mm hp).le (CKEdgeB_abs_log_Mp hp) hy hy'

/-! ### Bilinearity of `betheE` -/

private lemma CKEdgeB_betheE_sum_left {q n : ℕ} (t : ℝ) (f : Fin n → Fin q → ℝ)
    (ν : Fin q → ℝ) :
    betheE q t (fun a => ∑ v, f v a) ν = ∑ v, betheE q t (f v) ν := by
  unfold betheE
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

private lemma CKEdgeB_betheMvec_sum {q n : ℕ} (t : ℝ) (g : Fin n → Fin q → ℝ) (a : Fin q) :
    betheMvec q t (fun b => ∑ w, g w b) a = ∑ w, betheMvec q t (g w) a := by
  unfold betheMvec
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

private lemma CKEdgeB_betheE_sum_right {q n : ℕ} (t : ℝ) (μ : Fin q → ℝ)
    (g : Fin n → Fin q → ℝ) :
    betheE q t μ (fun b => ∑ w, g w b) = ∑ w, betheE q t μ (g w) := by
  unfold betheE
  simp only [CKEdgeB_betheMvec_sum, Finset.mul_sum]
  exact Finset.sum_comm

private lemma CKEdgeB_betheE_smul {q : ℕ} (t c : ℝ) (μ ν : Fin q → ℝ) :
    betheE q t (fun a => c * μ a) (fun b => c * ν b) = c ^ 2 * betheE q t μ ν := by
  unfold betheE betheMvec
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- `∑_{v,w} E(μ_v, μ_w) = n² E(m̄, m̄) ≤ n²` (BAL). -/
private lemma CKEdgeB_sum_betheE_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    (m : Fin n → Fin q → ℝ) (hm : ∀ v, ∑ a, m v a = 1) :
    ∑ v, ∑ w, betheE q t (m v) (m w) ≤ (n : ℝ) ^ 2 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set mb : Fin q → ℝ := fun a => ∑ v, (n : ℝ)⁻¹ * m v a with hmb
  have hmb1 : ∑ a, mb a = 1 := by
    rw [hmb]
    simp only
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hm, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have h1 := ck_betheE_self_le_one hp hmb1
  have h2 : betheE q t mb mb = ((n : ℝ)⁻¹) ^ 2 * ∑ v, ∑ w, betheE q t (m v) (m w) := by
    rw [hmb, CKEdgeB_betheE_sum_left]
    simp only [CKEdgeB_betheE_sum_right, CKEdgeB_betheE_smul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
  rw [h2] at h1
  have h3 : (0 : ℝ) < ((n : ℝ)⁻¹) ^ 2 := by positivity
  have h4 : ((n : ℝ)⁻¹) ^ 2 * (n : ℝ) ^ 2 = 1 := by field_simp
  nlinarith

/-! ### Cauchy–Schwarz for the off-diagonal pairs -/

private lemma CKEdgeB_cs {n : ℕ} (I : Fin n → Fin n → ℝ) (hI : ∀ v w, 0 ≤ I v w) :
    ∑ v, ∑ w ∈ Finset.univ.erase v, Real.sqrt (I v w) ≤
      (n : ℝ) ^ 2 * Real.sqrt (((n : ℝ) ^ 2)⁻¹ * ∑ v, ∑ w ∈ Finset.univ.erase v, I v w) := by
  set X := ∑ v, ∑ w ∈ Finset.univ.erase v, Real.sqrt (I v w) with hXdef
  set S := ∑ v, ∑ w ∈ Finset.univ.erase v, I v w with hSdef
  have hX0 : 0 ≤ X :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hI _ _
  have hX2 : X ^ 2 ≤ (n : ℝ) ^ 2 * S := by
    have h1 : X = ∑ x ∈ Finset.univ.sigma (fun v : Fin n => Finset.univ.erase v),
        Real.sqrt (I x.1 x.2) := Finset.sum_sigma' _ _ _
    have h2 : S = ∑ x ∈ Finset.univ.sigma (fun v : Fin n => Finset.univ.erase v),
        Real.sqrt (I x.1 x.2) ^ 2 := by
      rw [hSdef, Finset.sum_sigma']
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Real.sq_sqrt (hI _ _)]
    have hcs := sq_sum_le_card_mul_sum_sq
      (s := Finset.univ.sigma (fun v : Fin n => Finset.univ.erase v))
      (f := fun x => Real.sqrt (I x.1 x.2))
    have hcard : ((Finset.univ.sigma (fun v : Fin n => Finset.univ.erase v)).card : ℝ) ≤
        (n : ℝ) ^ 2 := by
      rw [Finset.card_sigma]
      have : ∑ v : Fin n, (Finset.univ.erase v).card ≤ n * n := by
        calc ∑ v : Fin n, (Finset.univ.erase v).card ≤ ∑ _v : Fin n, n :=
              Finset.sum_le_sum fun v _ => by
                rw [Finset.card_erase_of_mem (Finset.mem_univ v)]
                simp
          _ = n * n := by simp
      calc ((∑ v : Fin n, (Finset.univ.erase v).card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = (n : ℝ) ^ 2 := by push_cast; ring
    rw [h1, h2]
    have hsum0 : 0 ≤ ∑ x ∈ Finset.univ.sigma (fun v : Fin n => Finset.univ.erase v),
        Real.sqrt (I x.1 x.2) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hsum0
  have hrhs : (n : ℝ) ^ 2 * Real.sqrt (((n : ℝ) ^ 2)⁻¹ * S) = Real.sqrt ((n : ℝ) ^ 2 * S) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_inv,
        Real.sqrt_sq hn'.le]
      field_simp
  rw [hrhs]
  calc X = Real.sqrt (X ^ 2) := (Real.sqrt_sq hX0).symm
    _ ≤ Real.sqrt ((n : ℝ) ^ 2 * S) := Real.sqrt_le_sqrt hX2

/-- `0 ≤ ∑_e kl(⟨M_e⟩_μ) ≤ n² (1 + ℓ₀ m₊)` (proof of `ck_edgeKL_mem`, needed earlier). -/
private lemma CKEdgeB_edgeKL_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    0 ≤ ckEdgeKL q t μ ∧ ckEdgeKL q t μ ≤ (n : ℝ) ^ 2 * (1 + ckEll q t * ckMp t) := by
  have hterm : ∀ e : Fin n × Fin n,
      0 ≤ InformationTheory.klFun (∑ τ, μ τ * rsM q t (τ e.1) (τ e.2)) ∧
        InformationTheory.klFun (∑ τ, μ τ * rsM q t (τ e.1) (τ e.2)) ≤
          1 + ckEll q t * ckMp t :=
    fun e => ck_klFun_mem hp (CKEdgeB_avg_mem hμ fun τ => ck_rsM_mem hp _ _)
  unfold ckEdgeKL
  refine ⟨Finset.sum_nonneg fun e _ => (hterm e).1, ?_⟩
  calc _ ≤ ∑ _e : Fin n × Fin n, (1 + ckEll q t * ckMp t) :=
        Finset.sum_le_sum fun e _ => (hterm e).2
    _ = _ := CKEdgeB_sum_const_pairs _

/-! ### Lemma 5.3: single-edge configurations -/

/-- The multigraph with one edge on the ordered pair `e`. -/
private def CKEdgeB_one {n : ℕ} (e : Fin n × Fin n) : RSGraph n :=
  fun e' => if e' = e then 1 else 0

private lemma CKEdgeB_one_injective {n : ℕ} : Function.Injective (CKEdgeB_one (n := n)) := by
  intro e e' h
  by_contra hne
  have := congrFun h e
  simp [CKEdgeB_one, hne] at this

/-- `𝖯_δ(𝟏_e) = δ e^{-δ n²}`. -/
private lemma CKEdgeB_poisPi_one {n : ℕ} (δ : ℝ) (e : Fin n × Fin n) :
    poisPi (fun _ => δ) (CKEdgeB_one e) = δ * Real.exp (-(δ * (n : ℝ) ^ 2)) := by
  have h : ∀ e' : Fin n × Fin n,
      poisPMF δ (CKEdgeB_one e e') = Real.exp (-δ) * δ ^ (CKEdgeB_one e e') := by
    intro e'
    unfold CKEdgeB_one poisPMF
    split_ifs <;> simp
  unfold poisPi
  rw [Finset.prod_congr rfl (fun e' _ => h e'), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum]
  have hs : ∑ e', CKEdgeB_one e e' = 1 := by simp [CKEdgeB_one]
  rw [hs, pow_one, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← Real.exp_nat_mul,
    mul_comm]
  congr 2
  push_cast
  ring

/-- `L_δ(𝟏_e, τ) = e^{-δ S(τ)} M_e(τ)`. -/
private lemma CKEdgeB_L_one {q n : ℕ} (t δ : ℝ) (e : Fin n × Fin n) (τ : Fin n → Fin q) :
    ckL q t δ (CKEdgeB_one e) τ = Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2) := by
  unfold ckL rsW
  congr 1
  rw [Finset.prod_eq_single e]
  · simp [CKEdgeB_one]
  · intro b _ hb
    simp [CKEdgeB_one, hb]
  · intro h
    exact absurd (Finset.mem_univ e) h

/-- `|Λ(y)| ≤ 1 + y²` for `y ≥ 0`. -/
private lemma CKEdgeB_lam_abs_le {y : ℝ} (hy : 0 ≤ y) : |ckLam y| ≤ 1 + y ^ 2 := by
  unfold ckLam
  rcases hy.eq_or_lt with h | h
  · subst h; simp
  · rcases le_or_gt y 1 with h1 | h1
    · have := Real.abs_log_mul_self_lt y h h1
      rw [mul_comm] at this
      nlinarith [sq_nonneg y]
    · have hl0 : 0 ≤ Real.log y := Real.log_nonneg h1.le
      have hl1 : Real.log y ≤ y - 1 := Real.log_le_sub_one_of_pos h
      rw [abs_of_nonneg (mul_nonneg h.le hl0)]
      nlinarith

/-- The `kl` form of `Ξ_δ` (Lemma 5.1(a)), as a `HasSum`. -/
private lemma CKEdgeB_xi_hasSum {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    HasSum (fun H : RSGraph n => poisPi (fun _ => δ) H *
      InformationTheory.klFun (∑ τ, μ τ * ckL q t δ H τ)) (ckXi q t δ μ) := by
  have hb := ck_const_bounds hp
  have hYb : ∀ H : RSGraph n, 0 ≤ ∑ τ, μ τ * ckL q t δ H τ ∧
      ∑ τ, μ τ * ckL q t δ H τ ≤ Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H := by
    intro H
    have := CKEdgeB_avg_mem hμ (f := fun τ => ckL q t δ H τ) (a := ckMm q t ^ rsEdges H)
      (b := Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H)
      (fun τ => ⟨(ck_L_mem hp hδ H τ).1, (ck_L_mem hp hδ H τ).2.1⟩)
    exact ⟨le_trans (pow_nonneg hb.1.le _) this.1, this.2⟩
  have hΛ : ∀ H : RSGraph n, |ckLam (∑ τ, μ τ * ckL q t δ H τ)| ≤
      (1 + Real.exp (δ * (n : ℝ) ^ 2) ^ 2) * (ckMp t ^ 2) ^ (∑ i, H i) := by
    intro H
    have h1 := CKEdgeB_lam_abs_le (hYb H).1
    have h2 : (∑ τ, μ τ * ckL q t δ H τ) ^ 2 ≤
        (Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H) ^ 2 :=
      pow_le_pow_left₀ (hYb H).1 (hYb H).2 2
    have h3 : (1 : ℝ) ≤ (ckMp t ^ 2) ^ (∑ i, H i) :=
      one_le_pow₀ (by nlinarith [hb.2.2.1])
    have h4 : (Real.exp (δ * (n : ℝ) ^ 2) * ckMp t ^ rsEdges H) ^ 2 =
        Real.exp (δ * (n : ℝ) ^ 2) ^ 2 * (ckMp t ^ 2) ^ (∑ i, H i) := by
      unfold rsEdges
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (∑ i, H i) 2]
    nlinarith [h1, h2, h3, h4, sq_nonneg (Real.exp (δ * (n : ℝ) ^ 2))]
  have hs1 : Summable (fun H : RSGraph n =>
      poisPi (fun _ => δ) H * ckLam (∑ τ, μ τ * ckL q t δ H τ)) :=
    rs_summable_poisPi_of_abs_le (fun _ => hδ) (sq_nonneg _) hΛ
  have h1 : HasSum (fun H : RSGraph n =>
      poisPi (fun _ => δ) H * ckLam (∑ τ, μ τ * ckL q t δ H τ)) (ckXi q t δ μ) :=
    hs1.hasSum
  have h2 : HasSum (fun H : RSGraph n => poisPi (fun _ => δ) H) 1 :=
    rs_hasSum_poisPi (fun _ => hδ)
  have h3 : HasSum (fun H : RSGraph n =>
      poisPi (fun _ => δ) H * ∑ τ, μ τ * ckL q t δ H τ) 1 := by
    have hpl : ∀ τ : Fin n → Fin q, ∀ e, 0 ≤ ckPl q t δ τ e := fun τ e =>
      mul_nonneg hδ (le_trans hb.1.le (ck_rsM_mem hp _ _).1)
    have H := hasSum_sum (s := Finset.univ)
      (fun τ _ => (rs_hasSum_poisPi (hpl τ)).mul_left (μ τ))
    simp only [mul_one, hμ.2] at H
    refine H.congr_fun fun G => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [ck_pl_eq]
    ring
  have := (h1.add h2).sub h3
  rw [add_sub_cancel_right] at this
  refine this.congr_fun fun H => ?_
  simp only [CKEdgeB_klFun_eq]
  ring

/-- Keep only the single-edge configurations: `δ e^{-δn²} ∑_e kl(⟨e^{-δS} M_e⟩_μ) ≤ Ξ_δ(μ)`. -/
private lemma CKEdgeB_xi_ge {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    δ * Real.exp (-(δ * (n : ℝ) ^ 2)) * ∑ e : Fin n × Fin n, InformationTheory.klFun
      (∑ τ, μ τ * (Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2))) ≤
      ckXi q t δ μ := by
  have hb := ck_const_bounds hp
  have hg := CKEdgeB_xi_hasSum hp hδ hμ
  rw [Finset.mul_sum]
  refine hasSum_le_inj (CKEdgeB_one (n := n)) CKEdgeB_one_injective ?_ ?_ (hasSum_fintype _) hg
  · intro H _
    refine mul_nonneg (rs_poisPi_nonneg (fun _ => hδ) H) (InformationTheory.klFun_nonneg ?_)
    exact Finset.sum_nonneg fun τ _ =>
      mul_nonneg (hμ.1 τ) (le_trans (pow_nonneg hb.1.le _) (ck_L_mem hp hδ H τ).1)
  · intro e
    rw [CKEdgeB_poisPi_one]
    simp only [CKEdgeB_L_one]
    exact le_rfl

/-- Removing the tilt `e^{-δS}` on one edge, with the explicit error (`c = δ n²`,
`κ₀ = 1 + ℓ₀ m₊`). -/
private lemma CKEdgeB_kl_tilt {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) (e : Fin n × Fin n) :
    InformationTheory.klFun (∑ τ, μ τ * rsM q t (τ e.1) (τ e.2)) -
      δ * (n : ℝ) ^ 2 * ((ckEll q t + δ * (n : ℝ) ^ 2) * ckMp t + (1 + ckEll q t * ckMp t)) ≤
    Real.exp (-(δ * (n : ℝ) ^ 2)) * InformationTheory.klFun
      (∑ τ, μ τ * (Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2))) := by
  have hb := ck_const_bounds hp
  have hmp0 : 0 < ckMp t := by linarith [hb.2.2.1]
  have hl0 : 0 < ckEll q t := hb.2.2.2.2.2.1
  have hc0 : 0 ≤ δ * (n : ℝ) ^ 2 := by positivity
  have hX : ∀ τ : Fin n → Fin q, 1 ≤ Real.exp (-(δ * ckS q t τ)) ∧
      Real.exp (-(δ * ckS q t τ)) ≤ Real.exp (δ * (n : ℝ) ^ 2) := by
    intro τ
    have hS := ck_S_mem hp τ
    constructor
    · exact Real.one_le_exp (by nlinarith [hS.2])
    · exact Real.exp_le_exp.mpr (by nlinarith [hS.1])
  have hM := fun τ : Fin n → Fin q => ck_rsM_mem hp (τ e.1) (τ e.2)
  have hy0m : ckMm q t ≤ ∑ τ, μ τ * rsM q t (τ e.1) (τ e.2) ∧
      ∑ τ, μ τ * rsM q t (τ e.1) (τ e.2) ≤ ckMp t := CKEdgeB_avg_mem hμ hM
  have hym : ckMm q t ≤ ∑ τ, μ τ * (Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2)) ∧
      ∑ τ, μ τ * (Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2)) ≤
        Real.exp (δ * (n : ℝ) ^ 2) * ckMp t := by
    refine CKEdgeB_avg_mem hμ fun τ => ⟨?_, ?_⟩
    · nlinarith [(hX τ).1, (hM τ).1, hb.1]
    · exact mul_le_mul (hX τ).2 (hM τ).2 (by linarith [(hM τ).1, hb.1]) (Real.exp_pos _).le
  set y0 := ∑ τ, μ τ * rsM q t (τ e.1) (τ e.2) with hy0
  set y := ∑ τ, μ τ * (Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2)) with hy
  set c := δ * (n : ℝ) ^ 2 with hc
  have hdiff : 0 ≤ y - y0 ∧ y - y0 ≤ (Real.exp c - 1) * ckMp t := by
    have hyy : y - y0 = ∑ τ, μ τ *
        ((Real.exp (-(δ * ckS q t τ)) - 1) * rsM q t (τ e.1) (τ e.2)) := by
      rw [hy, hy0, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      ring
    rw [hyy]
    refine CKEdgeB_avg_mem hμ fun τ => ⟨?_, ?_⟩
    · exact mul_nonneg (by linarith [(hX τ).1]) (by linarith [(hM τ).1, hb.1])
    · exact mul_le_mul (by linarith [(hX τ).2]) (hM τ).2 (by linarith [(hM τ).1, hb.1])
        (by linarith [Real.add_one_le_exp c])
  -- `kl` is `(ℓ₀ + c)`-Lipschitz on `[m₋, e^c m₊]`
  have hlip : |InformationTheory.klFun y - InformationTheory.klFun y0| ≤
      (ckEll q t + c) * |y - y0| := by
    have h1 : |Real.log (ckMm q t)| ≤ ckEll q t + c := by
      rw [CKEdgeB_abs_log_Mm hp]; linarith
    have h2 : |Real.log (Real.exp c * ckMp t)| ≤ ckEll q t + c := by
      rw [Real.log_mul (Real.exp_pos c).ne' hmp0.ne', Real.log_exp]
      have := Real.log_pos hb.2.2.1
      rw [abs_of_nonneg (by linarith)]
      linarith [hb.2.2.2.2.2.2]
    exact ck_klFun_lip hb.1 h1 h2 hym
      ⟨hy0m.1, le_trans hy0m.2 (le_mul_of_one_le_left hmp0.le (Real.one_le_exp hc0))⟩
  have hk0 := ck_klFun_mem hp hy0m
  have A1 : InformationTheory.klFun y0 - (ckEll q t + c) * ((Real.exp c - 1) * ckMp t) ≤
      InformationTheory.klFun y := by
    have h1 : InformationTheory.klFun y0 - InformationTheory.klFun y ≤
        |InformationTheory.klFun y - InformationTheory.klFun y0| := by
      rw [abs_sub_comm]; exact le_abs_self _
    have h2 : (ckEll q t + c) * |y - y0| ≤ (ckEll q t + c) * ((Real.exp c - 1) * ckMp t) :=
      mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hdiff.1]; exact hdiff.2) (by linarith)
    linarith
  have hu0 : 0 < Real.exp (-c) := Real.exp_pos _
  have hu1 : Real.exp (-c) * Real.exp c = 1 := by rw [← Real.exp_add]; simp
  have hu2 : 1 - Real.exp (-c) ≤ c := by linarith [Real.add_one_le_exp (-c)]
  have hu3 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have A2 := mul_le_mul_of_nonneg_left A1 hu0.le
  have A3 : Real.exp (-c) * (InformationTheory.klFun y0 -
      (ckEll q t + c) * ((Real.exp c - 1) * ckMp t)) =
      Real.exp (-c) * InformationTheory.klFun y0 -
        (ckEll q t + c) * (1 - Real.exp (-c)) * ckMp t := by
    linear_combination (-(ckEll q t + c) * ckMp t) * hu1
  have A4 : (1 - Real.exp (-c)) * InformationTheory.klFun y0 ≤
      (1 - Real.exp (-c)) * (1 + ckEll q t * ckMp t) :=
    mul_le_mul_of_nonneg_left hk0.2 (by linarith)
  have hB0 : 0 ≤ (ckEll q t + c) * ckMp t + (1 + ckEll q t * ckMp t) := by positivity
  have A5 : (1 - Real.exp (-c)) * ((ckEll q t + c) * ckMp t + (1 + ckEll q t * ckMp t)) ≤
      c * ((ckEll q t + c) * ckMp t + (1 + ckEll q t * ckMp t)) :=
    mul_le_mul_of_nonneg_right hu2 hB0
  nlinarith [A2, A3, A4, A5]

/-- The explicit error term `n² c [(ℓ₀ + c) m₊ + κ₀]` of Lemma 5.3. -/
private def CKEdgeB_err (q : ℕ) (t : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * (c * ((ckEll q t + c) * ckMp t + (1 + ckEll q t * ckMp t)))

/-- Per posterior: `δ ∑_e kl(⟨M_e⟩_μ) - δ·err(δ n²) ≤ Ξ_δ(μ)`. -/
private lemma CKEdgeB_xi_lower {q n : ℕ} {t : ℝ} (hp : CKPar q t) {δ : ℝ} (hδ : 0 ≤ δ)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    δ * ckEdgeKL q t μ - δ * CKEdgeB_err q t n (δ * (n : ℝ) ^ 2) ≤ ckXi q t δ μ := by
  have h1 := CKEdgeB_xi_ge hp hδ hμ
  have h2 : ∑ e : Fin n × Fin n, (InformationTheory.klFun (∑ τ, μ τ * rsM q t (τ e.1) (τ e.2)) -
      δ * (n : ℝ) ^ 2 * ((ckEll q t + δ * (n : ℝ) ^ 2) * ckMp t + (1 + ckEll q t * ckMp t))) ≤
      ∑ e : Fin n × Fin n, Real.exp (-(δ * (n : ℝ) ^ 2)) * InformationTheory.klFun
        (∑ τ, μ τ * (Real.exp (-(δ * ckS q t τ)) * rsM q t (τ e.1) (τ e.2))) :=
    Finset.sum_le_sum fun e _ => CKEdgeB_kl_tilt hp hδ hμ e
  rw [Finset.sum_sub_distrib, CKEdgeB_sum_const_pairs, ← Finset.mul_sum] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hδ
  unfold ckEdgeKL CKEdgeB_err
  nlinarith [h1, h3]

/-- Chunking (Lemma 5.2 telescoped): `J (𝒦(ϱ + β/J) - 𝒦(ϱ)) ≤ 𝒦(ϱ + β) - 𝒦(ϱ)`. -/
private lemma CKEdgeB_chunk {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ β π : ℝ} (hϱ : 0 ≤ ϱ)
    (hβ : 0 ≤ β) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {J : ℕ} (hJ : 0 < J) :
    (J : ℝ) * (ckK q t (ϱ + β / J) π n - ckK q t ϱ π n) ≤
      ckK q t (ϱ + β) π n - ckK q t ϱ π n := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hδ : 0 ≤ β / J := div_nonneg hβ hJ'.le
  have htel := Finset.sum_range_sub (fun j : ℕ => ckK q t (ϱ + j * (β / J)) π n) J
  have hJδ : ϱ + (J : ℝ) * (β / J) = ϱ + β := by field_simp
  simp only [Nat.cast_zero, zero_mul, add_zero, hJδ] at htel
  rw [← htel]
  calc (J : ℝ) * (ckK q t (ϱ + β / J) π n - ckK q t ϱ π n) =
        ∑ _j ∈ Finset.range J, (ckK q t (ϱ + β / J) π n - ckK q t ϱ π n) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
        have := ck_K_increment_mono hp hϱ
          (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hδ)) hδ hπ0 hπ1 (n := n)
        have e1 : ϱ + ((j + 1 : ℕ) : ℝ) * (β / J) = ϱ + (j : ℝ) * (β / J) + β / J := by
          push_cast; ring
        rw [e1]
        exact this

private lemma CKEdgeB_dom {q n : ℕ} {f : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ}
    {A : ℝ} (h : ∀ σ G U, |f σ G U| ≤ A) : CKDom f :=
  ⟨A, 1, zero_le_one, fun σ G U => by rw [one_pow, mul_one]; exact h σ G U⟩

/-- Lemma 5.3, explicit-`J` form. -/
private lemma CKEdgeB_explicit {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ β π : ℝ} (hϱ : 0 ≤ ϱ)
    (hβ : 0 ≤ β) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) {J : ℕ} (hJ : 0 < J) :
    β * ckQExp q t ϱ π n (fun σ G U => ckEdgeKL q t (ckPost q t ϱ G U σ)) -
      β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2) ≤
      ckK q t (ϱ + β) π n - ckK q t ϱ π n := by
  have hJ' : (0 : ℝ) < J := Nat.cast_pos.mpr hJ
  have hδ : 0 ≤ β / J := div_nonneg hβ hJ'.le
  have hJδ : (J : ℝ) * (β / J) = β := by field_simp
  have hchunk := CKEdgeB_chunk hp hϱ hβ hπ0 hπ1 hJ (n := n)
  have hsup := ck_superpose hp hϱ hδ hπ0 hπ1 (n := n)
  have hpost : ∀ σ (G : RSGraph n) (U : Finset (Fin n)), IsPMF (ckPost q t ϱ G U σ) :=
    fun σ G U => ck_post_isPMF hp hϱ G U σ
  obtain ⟨B, hB⟩ := ck_xi_bdd hp hδ (n := n)
  have hdomF : CKDom (fun σ G U => β * ckEdgeKL q t (ckPost q t ϱ G U σ)) :=
    CKEdgeB_dom (A := β * ((n : ℝ) ^ 2 * (1 + ckEll q t * ckMp t))) fun σ G U => by
      have := CKEdgeB_edgeKL_mem hp (hpost σ G U)
      rw [abs_of_nonneg (mul_nonneg hβ this.1)]
      exact mul_le_mul_of_nonneg_left this.2 hβ
  have hdomC : CKDom (fun (_ : Fin n → Fin q) (_ : RSGraph n) (_ : Finset (Fin n)) =>
      -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2))) :=
    CKEdgeB_dom (A := |β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2)|) fun _ _ _ => by
      rw [abs_neg]
  have hdomFC : CKDom (fun σ G U => β * ckEdgeKL q t (ckPost q t ϱ G U σ) +
      -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2))) :=
    CKEdgeB_dom (A := β * ((n : ℝ) ^ 2 * (1 + ckEll q t * ckMp t)) +
        |β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2)|) fun σ G U => by
      have := CKEdgeB_edgeKL_mem hp (hpost σ G U)
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_neg, abs_of_nonneg (mul_nonneg hβ this.1)]
      have := mul_le_mul_of_nonneg_left this.2 hβ
      linarith
  have hdomX : CKDom (fun σ G U => (J : ℝ) * ckXi q t (β / J) (ckPost q t ϱ G U σ)) :=
    CKEdgeB_dom (A := J * B) fun σ G U => by
      have := hB _ (hpost σ G U)
      rw [abs_of_nonneg (mul_nonneg hJ'.le this.1)]
      exact mul_le_mul_of_nonneg_left this.2 hJ'.le
  have hmono := ck_QExp_mono hp hϱ hπ0 hπ1 hdomFC hdomX (fun σ G U => by
    have h1 := CKEdgeB_xi_lower hp hδ (hpost σ G U)
    have h2 := mul_le_mul_of_nonneg_left h1 hJ'.le
    have h3 : (J : ℝ) * (β / J * ckEdgeKL q t (ckPost q t ϱ G U σ) -
        β / J * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2)) =
        β * ckEdgeKL q t (ckPost q t ϱ G U σ) +
          -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2)) := by
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hJδ]; ring
    rw [h3] at h2
    exact h2)
  have e1 : ckQExp q t ϱ π n (fun σ G U => β * ckEdgeKL q t (ckPost q t ϱ G U σ) +
      -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2))) =
      ckQExp q t ϱ π n (fun σ G U => β * ckEdgeKL q t (ckPost q t ϱ G U σ)) +
        ckQExp q t ϱ π n (fun _ _ _ => -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2))) :=
    ck_QExp_add hp hϱ π hdomF hdomC
  have e2 : ckQExp q t ϱ π n (fun σ G U => β * ckEdgeKL q t (ckPost q t ϱ G U σ)) =
      β * ckQExp q t ϱ π n (fun σ G U => ckEdgeKL q t (ckPost q t ϱ G U σ)) :=
    ck_QExp_smul t ϱ π β _
  have e3 : ckQExp q t ϱ π n
      (fun (_ : Fin n → Fin q) (_ : RSGraph n) (_ : Finset (Fin n)) =>
        -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2))) =
      -(β * CKEdgeB_err q t n (β / J * (n : ℝ) ^ 2)) :=
    ck_QExp_const hp hϱ π _
  have e4 : ckQExp q t ϱ π n (fun σ G U => (J : ℝ) * ckXi q t (β / J) (ckPost q t ϱ G U σ)) =
      (J : ℝ) * ckQExp q t ϱ π n (fun σ G U => ckXi q t (β / J) (ckPost q t ϱ G U σ)) :=
    ck_QExp_smul t ϱ π (J : ℝ) _
  have e5 : ckK q t (ϱ + β / J) π n - ckK q t ϱ π n =
      ckQExp q t ϱ π n (fun σ G U => ckXi q t (β / J) (ckPost q t ϱ G U σ)) := by
    rw [hsup]; ring
  rw [e5] at hchunk
  linarith [hmono, hchunk, e1, e2, e3, e4]

-- Lemma 5.3 (prove the explicit-J form first, then J → ∞ in ℝ)
theorem ck_edge_lower {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ β π : ℝ} (hϱ : 0 ≤ ϱ)
    (hβ : 0 ≤ β) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1) :
    β * ckQExp q t ϱ π n (fun σ G U => ckEdgeKL q t (ckPost q t ϱ G U σ)) ≤
      ckK q t (ϱ + β) π n - ckK q t ϱ π n := by
  set E := ckQExp q t ϱ π n (fun σ G U => ckEdgeKL q t (ckPost q t ϱ G U σ)) with hE
  -- the explicit error tends to `0` as `J → ∞`
  have hg : Continuous (fun c : ℝ => β * E - β * CKEdgeB_err q t n c) := by
    unfold CKEdgeB_err
    fun_prop
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun k : ℕ => β * (n : ℝ) ^ 2 * (1 / ((k : ℝ) + 1))) atTop
      (𝓝 (β * (n : ℝ) ^ 2 * 0)) := h0.const_mul _
  rw [mul_zero] at h1
  have h2 : Tendsto (fun k : ℕ => β / (((k + 1 : ℕ) : ℝ)) * (n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine h1.congr fun k => ?_
    push_cast
    ring
  have h3 := (hg.tendsto 0).comp h2
  have h4 : β * E - β * CKEdgeB_err q t n 0 = β * E := by
    unfold CKEdgeB_err; ring
  rw [h4] at h3
  exact le_of_tendsto' h3 fun k => CKEdgeB_explicit hp hϱ hβ hπ0 hπ1 (Nat.succ_pos k)

-- 0 ≤ kl ≤ 1 + ℓ₀ m₊ on [m₋, m₊]
theorem ck_edgeKL_mem {q n : ℕ} {t : ℝ} (hp : CKPar q t) {μ : (Fin n → Fin q) → ℝ}
    (hμ : IsPMF μ) :
    0 ≤ ckEdgeKL q t μ ∧ ckEdgeKL q t μ ≤ (n : ℝ) ^ 2 * (1 + ckEll q t * ckMp t) :=
  CKEdgeB_edgeKL_mem hp hμ

-- Lemma 5.4
theorem ck_edge_pairwise {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 0 < n)
    {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    (n : ℝ) ^ 2 * (ckBE q t (fun _ => (n : ℝ)⁻¹) (ckMarg μ) -
        2 * ckEll q t * ckMp t * ckIota2 μ - ckEll q t * (ckMp t - ckMm q t) / n) ≤
      ckEdgeKL q t μ := by
  have hb := ck_const_bounds hp
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  set m := ckMarg μ with hm
  have hmS : ∀ v, m v ∈ stdSimplex ℝ (Fin q) := fun v => ck_marg_mem hμ v
  have hm1 : ∀ v, ∑ a, m v a = 1 := fun v => (hmS v).2
  set A : Fin n × Fin n → ℝ := fun e => ∑ τ, μ τ * rsM q t (τ e.1) (τ e.2) with hA
  set E : Fin n × Fin n → ℝ := fun e => betheE q t (m e.1) (m e.2) with hE
  have hAmem : ∀ e, ckMm q t ≤ A e ∧ A e ≤ ckMp t :=
    fun e => CKEdgeB_avg_mem hμ fun τ => ck_rsM_mem hp _ _
  have hEmem : ∀ e, ckMm q t ≤ E e ∧ E e ≤ ckMp t :=
    fun e => ck_betheE_mem hp (hmS _) (hmS _)
  -- main term: `∑ kl(E) ≥ n² BE`
  have hmain : (n : ℝ) ^ 2 * ckBE q t (fun _ => (n : ℝ)⁻¹) m ≤
      ∑ e, InformationTheory.klFun (E e) := by
    have h1 : (n : ℝ) ^ 2 * ckBE q t (fun _ => (n : ℝ)⁻¹) m = ∑ e, ckLam (E e) := by
      unfold ckBE
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [hE]
      field_simp
    have h2 : ∑ e, E e ≤ (n : ℝ) ^ 2 := by
      rw [Fintype.sum_prod_type]
      exact CKEdgeB_sum_betheE_le hp hn m hm1
    rw [h1]
    simp only [CKEdgeB_klFun_eq]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, CKEdgeB_sum_const_pairs]
    linarith
  -- pairwise deviations
  have hdiff : ∑ e, |A e - E e| ≤
      2 * ckMp t * ((n : ℝ) ^ 2 * ckIota2 μ) + n * (ckMp t - ckMm q t) := by
    rw [Fintype.sum_prod_type]
    have hrow : ∀ v, ∑ w, |A (v, w) - E (v, w)| ≤ (ckMp t - ckMm q t) +
        ∑ w ∈ Finset.univ.erase v, 2 * ckMp t * Real.sqrt (ckMI μ {v} {w} ∅) := by
      intro v
      rw [← Finset.add_sum_erase Finset.univ (fun w => |A (v, w) - E (v, w)|)
        (Finset.mem_univ v)]
      refine add_le_add ?_ (Finset.sum_le_sum fun w hw => ?_)
      · have h1 := hAmem (v, v)
        have h2 := hEmem (v, v)
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      · exact ck_pair_decorr hp hμ (Finset.ne_of_mem_erase hw).symm
    calc ∑ v, ∑ w, |A (v, w) - E (v, w)| ≤ ∑ v, ((ckMp t - ckMm q t) +
          ∑ w ∈ Finset.univ.erase v, 2 * ckMp t * Real.sqrt (ckMI μ {v} {w} ∅)) :=
          Finset.sum_le_sum fun v _ => hrow v
      _ = n * (ckMp t - ckMm q t) + 2 * ckMp t *
          ∑ v, ∑ w ∈ Finset.univ.erase v, Real.sqrt (ckMI μ {v} {w} ∅) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
      _ ≤ _ := by
        have hio : ∑ v, ∑ w ∈ Finset.univ.erase v, Real.sqrt (ckMI μ {v} {w} ∅) ≤
            (n : ℝ) ^ 2 * ckIota2 μ :=
          CKEdgeB_cs (fun v w => ckMI μ {v} {w} ∅) (fun v w => ck_MI_nonneg hμ _ _ _)
        nlinarith [mul_le_mul_of_nonneg_left hio (by linarith [hb.2.2.1] : (0:ℝ) ≤ 2 * ckMp t)]
  -- per-pair Lipschitz comparison
  have hkl : ∀ e, InformationTheory.klFun (E e) - ckEll q t * |A e - E e| ≤
      InformationTheory.klFun (A e) := by
    intro e
    have h1 := CKEdgeB_kl_lip hp (hAmem e) (hEmem e)
    have h2 := neg_abs_le (InformationTheory.klFun (A e) - InformationTheory.klFun (E e))
    linarith
  have hsum : ∑ e, (InformationTheory.klFun (E e) - ckEll q t * |A e - E e|) ≤
      ckEdgeKL q t μ := by
    unfold ckEdgeKL
    exact Finset.sum_le_sum fun e _ => hkl e
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have hl0 : 0 ≤ ckEll q t := hb.2.2.2.2.2.1.le
  have key : (n : ℝ) ^ 2 * (ckBE q t (fun _ => (n : ℝ)⁻¹) m -
      2 * ckEll q t * ckMp t * ckIota2 μ - ckEll q t * (ckMp t - ckMm q t) / n) =
      (n : ℝ) ^ 2 * ckBE q t (fun _ => (n : ℝ)⁻¹) m - ckEll q t *
        (2 * ckMp t * ((n : ℝ) ^ 2 * ckIota2 μ) + n * (ckMp t - ckMm q t)) := by
    field_simp
    ring
  rw [key]
  nlinarith [mul_le_mul_of_nonneg_left hdiff hl0]

end

end ERZeroFreeness
