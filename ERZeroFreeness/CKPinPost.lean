/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CKDefs
import ERZeroFreeness.CKInfo
import ERZeroFreeness.CKBern
import ERZeroFreeness.CKPlanted
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.RSModel
import ERZeroFreeness.RSBetheBasic
import ERZeroFreeness.RSPoisSplit
import ERZeroFreeness.Poisson

/-!
# Proof of [CKPZ, Prop. 3.6]: Corollary 6.2 (pinning the posterior to the ground truth)

Part of the self-contained proof of `CKPZProp36 q`, the Potts case of the planted free-energy
bound of Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Prop. 3.6], which Lemma C.3
(`lem:rs-ckpz`) cites.  Appendix C is formalized in two layers: the `RS*` modules prove
Theorem C.1 from `CKPZProp36 q` as an explicit hypothesis, and the `CK*` modules prove
`CKPZProp36 q`.  Lemma numbers refer to `docs/ckpz-proof.md`.

Let `ϱ ≥ 0`, `p ∈ (0,1)`, `T ≥ 1` and `π_k = 1 - (1-p)^k`, and let `𝖰_k = 𝖰_{[n],ϱ,π_k}` be the
planted triple law (`ckQExp`), with pinned posterior `post = post_{G,U,σ}` (`ckPost`).  The
functionals are `𝒥̄_p` (`ckJbar`) and `ι₂` (`ckIota2`).

* Corollary 6.2(a) (`ck_pin_post_J`): `T⁻¹ ∑_{k<T} E_{𝖰_k} 𝒥̄_p(post) ≤ p/(1-p) · n log q / T`.
* Corollary 6.2(b) (`ck_pin_post_iota`): for `n ≥ 2`,
  `T⁻¹ ∑_{k<T} E_{𝖰_k} ι₂(post)² ≤ (1 + np)/(np) · log q / T`.

## Proof

The Nishimori identity with the unpinned posterior (`ck_nishimori_free`, Lemma 4.3) replaces
the planted colouring `σ`, which supplies the pin values `σ_U`, by a sample `τ` of the unpinned
posterior `μ_G = post_{G,∅,σ}`, which does not depend on `σ` (`CKPinPostA_post_empty`).  Since
`post_{G,U,τ} = μ_G(· | τ'_U = τ_U)`, averaging over `τ` turns each mutual information under the
pinned posterior into the conditional mutual information under `μ_G` given `τ_U` ((E2),
`ck_MI_cond_avg`; `CKPinPostA_avg_J`, `CKPinPostA_avg_iota`).  This is the pin averaging of
Lemma 4.4(a).  Lemma 6.1 (`ck_pinning_J`, `ck_pinning_pairs`) bounds the resulting average over
`k < T` for each fixed `(σ, G)`, and `CKPinPostA_avg_le` integrates the bound against the law of
`(σ, G)`, which does not depend on `k`.
-/

open Filter Topology MeasureTheory

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Helpers: the planted law, boundedness and the exchange of sums -/

private lemma CKPinPostA_rate_nonneg {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (e : Fin n × Fin n) : 0 ≤ ckPl q t ϱ σ e :=
  mul_nonneg hϱ (lt_of_lt_of_le (ck_const_bounds hp).1 (ck_rsM_mem hp _ _).1).le

private lemma CKPinPostA_summable {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) {f : RSGraph n → ℝ} {C : ℝ} (hf : ∀ G, |f G| ≤ C) :
    Summable fun G => poisPi (ckPl q t ϱ σ) G * f G :=
  rs_summable_poisPi_of_abs_le (CKPinPostA_rate_nonneg hp hϱ σ) zero_le_one
    (fun G => by rw [one_pow, mul_one]; exact hf G)

private lemma CKPinPostA_tsum_const {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (σ : Fin n → Fin q) (B : ℝ) :
    ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * B = B := by
  rw [tsum_mul_right, (rs_hasSum_poisPi (CKPinPostA_rate_nonneg hp hϱ σ)).tsum_eq, one_mul]

/-- `|∑_U B_π(U) g(U)| ≤ (∑_U |B_π(U)|) C`. -/
private lemma CKPinPostA_abs_bern_sum_le {n : ℕ} (π : ℝ) {g : Finset (Fin n) → ℝ} {C : ℝ}
    (hg : ∀ U, |g U| ≤ C) :
    |∑ U, ckBern π U * g U| ≤ (∑ U : Finset (Fin n), |ckBern π U|) * C := by
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun U _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hg U) (abs_nonneg _)

/-- `E_{𝖰_π} g = q^{-n} ∑_σ ∑'_G 𝖯^σ(G) ∑_U B_π(U) g(σ,G,U)` for bounded `g`. -/
private lemma CKPinPostA_QExp_eq {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (π : ℝ) (g : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) {C : ℝ}
    (hg : ∀ σ G U, |g σ G U| ≤ C) :
    ckQExp q t ϱ π n g = ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
      ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern π U * g σ G U := by
  unfold ckQExp
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hs : ∀ U ∈ (Finset.univ : Finset (Finset (Fin n))),
      Summable fun G => ckBern π U * (poisPi (ckPl q t ϱ σ) G * g σ G U) :=
    fun U _ => (CKPinPostA_summable hp hϱ σ (fun G => hg σ G U)).mul_left _
  calc ∑ U, ckBern π U * ∑' G, poisPi (ckPl q t ϱ σ) G * g σ G U
      = ∑ U, ∑' G, ckBern π U * (poisPi (ckPl q t ϱ σ) G * g σ G U) :=
        Finset.sum_congr rfl fun U _ => tsum_mul_left.symm
    _ = ∑' G, ∑ U, ckBern π U * (poisPi (ckPl q t ϱ σ) G * g σ G U) :=
        (Summable.tsum_finsetSum hs).symm
    _ = ∑' G, poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern π U * g σ G U := by
        refine tsum_congr fun G => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun U _ => by ring

/-- Averaging over the layers `k < T`: a bound on `T⁻¹ ∑_k ∑_U B_{π_k}(U) g(σ,G,U)`, uniform in
`(σ,G)`, integrates to the same bound on `T⁻¹ ∑_k E_{𝖰_{π_k}} g`. -/
private lemma CKPinPostA_avg_le {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (π : ℕ → ℝ) (T : ℕ) (g : (Fin n → Fin q) → RSGraph n → Finset (Fin n) → ℝ) {C : ℝ}
    (hg : ∀ σ G U, |g σ G U| ≤ C) {B : ℝ}
    (hB : ∀ σ G, (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ U, ckBern (π k) U * g σ G U ≤ B) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ckQExp q t ϱ (π k) n g ≤ B := by
  have hhb : ∀ k σ G, |∑ U, ckBern (π k) U * g σ G U| ≤
      (∑ U : Finset (Fin n), |ckBern (π k) U|) * C :=
    fun k σ G => CKPinPostA_abs_bern_sum_le (π k) (fun U => hg σ G U)
  have hsum : ∀ k σ, Summable fun G =>
      poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern (π k) U * g σ G U :=
    fun k σ => CKPinPostA_summable hp hϱ σ (hhb k σ)
  have hσ : ∀ σ, (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T,
      ∑' G, poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern (π k) U * g σ G U ≤ B := by
    intro σ
    have hY : ∀ G, |(T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ U, ckBern (π k) U * g σ G U| ≤
        |(T : ℝ)⁻¹| * ∑ k ∈ Finset.range T, (∑ U : Finset (Fin n), |ckBern (π k) U|) * C := by
      intro G
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hhb k σ G)
    calc (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T,
          ∑' G, poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern (π k) U * g σ G U
        = ∑' G, poisPi (ckPl q t ϱ σ) G *
            ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ U, ckBern (π k) U * g σ G U) := by
          rw [← Summable.tsum_finsetSum (fun k _ => hsum k σ), ← tsum_mul_left]
          refine tsum_congr fun G => ?_
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ ≤ ∑' G, poisPi (ckPl q t ϱ σ) G * B := by
          refine Summable.tsum_le_tsum (fun G => ?_) (CKPinPostA_summable hp hϱ σ hY)
            (CKPinPostA_summable hp hϱ σ (fun _ => le_refl |B|))
          exact mul_le_mul_of_nonneg_left (hB σ G)
            (rs_poisPi_nonneg (CKPinPostA_rate_nonneg hp hϱ σ) G)
      _ = B := CKPinPostA_tsum_const hp hϱ σ B
  have hq : (0 : ℝ) < (q : ℝ) ^ n :=
    pow_pos (by have := hp.two_le; exact_mod_cast (by omega : 0 < q)) n
  calc (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ckQExp q t ϱ (π k) n g
      = (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q,
          ∑' G : RSGraph n, poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern (π k) U * g σ G U := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => CKPinPostA_QExp_eq hp hϱ (π k) g hg
    _ = ((q : ℝ) ^ n)⁻¹ * ∑ σ : Fin n → Fin q, ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T,
          ∑' G, poisPi (ckPl q t ϱ σ) G * ∑ U, ckBern (π k) U * g σ G U) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ((q : ℝ) ^ n)⁻¹ * ∑ _σ : Fin n → Fin q, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hσ σ) (inv_nonneg.2 hq.le)
    _ = B := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, ← mul_assoc,
          inv_mul_cancel₀ hq.ne', one_mul]

/-! ### Helpers: information bounds and the pin average (E2) -/

private lemma CKPinPostA_logq_nonneg {q : ℕ} {t : ℝ} (hp : CKPar q t) : 0 ≤ Real.log q :=
  Real.log_nonneg (by have := hp.two_le; exact_mod_cast (by omega : 1 ≤ q))

/-- `0 ≤ 𝒥_μ(W | S) ≤ n log q`. -/
private lemma CKPinPostA_J_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (hlog : 0 ≤ Real.log q) (W S : Finset (Fin n)) :
    0 ≤ ckJ μ W S ∧ ckJ μ W S ≤ n * Real.log q := by
  refine ⟨Finset.sum_nonneg fun w _ => ck_MI_nonneg hμ _ _ _, ?_⟩
  calc ckJ μ W S ≤ ∑ _w ∈ W, Real.log q :=
        Finset.sum_le_sum fun w _ => ck_MI_single_le hμ w _ _
    _ = W.card * Real.log q := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ n * Real.log q := by
        refine mul_le_mul_of_nonneg_right ?_ hlog
        have h := Finset.card_le_univ W
        rw [Fintype.card_fin] at h
        exact_mod_cast h

/-- `|E_W 𝒥_μ(W | S)| ≤ n log q`. -/
private lemma CKPinPostA_Jbar_abs_le {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (hlog : 0 ≤ Real.log q) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset (Fin n)) :
    |∑ W : Finset (Fin n), ckBern p W * ckJ μ W S| ≤ n * Real.log q := by
  have h0 : 0 ≤ ∑ W : Finset (Fin n), ckBern p W * ckJ μ W S :=
    Finset.sum_nonneg fun W _ =>
      mul_nonneg (ck_bern_nonneg hp0 hp1 W) (CKPinPostA_J_mem hμ hlog W S).1
  rw [abs_of_nonneg h0]
  calc ∑ W : Finset (Fin n), ckBern p W * ckJ μ W S
      ≤ ∑ W : Finset (Fin n), ckBern p W * (n * Real.log q) :=
        Finset.sum_le_sum fun W _ => mul_le_mul_of_nonneg_left
          (CKPinPostA_J_mem hμ hlog W S).2 (ck_bern_nonneg hp0 hp1 W)
    _ = n * Real.log q := by rw [← Finset.sum_mul, ck_bern_sum, one_mul]

/-- `0 ≤ ∑_{v ≠ w} I(τ_v; τ_w | τ_S) ≤ n (n log q)`. -/
private lemma CKPinPostA_pairs_mem {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ)
    (hlog : 0 ≤ Real.log q) (S : Finset (Fin n)) :
    0 ≤ ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} S ∧
      ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} S ≤ n * (n * Real.log q) := by
  refine ⟨Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => ck_MI_nonneg hμ _ _ _, ?_⟩
  have hin : ∀ v : Fin n, ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} S ≤ n * Real.log q := by
    intro v
    calc ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} S
        ≤ ∑ _w ∈ Finset.univ.erase v, Real.log q :=
          Finset.sum_le_sum fun w _ => ck_MI_single_le hμ v _ _
      _ = (Finset.univ.erase v).card * Real.log q := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ n * Real.log q := by
          refine mul_le_mul_of_nonneg_right ?_ hlog
          have h := Finset.card_le_univ (Finset.univ.erase v)
          rw [Fintype.card_fin] at h
          exact_mod_cast h
  calc ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} S ≤ ∑ _v : Fin n, n * Real.log q :=
        Finset.sum_le_sum fun v _ => hin v
    _ = n * (n * Real.log q) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `ι₂(μ)² = n⁻² ∑_{v ≠ w} I(τ_v; τ_w)`. -/
private lemma CKPinPostA_iota_sq {n q : ℕ} {μ : (Fin n → Fin q) → ℝ} (hμ : IsPMF μ) :
    ckIota2 μ ^ 2 = ((n : ℝ) ^ 2)⁻¹ * ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI μ {v} {w} ∅ := by
  unfold ckIota2
  rw [Real.sq_sqrt]
  exact mul_nonneg (inv_nonneg.2 (sq_nonneg _))
    (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => ck_MI_nonneg hμ _ _ _)

/-- The unpinned posterior does not depend on the planted configuration. -/
private lemma CKPinPostA_post_empty {q n : ℕ} (t ϱ : ℝ) (G : RSGraph n) (σ τ : Fin n → Fin q) :
    ckPost q t ϱ G ∅ σ = ckPost q t ϱ G ∅ τ := by
  funext ρ
  simp [ckPost, ckAgree]

/-- Averaging `𝒥̄_p` of the pinned posterior over the pin values (E2). -/
private lemma CKPinPostA_avg_J {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (p : ℝ)
    (G : RSGraph n) (U : Finset (Fin n)) (σ : Fin n → Fin q) :
    ∑ τ, ckPost q t ϱ G ∅ σ τ * ckJbar p (ckPost q t ϱ G U τ) =
      ∑ W, ckBern p W * ckJ (ckPost q t ϱ G ∅ σ) W U := by
  have hμ : IsPMF (ckPost q t ϱ G ∅ σ) := ck_post_isPMF hp hϱ G ∅ σ
  have hc : ∀ τ, ckPost q t ϱ G U τ = ckCond (ckPost q t ϱ G ∅ σ) U τ := fun τ => by
    rw [ck_post_eq_cond hp hϱ G U τ, CKPinPostA_post_empty t ϱ G τ σ]
  simp only [hc, ckJbar, ckJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← ck_MI_cond_avg hμ U {w} (W.erase w), Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

/-- Averaging `ι₂²` of the pinned posterior over the pin values (E2). -/
private lemma CKPinPostA_avg_iota {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    (G : RSGraph n) (U : Finset (Fin n)) (σ : Fin n → Fin q) :
    ∑ τ, ckPost q t ϱ G ∅ σ τ * ckIota2 (ckPost q t ϱ G U τ) ^ 2 =
      ((n : ℝ) ^ 2)⁻¹ *
        ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI (ckPost q t ϱ G ∅ σ) {v} {w} U := by
  have hμ : IsPMF (ckPost q t ϱ G ∅ σ) := ck_post_isPMF hp hϱ G ∅ σ
  have hsq : ∀ τ, ckIota2 (ckPost q t ϱ G U τ) ^ 2 = ((n : ℝ) ^ 2)⁻¹ *
      ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI (ckCond (ckPost q t ϱ G ∅ σ) U τ) {v} {w} ∅ :=
    fun τ => by
      rw [CKPinPostA_iota_sq (ck_post_isPMF hp hϱ G U τ), ck_post_eq_cond hp hϱ G U τ,
        CKPinPostA_post_empty t ϱ G τ σ]
  simp only [hsq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← ck_MI_cond_avg hμ U {v} {w}, Finset.mul_sum]
  exact Finset.sum_congr rfl fun τ _ => by ring

/-- Corollary 6.2(a): for `p ∈ (0,1)`, `T ≥ 1` and `π_k = 1 - (1-p)^k`,
`T⁻¹ ∑_{k<T} E_{𝖰_{π_k}} 𝒥̄_p(post_{G,U,σ}) ≤ p/(1-p) · n log q / T`. -/
theorem ck_pin_post_J {q n : ℕ} {t : ℝ} (hp : CKPar q t) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T,
        ckQExp q t ϱ (1 - (1 - p) ^ k) n (fun σ G U => ckJbar p (ckPost q t ϱ G U σ)) ≤
      p / (1 - p) * (n * Real.log q) / T := by
  have hlog := CKPinPostA_logq_nonneg hp
  have hbd : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)),
      |ckJbar p (ckPost q t ϱ G U σ)| ≤ n * Real.log q * 1 ^ rsEdges G := by
    intro σ G U
    rw [one_pow, mul_one]
    exact CKPinPostA_Jbar_abs_le (ck_post_isPMF hp hϱ G U σ) hlog hp0.le hp1.le ∅
  have hrw : ∀ π : ℝ,
      ckQExp q t ϱ π n (fun σ G U => ckJbar p (ckPost q t ϱ G U σ)) =
        ckQExp q t ϱ π n (fun σ G U => ∑ W, ckBern p W * ckJ (ckPost q t ϱ G ∅ σ) W U) := by
    intro π
    rw [ck_nishimori_free hp hϱ π (fun σ G U => ckJbar p (ckPost q t ϱ G U σ)) zero_le_one hbd]
    congr 1
    funext σ G U
    exact CKPinPostA_avg_J hp hϱ p G U σ
  rw [Finset.sum_congr rfl fun k _ => hrw (1 - (1 - p) ^ k)]
  refine CKPinPostA_avg_le hp hϱ (fun k => 1 - (1 - p) ^ k) T
    (fun σ G U => ∑ W, ckBern p W * ckJ (ckPost q t ϱ G ∅ σ) W U) (C := n * Real.log q)
    (fun σ G U => CKPinPostA_Jbar_abs_le (ck_post_isPMF hp hϱ G ∅ σ) hlog hp0.le hp1.le U)
    (fun σ G => ?_)
  exact ck_pinning_J (ck_post_isPMF hp hϱ G ∅ σ) hp0 hp1 hT

/-- Corollary 6.2(b): for `n ≥ 2`, `p ∈ (0,1)`, `T ≥ 1` and `π_k = 1 - (1-p)^k`,
`T⁻¹ ∑_{k<T} E_{𝖰_{π_k}} ι₂(post_{G,U,σ})² ≤ (1 + np)/(np) · log q / T`. -/
theorem ck_pin_post_iota {q n : ℕ} {t : ℝ} (hp : CKPar q t) (hn : 2 ≤ n) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {T : ℕ} (hT : 1 ≤ T) :
    (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T,
        ckQExp q t ϱ (1 - (1 - p) ^ k) n (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2) ≤
      (1 + n * p) / (n * p) * Real.log q / T := by
  have hlog := CKPinPostA_logq_nonneg hp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hbd : ∀ (σ : Fin n → Fin q) (G : RSGraph n) (U : Finset (Fin n)),
      |ckIota2 (ckPost q t ϱ G U σ) ^ 2| ≤
      ((n : ℝ) ^ 2)⁻¹ * (n * (n * Real.log q)) * 1 ^ rsEdges G := by
    intro σ G U
    have hμ := ck_post_isPMF hp hϱ G U σ
    have h := CKPinPostA_pairs_mem hμ hlog ∅
    rw [one_pow, mul_one, CKPinPostA_iota_sq hμ,
      abs_of_nonneg (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) h.1)]
    exact mul_le_mul_of_nonneg_left h.2 (inv_nonneg.2 (sq_nonneg _))
  have hrw : ∀ π : ℝ,
      ckQExp q t ϱ π n (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2) =
        ckQExp q t ϱ π n (fun σ G U => ((n : ℝ) ^ 2)⁻¹ *
          ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI (ckPost q t ϱ G ∅ σ) {v} {w} U) := by
    intro π
    rw [ck_nishimori_free hp hϱ π (fun σ G U => ckIota2 (ckPost q t ϱ G U σ) ^ 2)
      zero_le_one hbd]
    congr 1
    funext σ G U
    exact CKPinPostA_avg_iota hp hϱ G U σ
  rw [Finset.sum_congr rfl fun k _ => hrw (1 - (1 - p) ^ k)]
  refine CKPinPostA_avg_le hp hϱ (fun k => 1 - (1 - p) ^ k) T
    (fun σ G U => ((n : ℝ) ^ 2)⁻¹ *
      ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI (ckPost q t ϱ G ∅ σ) {v} {w} U)
    (C := ((n : ℝ) ^ 2)⁻¹ * (n * (n * Real.log q))) (fun σ G U => ?_) (fun σ G => ?_)
  · have h := CKPinPostA_pairs_mem (ck_post_isPMF hp hϱ G ∅ σ) hlog U
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.2 (sq_nonneg _)) h.1)]
    exact mul_le_mul_of_nonneg_left h.2 (inv_nonneg.2 (sq_nonneg _))
  · have h := ck_pinning_pairs hn (ck_post_isPMF hp hϱ G ∅ σ) hp0 hp1 hT
    calc (T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ U, ckBern (1 - (1 - p) ^ k) U *
          (((n : ℝ) ^ 2)⁻¹ *
            ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI (ckPost q t ϱ G ∅ σ) {v} {w} U)
        = ((n : ℝ) ^ 2)⁻¹ * ((T : ℝ)⁻¹ * ∑ k ∈ Finset.range T, ∑ U,
            ckBern (1 - (1 - p) ^ k) U *
              ∑ v, ∑ w ∈ Finset.univ.erase v, ckMI (ckPost q t ϱ G ∅ σ) {v} {w} U) := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun U _ =>
            Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => by ring
      _ ≤ ((n : ℝ) ^ 2)⁻¹ * ((1 + n * p) / p * (n * Real.log q) / T) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 (sq_nonneg _))
      _ = (1 + n * p) / (n * p) * Real.log q / T := by
          field_simp

end

end ERZeroFreeness
