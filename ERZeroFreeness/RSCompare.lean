/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSPoisPi
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.TwoReplica

/-!
# Appendix C: comparison of `G(n, d/n)` with the Poisson multigraph `𝖯_d`

Used in the proof of Proposition C.2 (`prop:rs-first-moment`):

* `rs_erExp_le_rsExp`: for `0 < d ≤ n` and every complex `t`,
  `E_{G(n,d/n)} |Ẑ_G(t)| ≤ e^{d/2} E_{𝖯_d}[e^{dm/n} |F_G(t)|]`;
* `rs_erExp_le_pow`: `E_{G(n,p)} |Ẑ_G(t)| ≤ (1 + (q-1)T)^{C(n,2)}` for `‖t‖ ≤ T`, `p ∈ [0,1]` (for
  the finitely many `n` below the threshold of Lemma C.4).

**Deviation from the paper.**  The paper conditions `𝖯_d` on simplicity (the conditional law of
`Ḡ` is `G(n, d/(n+d))`) and compares likelihoods, with constant `e^{d/2 + d²/4}`.  Here the
conditioning is replaced by a deterministic injection: each pair (simple graph `Γ`, set `T` of
edges oriented "upwards") is mapped to an ordered multigraph with `0/1` counts, whose `𝖯_d`-mass is
`e^{-dn/2}(d/(2n))^{|E(Γ)|}`, so the `2^{|E(Γ)|}` orientations of `Γ` carry total mass
`e^{-dn/2}(d/n)^{|E(Γ)|}`; and `erWeight(Γ) ≤ e^{d/2} e^{d|E(Γ)|/n} e^{-dn/2} (d/n)^{|E(Γ)|}`
(`(1-p)^j ≤ e^{-pj}`), which gives the constant `e^{d/2}`.
The map is `orient` (injective by `orient_inj`), and on its image `F_G(t) = Ẑ_Γ(t)`
(`rsc_rsF_orient`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace RSCompareAux

/-- Product Poisson weights with nonnegative means are nonnegative. -/
theorem rsc_poisPi_nonneg {n : ℕ} {lam : Fin n × Fin n → ℝ} (hlam : ∀ uv, 0 ≤ lam uv)
    (N : RSGraph n) : 0 ≤ poisPi lam N :=
  Finset.prod_nonneg fun uv _ => poisPMF_nonneg (hlam uv) (N uv)

/-- `E_{𝖯}[c^m] = exp(λ(c-1))^{n²}` for constant means `λ`. -/
theorem rsc_hasSum_poisPi_mul_pow {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) {c : ℝ} (hc : 0 ≤ c) :
    HasSum (fun N : RSGraph n => poisPi (fun _ => lam) N * c ^ rsEdges N)
      (Real.exp (lam * (c - 1)) ^ (n * n)) := by
  have H := RSPoisPiAux.hasSum_fintype_pi_prod (ι := Fin n × Fin n)
    (fun _ k => poisPMF lam k * c ^ k)
    (fun _ k => mul_nonneg (poisPMF_nonneg hlam k) (pow_nonneg hc k))
    (fun _ => Real.exp (lam * (c - 1))) (fun _ => RSPoisPiAux.hasSum_poisPMF_mul_pow c)
  convert H using 1
  · funext N
    simp only [poisPi, rsEdges, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  · simp [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- `|M_t(a,b)| ≤ 1 + (q-1)|t|`. -/
theorem rsc_norm_rsM_le {q : ℕ} (hq : 2 ≤ q) (t : ℂ) (a b : Fin q) :
    ‖rsM q t a b‖ ≤ 1 + ((q : ℝ) - 1) * ‖t‖ := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold rsM rsA
  split_ifs
  · have h : (((q : ℤ) - 1 : ℤ) : ℂ) = (((q : ℝ) - 1 : ℝ) : ℂ) := by push_cast; ring
    rw [h]
    calc ‖1 + t * (((q : ℝ) - 1 : ℝ) : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖t * (((q : ℝ) - 1 : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = 1 + ((q : ℝ) - 1) * ‖t‖ := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith)]
          ring
  · calc ‖1 + t * (((-1 : ℤ)) : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖t * (((-1 : ℤ)) : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖t‖ := by simp
      _ ≤ 1 + ((q : ℝ) - 1) * ‖t‖ := by nlinarith [norm_nonneg t]

/-- `|F_G(t)| ≤ (1 + (q-1)|t|)^m`, `m` the number of edges of `G`. -/
theorem rsc_norm_rsF_le {q n : ℕ} (hq : 2 ≤ q) (N : RSGraph n) (t : ℂ) :
    ‖rsF q t N‖ ≤ (1 + ((q : ℝ) - 1) * ‖t‖) ^ rsEdges N := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hσ : ∀ σ : Fin n → Fin q,
      ‖∏ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) ^ N uv‖ ≤
        (1 + ((q : ℝ) - 1) * ‖t‖) ^ rsEdges N := by
    intro σ
    rw [norm_prod, rsEdges, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun uv _ => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (rsc_norm_rsM_le hq t _ _) _)
  unfold rsF rsW
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hσ σ)
    (by positivity)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul]

/-- The integrand `e^{dm/n} |F_G(t)|` is summable against `𝖯_d`. -/
theorem rsc_summable_cmp {q n : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 ≤ d) (t : ℂ) :
    Summable (fun N : RSGraph n => poisPi (fun _ => d / (2 * n)) N *
      (Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖)) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set c : ℝ := Real.exp (d / n) * (1 + ((q : ℝ) - 1) * ‖t‖) with hc_def
  have hK : 0 ≤ 1 + ((q : ℝ) - 1) * ‖t‖ := by nlinarith [norm_nonneg t]
  have hc : 0 ≤ c := mul_nonneg (Real.exp_pos _).le hK
  have hlam : 0 ≤ d / (2 * (n : ℝ)) := by positivity
  refine (rsc_hasSum_poisPi_mul_pow (n := n) hlam hc).summable.of_nonneg_of_le (fun N => ?_)
    (fun N => ?_)
  · exact mul_nonneg (rsc_poisPi_nonneg (fun _ => hlam) N)
      (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  · refine mul_le_mul_of_nonneg_left ?_ (rsc_poisPi_nonneg (fun _ => hlam) N)
    have he : Real.exp (d * (rsEdges N : ℝ) / n) = Real.exp (d / n) ^ rsEdges N := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [he, hc_def, mul_pow]
    exact mul_le_mul_of_nonneg_left (rsc_norm_rsF_le hq N t) (pow_nonneg (Real.exp_pos _).le _)

/-- Small-`n` bound: `‖Ẑ_G(t)‖ ≤ (1 + (q-1)|t|)^{|E(G)|}`. -/
theorem rsc_norm_zhat_eval_le {q n : ℕ} (hq : 2 ≤ q) (G : SimpleGraph (Fin n)) (t : ℂ) :
    ‖(zhat G q).eval t‖ ≤ (1 + ((q : ℝ) - 1) * ‖t‖) ^ G.edgeFinset.card := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hfac : ∀ (σ : Fin n → Fin q) (e : Sym2 (Fin n)),
      ‖1 + t * edgeA q σ e‖ ≤ 1 + ((q : ℝ) - 1) * ‖t‖ := by
    intro σ e
    rw [TwoReplicaAux.edgeA_eq_ofReal]
    calc ‖1 + t * (TwoReplicaAux.aRe q σ e : ℂ)‖
        ≤ ‖(1 : ℂ)‖ + ‖t * (TwoReplicaAux.aRe q σ e : ℂ)‖ := norm_add_le _ _
      _ = 1 + ‖t‖ * |TwoReplicaAux.aRe q σ e| := by
          rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + ‖t‖ * ((q : ℝ) - 1) := by
          gcongr; exact TwoReplicaAux.abs_aRe_le hq σ e
      _ = 1 + ((q : ℝ) - 1) * ‖t‖ := by ring
  have hσ : ∀ σ : Fin n → Fin q, ‖∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ≤
      (1 + ((q : ℝ) - 1) * ‖t‖) ^ G.edgeFinset.card := by
    intro σ
    rw [norm_prod, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun e _ => norm_nonneg _) (fun e _ => hfac σ e)
  have hz : (zhat G q).eval t = ((q : ℂ) ^ n)⁻¹ *
      ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e) := by
    rw [zhat_eval]
    simp only [Fintype.card_fin]
    congr 1
    exact Finset.sum_congr (Finset.ext fun σ => by simp) fun _ _ => rfl
  rw [hz, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)).trans ?_
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hσ σ)
    (by positivity)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq0.ne'), one_mul]

/-- The edge `{u,v}` (`u < v`) of `Γ` is oriented as `(u,v)` if it lies in `T`, else as `(v,u)`. -/
def orient {n : ℕ} (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) : RSGraph n :=
  fun uv => if Γ.Adj uv.1 uv.2 ∧ (uv.1 < uv.2 ↔ s(uv.1, uv.2) ∈ T) then 1 else 0

/-- The support of `orient Γ T`: the ordered pairs `(u,v)` that carry an edge of `Γ` oriented
from `u` to `v`. -/
def orientSupp {n : ℕ} (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter fun uv => Γ.Adj uv.1 uv.2 ∧ (uv.1 < uv.2 ↔ s(uv.1, uv.2) ∈ T)

variable {n : ℕ}

/-- Every pair of the support is an edge of `Γ`. -/
theorem orientSupp_mem {Γ : SimpleGraph (Fin n)} {T : Finset (Sym2 (Fin n))} :
    ∀ uv ∈ orientSupp Γ T, s(uv.1, uv.2) ∈ Γ.edgeFinset := by
  intro uv huv
  simp only [orientSupp, Finset.mem_filter, Finset.mem_univ, true_and] at huv
  exact SimpleGraph.mem_edgeFinset.2 huv.1

/-- Distinct pairs of the support are distinct edges of `Γ`. -/
theorem orientSupp_inj {Γ : SimpleGraph (Fin n)} {T : Finset (Sym2 (Fin n))} :
    ∀ uv ∈ orientSupp Γ T, ∀ uv' ∈ orientSupp Γ T,
      s(uv.1, uv.2) = s(uv'.1, uv'.2) → uv = uv' := by
  rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' h
  simp only [orientSupp, Finset.mem_filter, Finset.mem_univ, true_and] at huv huv'
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exfalso
    have hne : u ≠ v := Γ.ne_of_adj huv.1
    have hs : s(v, u) = s(u, v) := Sym2.eq_swap
    have h1 := huv.2
    have h2 := huv'.2
    rw [hs] at h2
    rcases lt_or_gt_of_ne hne with h | h
    · exact (lt_asymm h) (h2.2 (h1.1 h))
    · exact (lt_asymm h) (h1.2 (h2.1 h))

/-- Every edge of `Γ` comes from a pair of the support. -/
theorem orientSupp_surj {Γ : SimpleGraph (Fin n)} {T : Finset (Sym2 (Fin n))} :
    ∀ e ∈ Γ.edgeFinset, ∃ uv ∈ orientSupp Γ T, s(uv.1, uv.2) = e := by
  intro e he
  induction e using Sym2.ind with
  | h u v =>
    have hadj : Γ.Adj u v := SimpleGraph.mem_edgeFinset.1 he
    have hne : u ≠ v := Γ.ne_of_adj hadj
    by_cases h : (u < v ↔ s(u, v) ∈ T)
    · exact ⟨(u, v), by simp [orientSupp, hadj, h], rfl⟩
    · refine ⟨(v, u), ?_, Sym2.eq_swap⟩
      simp only [orientSupp, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hadj.symm, ?_⟩
      rw [Sym2.eq_swap]
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact ⟨fun h'' => absurd h' (lt_asymm h''), fun hT => absurd ⟨fun _ => hT, fun _ => h'⟩ h⟩
      · exact ⟨fun _ => by by_contra hT; exact h ⟨fun h'' => absurd h' (lt_asymm h''),
          fun h'' => absurd h'' hT⟩, fun _ => h'⟩

/-- The support has `|E(Γ)|` elements. -/
theorem card_orientSupp (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) :
    (orientSupp Γ T).card = Γ.edgeFinset.card :=
  Finset.card_bij (fun uv _ => s(uv.1, uv.2)) orientSupp_mem orientSupp_inj
    (fun e he => by
      obtain ⟨uv, huv, h⟩ := orientSupp_surj (Γ := Γ) (T := T) e he
      exact ⟨uv, huv, h⟩)

/-- `orient Γ T` has `|E(Γ)|` edges. -/
theorem rsc_rsEdges_orient (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) :
    rsEdges (orient Γ T) = Γ.edgeFinset.card := by
  rw [← card_orientSupp Γ T, rsEdges, orientSupp, Finset.card_filter]
  rfl

/-- The mass of `orient Γ T` under constant Poisson means `λ` is `e^{-λn²} λ^{|E(Γ)|}`. -/
theorem rsc_poisPi_orient (lam : ℝ) (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) :
    poisPi (fun _ => lam) (orient Γ T) =
      Real.exp (-lam) ^ (n * n) * lam ^ Γ.edgeFinset.card := by
  have h : ∀ uv, poisPMF lam (orient Γ T uv) = Real.exp (-lam) * lam ^ orient Γ T uv := by
    intro uv
    unfold orient
    split_ifs <;> simp [poisPMF]
  rw [poisPi, Finset.prod_congr rfl fun uv _ => h uv, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.prod_pow_eq_pow_sum]
  have : ∑ uv : Fin n × Fin n, orient Γ T uv = Γ.edgeFinset.card := rsc_rsEdges_orient Γ T
  rw [this]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- On an orientation of `Γ`, `F_G(t) = Ẑ_Γ(t)`. -/
theorem rsc_rsF_orient {q : ℕ} (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) (t : ℂ) :
    rsF q t (orient Γ T) = (zhat Γ q).eval t := by
  rw [zhat_eval, rsF]
  simp only [Fintype.card_fin]
  congr 1
  refine Finset.sum_congr (Finset.ext fun σ => by simp) fun σ _ => ?_
  unfold rsW
  have h1 : ∀ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) ^ orient Γ T uv =
      if uv ∈ orientSupp Γ T then rsM q t (σ uv.1) (σ uv.2) else 1 := by
    intro uv
    simp only [orient, orientSupp, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp
  rw [Finset.prod_congr rfl fun uv _ => h1 uv, Finset.prod_ite_mem, Finset.univ_inter]
  refine Finset.prod_bij (fun uv _ => s(uv.1, uv.2)) orientSupp_mem orientSupp_inj
    (fun e he => by
      obtain ⟨uv, huv, h⟩ := orientSupp_surj (Γ := Γ) (T := T) e he
      exact ⟨uv, huv, h⟩) (fun uv _ => ?_)
  unfold rsM rsA edgeA
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
  split_ifs <;> push_cast <;> ring

/-- `Γ` is recovered from `orient Γ T`: `u ~ v` iff one of `(u,v)`, `(v,u)` carries an edge. -/
theorem orient_adj_iff (Γ : SimpleGraph (Fin n)) (T : Finset (Sym2 (Fin n))) (u v : Fin n) :
    Γ.Adj u v ↔ (orient Γ T (u, v) = 1 ∨ orient Γ T (v, u) = 1) := by
  constructor
  · intro hadj
    obtain ⟨uv, huv, he⟩ := orientSupp_surj (Γ := Γ) (T := T) s(u, v)
      (SimpleGraph.mem_edgeFinset.2 hadj)
    simp only [orientSupp, Finset.mem_filter, Finset.mem_univ, true_and] at huv
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; simp only [orient]; rw [← h1, ← h2]; simp [huv]
    · right; simp only [orient]; rw [← h1, ← h2]; simp [huv]
  · rintro (h | h)
    · simp only [orient] at h; split_ifs at h with hc
      · exact hc.1
    · simp only [orient] at h; split_ifs at h with hc
      · exact hc.1.symm

/-- For `T ⊆ E(Γ)` and `u < v`: `{u,v} ∈ T` iff `orient Γ T` has the edge `(u,v)`. -/
theorem mem_T_iff_orient {Γ : SimpleGraph (Fin n)} {T : Finset (Sym2 (Fin n))}
    (hT : T ⊆ Γ.edgeFinset) {u v : Fin n} (huv : u < v) :
    s(u, v) ∈ T ↔ orient Γ T (u, v) = 1 := by
  constructor
  · intro hs
    have hadj : Γ.Adj u v := SimpleGraph.mem_edgeFinset.1 (hT hs)
    simp [orient, hadj, huv, hs]
  · intro h
    simp only [orient] at h
    split_ifs at h with hc
    exact hc.2.1 huv

/-- `(Γ, T) ↦ orient Γ T` is injective on the pairs with `T ⊆ E(Γ)`. -/
theorem orient_inj {Γ Γ' : SimpleGraph (Fin n)} {T T' : Finset (Sym2 (Fin n))}
    (hT : T ⊆ Γ.edgeFinset) (hT' : T' ⊆ Γ'.edgeFinset) (h : orient Γ T = orient Γ' T') :
    Γ = Γ' ∧ T = T' := by
  have hG : Γ = Γ' := by
    ext u v
    rw [orient_adj_iff Γ T, orient_adj_iff Γ' T', h]
  subst hG
  refine ⟨rfl, ?_⟩
  ext e
  induction e using Sym2.ind with
  | h u v =>
    rcases lt_trichotomy u v with huv | rfl | huv
    · rw [mem_T_iff_orient hT huv, mem_T_iff_orient hT' huv, h]
    · constructor
      · intro hs; exact absurd (hT hs) (by simp)
      · intro hs; exact absurd (hT' hs) (by simp)
    · rw [Sym2.eq_swap, mem_T_iff_orient hT huv, mem_T_iff_orient hT' huv, h]

/-- Weight comparison: `G(n,d/n)` against the orientations of `Γ` under `𝖯_d`. -/
theorem rsc_erWeight_le_pois {d : ℝ} (hd : 0 ≤ d) (hdn : d ≤ n) (hn : 0 < n)
    (Γ : SimpleGraph (Fin n)) :
    erWeight n (d / n) Γ ≤ Real.exp (d / 2) * Real.exp (d * Γ.edgeFinset.card / n) *
      (Real.exp (-(d * n / 2)) * (d / n) ^ Γ.edgeFinset.card) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd hdn
  set k := Γ.edgeFinset.card with hk
  have hkN : k ≤ n.choose 2 := by
    have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := Γ)
    simpa [Fintype.card_fin] using this
  unfold erWeight
  rw [← hk]
  have h1 : (1 - d / n) ^ (n.choose 2 - k) ≤ Real.exp (-(d / n)) ^ (n.choose 2 - k) :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-(d / n))]) _
  have h2 : Real.exp (-(d / n)) ^ (n.choose 2 - k) =
      Real.exp (d / 2) * Real.exp (d * k / n) * Real.exp (-(d * n / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, Nat.cast_sub hkN,
      Nat.cast_choose_two]
    congr 1
    field_simp
    ring
  calc (d / n) ^ k * (1 - d / n) ^ (n.choose 2 - k)
      ≤ (d / n) ^ k * Real.exp (-(d / n)) ^ (n.choose 2 - k) :=
        mul_le_mul_of_nonneg_left h1 (pow_nonneg hp0 _)
    _ = _ := by rw [h2]; ring

end RSCompareAux

open RSCompareAux in
/-- **Comparison of `G(n,d/n)` with the Poisson multigraph `𝖯_d`** (replaces the conditioning
on simplicity in the proof of Proposition C.2): for `d ≤ n` and every complex `t`,
`E_{G(n,d/n)} |Ẑ_G(t)| ≤ e^{d/2} E_{𝖯_d}[e^{dm/n} |F_G(t)|]`. -/
theorem rs_erExp_le_rsExp {q n : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) (hdn : d ≤ n)
    (t : ℂ) :
    erExp n (d / n) (fun G => ‖(zhat G q).eval t‖) ≤
      Real.exp (d / 2) *
        rsExp n d (fun N => Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) := by
  have hn' : (0 : ℝ) < n := hd.trans_le hdn
  have hn : 0 < n := by exact_mod_cast hn'
  set g : RSGraph n → ℝ := fun N => poisPi (fun _ => d / (2 * (n : ℝ))) N *
    (Real.exp (d * (rsEdges N : ℝ) / n) * ‖rsF q t N‖) with hg
  have hlam : 0 ≤ d / (2 * (n : ℝ)) := by positivity
  have hg0 : ∀ N, 0 ≤ g N := fun N => mul_nonneg (rsc_poisPi_nonneg (fun _ => hlam) N)
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have hgs : Summable g := rsc_summable_cmp hq hd.le t
  set P := (Finset.univ : Finset (SimpleGraph (Fin n))).sigma
    fun Γ => Γ.edgeFinset.powerset with hP
  have hinj : Set.InjOn (fun p : (Σ _ : SimpleGraph (Fin n), Finset (Sym2 (Fin n))) =>
      orient p.1 p.2) P := by
    rintro ⟨Γ, T⟩ hp ⟨Γ', T'⟩ hp' h
    simp only [hP, Finset.coe_sigma, Set.mem_sigma_iff, Finset.coe_univ, Set.mem_univ,
      Finset.mem_coe, Finset.mem_powerset, true_and] at hp hp'
    obtain ⟨rfl, rfl⟩ := orient_inj hp hp' h
    rfl
  have hΓ : ∀ Γ : SimpleGraph (Fin n), erWeight n (d / n) Γ * ‖(zhat Γ q).eval t‖ ≤
      Real.exp (d / 2) * ∑ T ∈ Γ.edgeFinset.powerset, g (orient Γ T) := by
    intro Γ
    have hsum : ∑ T ∈ Γ.edgeFinset.powerset, g (orient Γ T) =
        Real.exp (-(d * n / 2)) * (d / n) ^ Γ.edgeFinset.card *
          (Real.exp (d * Γ.edgeFinset.card / n) * ‖(zhat Γ q).eval t‖) := by
      simp only [hg, rsc_poisPi_orient, rsc_rsEdges_orient, rsc_rsF_orient, Finset.sum_const,
        Finset.card_powerset, nsmul_eq_mul]
      rw [← Real.exp_nat_mul]
      have e1 : ((n * n : ℕ) : ℝ) * -(d / (2 * (n : ℝ))) = -(d * n / 2) := by
        push_cast; field_simp
      rw [e1]
      push_cast
      rw [div_pow, div_pow, mul_pow]
      field_simp
    rw [hsum]
    calc erWeight n (d / n) Γ * ‖(zhat Γ q).eval t‖
        ≤ (Real.exp (d / 2) * Real.exp (d * Γ.edgeFinset.card / n) *
            (Real.exp (-(d * n / 2)) * (d / n) ^ Γ.edgeFinset.card)) *
              ‖(zhat Γ q).eval t‖ :=
          mul_le_mul_of_nonneg_right (rsc_erWeight_le_pois hd.le hdn hn Γ) (norm_nonneg _)
      _ = _ := by ring
  calc erExp n (d / n) (fun G => ‖(zhat G q).eval t‖)
      = ∑ Γ, erWeight n (d / n) Γ * ‖(zhat Γ q).eval t‖ := rfl
    _ ≤ ∑ Γ, Real.exp (d / 2) * ∑ T ∈ Γ.edgeFinset.powerset, g (orient Γ T) :=
        Finset.sum_le_sum fun Γ _ => hΓ Γ
    _ = Real.exp (d / 2) * ∑ p ∈ P, g (orient p.1 p.2) := by
        rw [← Finset.mul_sum, Finset.sum_sigma]
    _ = Real.exp (d / 2) * ∑ N ∈ P.image (fun p => orient p.1 p.2), g N := by
        rw [Finset.sum_image hinj]
    _ ≤ Real.exp (d / 2) * ∑' N, g N := by
        gcongr
        exact hgs.sum_le_tsum _ (fun N _ => hg0 N)
    _ = _ := rfl

/-- Crude bound for the finitely many small `n`: `E_{G(n,p)} |Ẑ_G(t)| ≤ (1 + (q-1)T)^{C(n,2)}`
for `‖t‖ ≤ T`. -/
theorem rs_erExp_le_pow {q n : ℕ} (hq : 2 ≤ q) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {t : ℂ} {T : ℝ} (ht : ‖t‖ ≤ T) :
    erExp n p (fun G => ‖(zhat G q).eval t‖) ≤ (1 + ((q : ℝ) - 1) * T) ^ (n.choose 2) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hT : 0 ≤ T := (norm_nonneg t).trans ht
  have hK : 1 ≤ 1 + ((q : ℝ) - 1) * T := by nlinarith
  calc erExp n p (fun G => ‖(zhat G q).eval t‖)
      ≤ erExp n p (fun _ => (1 + ((q : ℝ) - 1) * T) ^ (n.choose 2)) := by
        refine erExp_mono hp0 hp1 fun G => ?_
        calc ‖(zhat G q).eval t‖ ≤ (1 + ((q : ℝ) - 1) * ‖t‖) ^ G.edgeFinset.card :=
              RSCompareAux.rsc_norm_zhat_eval_le hq G t
          _ ≤ (1 + ((q : ℝ) - 1) * T) ^ G.edgeFinset.card := by
              gcongr
              · nlinarith [norm_nonneg t]
              · linarith
          _ ≤ (1 + ((q : ℝ) - 1) * T) ^ (n.choose 2) := by
              refine pow_le_pow_right₀ hK ?_
              have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := G)
              simpa [Fintype.card_fin] using this
    _ = _ := erExp_const _


end

end ERZeroFreeness
