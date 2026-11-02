/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi
import ERZeroFreeness.Multinomial

/-!
# The balancing remainder (Lemma 5.1, `lem:remainder`)

`remainder_bound`: for `q ≥ 3` and `δ > 0` there are `κ > 0` and `C` such that
`E|Ẑ_{G_n}(t) - Ẑ^B_{G_n}(t)| ≤ C e^{-(κ - 2d(q-1)ρ) n}` for `G_n ∼ G(n, d/n)`, all `ρ ≥ 0`,
`n ≥ d` and `t ∈ L_{4ρ}(I)`, `I = [-1/(q-1), 0]`.  The paper bounds the proportion of
unbalanced colourings by Hoeffding's inequality, with rate `2δ²` and the condition
`cond:remainder`; here the rate `κ` comes from the relative-entropy moment bound, and `ρ` is
later taken small relative to `κ` (`first_moment_bound`).

Proof.  Triangle inequality over colourings: the left side is at most
`q^{-n} ∑_{σ ∉ 𝓑} E_G ∏_{e ∈ E(G)} |1 + t A_{σe}|`.  By `sum_erWeight_mul_prod` with
`y_e = |1 + tA_{σe}| ≥ 0` and `1 + p(y - 1) ≤ e^{p(y-1)}`, this expectation is at most
`exp(p ∑_{u<v} (y_{uv} - 1))`; with `x ∈ I`, `|t - x| ≤ 4ρ`:
`y ≤ 1 + xA + 4(q-1)ρ` and `∑_{u<v} A_{σ_u σ_v} ≥ -n(q-1)/2`, so the expectation is
`≤ exp(d/2 + 2d(q-1)ρ n)`.  Unbalanced colourings: `empKL σ ≥ κ'`
(`exists_empKL_ge_of_not_balanced`), so by Markov and `exists_sum_exp_empKL_le` with
`θ = 1/2`, `q^{-n} #{σ ∉ 𝓑} ≤ C e^{-κ' n/2}`; thus `κ = κ'/2`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### The real edge matrix and the edge-factor bound on the tube -/

/-- The real edge entry `A_{σ_u σ_v}` (`q - 1` on monochromatic pairs, `-1` otherwise). -/
private def remA (q : ℕ) {V : Type*} (σ : V → Fin q) (e : Sym2 V) : ℝ :=
  if (e.map σ).IsDiag then (q : ℝ) - 1 else -1

private lemma remA_edgeA {V : Type*} (q : ℕ) (σ : V → Fin q) (e : Sym2 V) :
    edgeA q σ e = ((remA q σ e : ℝ) : ℂ) := by
  unfold edgeA remA
  split_ifs <;> simp

private lemma remA_mk {V : Type*} (q : ℕ) (σ : V → Fin q) (u v : V) :
    remA q σ s(u, v) = (q : ℝ) * (if σ u = σ v then 1 else 0) - 1 := by
  unfold remA
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
  split_ifs <;> ring

/-- On the tube, `|1 + tA| ≤ 1 + xA + (q-1)r`. -/
private lemma rem_norm_factor_le {q : ℕ} (hq : 2 ≤ q) {V : Type*} (σ : V → Fin q) (e : Sym2 V)
    {x r : ℝ} (hx : x ∈ Set.Icc (-(1 / ((q : ℝ) - 1))) 0) {t : ℂ} (ht : ‖t - x‖ ≤ r) :
    ‖1 + t * edgeA q σ e‖ ≤ 1 + x * remA q σ e + ((q : ℝ) - 1) * r := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) - 1 := by linarith
  obtain ⟨hx0, hx1⟩ := hx
  have hxq : -1 ≤ x * ((q : ℝ) - 1) := by
    have h := mul_le_mul_of_nonneg_right hx0 hpos.le
    rwa [neg_mul, one_div, inv_mul_cancel₀ hpos.ne'] at h
  have hA : 0 ≤ 1 + x * remA q σ e ∧ |remA q σ e| ≤ (q : ℝ) - 1 := by
    unfold remA
    split_ifs
    · exact ⟨by linarith, by rw [abs_of_pos hpos]⟩
    · exact ⟨by linarith, by rw [abs_neg, abs_one]; linarith⟩
  have hdecomp : 1 + t * edgeA q σ e =
      ((1 + x * remA q σ e : ℝ) : ℂ) + (t - x) * (remA q σ e : ℂ) := by
    rw [remA_edgeA]; push_cast; ring
  rw [hdecomp]
  calc ‖((1 + x * remA q σ e : ℝ) : ℂ) + (t - x) * (remA q σ e : ℂ)‖
      ≤ ‖((1 + x * remA q σ e : ℝ) : ℂ)‖ + ‖(t - x) * (remA q σ e : ℂ)‖ := norm_add_le _ _
    _ = (1 + x * remA q σ e) + ‖t - x‖ * |remA q σ e| := by
        rw [Complex.norm_real, Real.norm_of_nonneg hA.1, norm_mul, Complex.norm_real,
          Real.norm_eq_abs]
    _ ≤ (1 + x * remA q σ e) + r * ((q : ℝ) - 1) := by
        have := mul_le_mul ht hA.2 (abs_nonneg _) ((norm_nonneg _).trans ht)
        linarith
    _ = _ := by ring

/-! ### Summing the edge matrix over the complete graph -/

/-- Ordered pairs of distinct vertices cover each edge of the complete graph twice. -/
private lemma rem_sum_offDiag {V : Type*} [Fintype V] [DecidableEq V] (F : Sym2 V → ℝ) :
    ∑ p ∈ (Finset.univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2), F s(p.1, p.2) =
      2 * ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, F e := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2))
    (t := (⊤ : SimpleGraph V).edgeFinset) (g := fun p => s(p.1, p.2))]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by simpa using he
      have hfib : ((Finset.univ : Finset (V × V)).filter (fun p => p.1 ≠ p.2)).filter
          (fun p => s(p.1, p.2) = s(a, b)) = {(a, b), (b, a)} := by
        ext ⟨x, y⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro ⟨_, h⟩
          rcases Sym2.eq_iff.mp h with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact ⟨hab, rfl⟩
          · exact ⟨hab.symm, Sym2.eq_swap⟩
      rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2], hfib,
        Finset.sum_pair (by simp [hab])]
      ring
  · intro p hp
    simpa using (Finset.mem_filter.mp hp).2

/-- `∑_{u,v} F(uv) = ∑_u F(uu) + 2 ∑_{e ∈ E(K_V)} F(e)`. -/
private lemma rem_sum_pairs {V : Type*} [Fintype V] [DecidableEq V] (F : Sym2 V → ℝ) :
    ∑ u : V, ∑ v : V, F s(u, v) =
      ∑ u : V, F s(u, u) + 2 * ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, F e := by
  rw [← rem_sum_offDiag, ← Fintype.sum_prod_type' (f := fun u v => F s(u, v)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : V × V => p.1 = p.2)]
  congr 1
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

/-- `∑_{u,v} A_{σ_u σ_v} = q ∑_i N_i² - n² ≥ 0` (Cauchy–Schwarz). -/
private lemma rem_sum_sq_nonneg {V : Type*} [Fintype V] (q : ℕ) (σ : V → Fin q) :
    0 ≤ ∑ u : V, ∑ v : V, remA q σ s(u, v) := by
  have hF : ∀ c : Fin q, fiberCard σ c = (Finset.univ.filter (fun v => σ v = c)).card := by
    intro c
    unfold fiberCard
    convert rfl
  have hN : ∀ c : Fin q, (fiberCard σ c : ℝ) = ∑ v ∈ Finset.univ.filter (fun v => σ v = c), 1 := by
    intro c
    rw [hF c, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : ∑ u : V, ∑ v : V, remA q σ s(u, v) =
      (q : ℝ) * ∑ c : Fin q, (fiberCard σ c : ℝ) ^ 2 - (Fintype.card V : ℝ) ^ 2 := by
    have hrow : ∀ u : V, ∑ v : V, remA q σ s(u, v) =
        (q : ℝ) * (fiberCard σ (σ u) : ℝ) - Fintype.card V := by
      intro u
      simp only [remA_mk]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, hF (σ u)]
      simp [eq_comm]
    simp only [hrow]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have hsq : ∑ u : V, (fiberCard σ (σ u) : ℝ) = ∑ c : Fin q, (fiberCard σ c : ℝ) ^ 2 := by
      rw [← Finset.sum_fiberwise Finset.univ σ (fun u => (fiberCard σ (σ u) : ℝ))]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_congr rfl fun u hu => by rw [(Finset.mem_filter.mp hu).2]]
      rw [Finset.sum_const, nsmul_eq_mul, sq, hF c]
    rw [hsq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq]
  have h2 : ∑ c : Fin q, (fiberCard σ c : ℝ) = Fintype.card V := by
    simp only [hN]
    rw [Finset.sum_fiberwise Finset.univ σ (fun _ => (1 : ℝ))]
    simp
  have h3 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q)))
    (f := fun c : Fin q => (fiberCard σ c : ℝ))
  rw [h2, Finset.card_univ, Fintype.card_fin] at h3
  rw [h1]
  linarith

/-- `∑_{e ∈ E(K_n)} A_{σ e} ≥ -n(q-1)/2`. -/
private lemma rem_sum_edges_ge {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ) (σ : V → Fin q) :
    -((Fintype.card V : ℝ) * ((q : ℝ) - 1)) / 2 ≤
      ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, remA q σ e := by
  have h := rem_sum_pairs (fun e => remA q σ e)
  have hdiag : ∑ u : V, remA q σ s(u, u) = (Fintype.card V : ℝ) * ((q : ℝ) - 1) := by
    simp [remA_mk]
    ring
  have := rem_sum_sq_nonneg q σ
  linarith

/-! ### The `G(n,p)` average of a product of nonnegative edge weights -/

/-- `E_G ∏_{e ∈ E(G)} y_e = ∏_{e ∈ E(K_n)} (1 + p(y_e - 1)) ≤ exp(p ∑_e (y_e - 1))`. -/
private lemma rem_erExp_prod_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : Sym2 (Fin n) → ℝ) (hy : ∀ e, 0 ≤ y e) :
    erExp n p (fun G => ∏ e ∈ G.edgeFinset, y e) ≤
      Real.exp (p * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (y e - 1)) := by
  have h := sum_erWeight_mul_prod (R := ℝ) (n := n) (p := p) y
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at h
  unfold erExp
  rw [h, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun e _ => ?_) (fun e _ => ?_)
  · exact add_nonneg (by linarith) (mul_nonneg hp0 (hy e))
  · have := Real.add_one_le_exp (p * (y e - 1))
    linarith

private lemma rem_erExp_mul_sum {n : ℕ} {p : ℝ} {ι : Type*} (c : ℝ) (S : Finset ι)
    (f : ι → SimpleGraph (Fin n) → ℝ) :
    erExp n p (fun G => c * ∑ i ∈ S, f i G) = c * ∑ i ∈ S, erExp n p (f i) := by
  simp only [erExp, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun G _ => by ring

/-! ### Few unbalanced colourings -/

/-- `#{σ ∉ 𝓑_n} ≤ C q^n e^{-κ n}`. -/
private lemma rem_card_unbalanced {q : ℕ} (hq : 2 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ > 0, ∃ C : ℝ, ∀ n : ℕ, 0 < n →
      ((Finset.univ \ balanced q n δ).card : ℝ) ≤ C * (q : ℝ) ^ n * Real.exp (-κ * n) := by
  obtain ⟨κ', hκ', hbal⟩ := exists_empKL_ge_of_not_balanced hq hδ
  obtain ⟨C, hC⟩ := exists_sum_exp_empKL_le (θ := 1 / 2) (by norm_num) (by norm_num) q
  refine ⟨κ' / 2, by positivity, C, fun n hn => ?_⟩
  have hsum := hC (Fin n) (Fin q) (Fintype.card_fin q)
  rw [Fintype.card_fin] at hsum
  have hsum' : ∑ f : Fin n → Fin q, Real.exp (1 / 2 * (n : ℝ) * empKL f) ≤ C * (q : ℝ) ^ n :=
    by convert hsum using 3
  have hlow : ((Finset.univ \ balanced q n δ).card : ℝ) * Real.exp (κ' / 2 * n) ≤
      ∑ f : Fin n → Fin q, Real.exp (1 / 2 * (n : ℝ) * empKL f) := by
    calc ((Finset.univ \ balanced q n δ).card : ℝ) * Real.exp (κ' / 2 * n)
        = ∑ σ ∈ Finset.univ \ balanced q n δ, Real.exp (κ' / 2 * n) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ σ ∈ Finset.univ \ balanced q n δ, Real.exp (1 / 2 * (n : ℝ) * empKL σ) := by
          refine Finset.sum_le_sum fun σ hσ => ?_
          have h := hbal n hn σ (Finset.mem_sdiff.mp hσ).2
          apply Real.exp_le_exp.mpr
          have hn' : (0 : ℝ) ≤ n := by positivity
          nlinarith
      _ ≤ ∑ f : Fin n → Fin q, Real.exp (1 / 2 * (n : ℝ) * empKL f) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => (Real.exp_pos _).le)
  have hexp : Real.exp (κ' / 2 * n) * Real.exp (-(κ' / 2) * n) = 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    congr 1
    ring
  calc ((Finset.univ \ balanced q n δ).card : ℝ)
      = ((Finset.univ \ balanced q n δ).card : ℝ) * Real.exp (κ' / 2 * n) *
          Real.exp (-(κ' / 2) * n) := by rw [mul_assoc, hexp, mul_one]
    _ ≤ C * (q : ℝ) ^ n * Real.exp (-(κ' / 2) * n) :=
        mul_le_mul_of_nonneg_right (hlow.trans hsum') (Real.exp_pos _).le

/-! ### The remainder bound -/

/-- **Lemma 5.1 (`lem:remainder`)**, with the rate `κ` of the relative-entropy bound in place of
Hoeffding's `2δ²`: `E|Ẑ_{G_n}(t) - Ẑ^B_{G_n}(t)| ≤ C e^{-(κ - 2d(q-1)ρ) n}` on `L_{4ρ}(I)`. -/
theorem remainder_bound {q : ℕ} (hq : 3 ≤ q) {d : ℝ} (hd : 0 < d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ > 0, ∃ C : ℝ, ∀ ρ : ℝ, 0 ≤ ρ → ∀ n : ℕ, d ≤ n →
      ∀ t ∈ tube (1 / ((q : ℝ) - 1)) (4 * ρ),
        erExp n (d / n) (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖) ≤
          C * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) := by
  obtain ⟨κ, hκ, C, hcount⟩ := rem_card_unbalanced (q := q) (by omega) hδ
  refine ⟨κ, hκ, C * Real.exp (d / 2), fun ρ hρ n hn t ht => ?_⟩
  obtain ⟨x, hx, hxt⟩ := ht
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have hn0 : 0 < n := by exact_mod_cast hnR
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  set S := Finset.univ \ balanced q n δ with hS
  -- pointwise bound by the unbalanced colourings
  have hpt : ∀ G : SimpleGraph (Fin n), ‖(zhat G q).eval t - zhatB G q δ t‖ ≤
      ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ S, ∏ e ∈ G.edgeFinset, ‖1 + t * edgeA q σ e‖ := by
    intro G
    have hdiff : (zhat G q).eval t - zhatB G q δ t =
        ((q : ℂ) ^ n)⁻¹ * ∑ σ ∈ S, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e) := by
      have hsplit : ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e) =
          ∑ σ ∈ S, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e) +
            ∑ σ ∈ balanced q n δ, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e) :=
        (Finset.sum_sdiff (Finset.subset_univ (balanced q n δ))).symm
      rw [zhat_eval, zhatB, Fintype.card_fin, ← mul_sub]
      congr 1
      rw [sub_eq_iff_eq_add]
      convert hsplit using 3
    rw [hdiff, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    gcongr
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun σ _ => norm_prod _ _
  -- expected weight of a fixed colouring
  have hσ : ∀ σ : Fin n → Fin q,
      erExp n (d / n) (fun G => ∏ e ∈ G.edgeFinset, ‖1 + t * edgeA q σ e‖) ≤
        Real.exp (d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n) := by
    intro σ
    refine (rem_erExp_prod_le hp0 hp1 _ (fun e => norm_nonneg _)).trans ?_
    apply Real.exp_le_exp.mpr
    have h1 : ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (‖1 + t * edgeA q σ e‖ - 1) ≤
        ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (x * remA q σ e + ((q : ℝ) - 1) * (4 * ρ)) := by
      refine Finset.sum_le_sum fun e _ => ?_
      have := rem_norm_factor_le (by omega) σ e hx hxt
      linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin,
      Nat.cast_choose_two] at h1
    have h2 : x * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, remA q σ e ≤ (n : ℝ) / 2 := by
      have hs := rem_sum_edges_ge q σ
      rw [Fintype.card_fin] at hs
      obtain ⟨hx0, hx1⟩ := hx
      have hpos : 0 < (q : ℝ) - 1 := by linarith
      have hxq : -1 ≤ x * ((q : ℝ) - 1) := by
        have h := mul_le_mul_of_nonneg_right hx0 hpos.le
        rwa [neg_mul, one_div, inv_mul_cancel₀ hpos.ne'] at h
      nlinarith [mul_nonneg (neg_nonneg.mpr hx1)
        (by linarith : 0 ≤ ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, remA q σ e +
          (n : ℝ) * ((q : ℝ) - 1) / 2),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + x * ((q : ℝ) - 1)) hnR.le]
    have hρ' : 0 ≤ ((q : ℝ) - 1) * (4 * ρ) := by
      have : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
      positivity
    calc d / n * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (‖1 + t * edgeA q σ e‖ - 1)
        ≤ d / n * ((n : ℝ) / 2 + (n : ℝ) * ((n : ℝ) - 1) / 2 * (((q : ℝ) - 1) * (4 * ρ))) := by
          apply mul_le_mul_of_nonneg_left _ hp0
          linarith
      _ = d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * ((n : ℝ) - 1) := by
          field_simp
          ring
      _ ≤ d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n := by
          have : 0 ≤ 2 * d * ((q : ℝ) - 1) * ρ := by
            have : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith
            positivity
          nlinarith
  have hqn : ((q : ℝ) ^ n) ≠ 0 := by positivity
  have he : Real.exp (-κ * n) * Real.exp (d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n) =
      Real.exp (d / 2) * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc erExp n (d / n) (fun G => ‖(zhat G q).eval t - zhatB G q δ t‖)
      ≤ erExp n (d / n)
          (fun G => ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ S, ∏ e ∈ G.edgeFinset, ‖1 + t * edgeA q σ e‖) :=
        erExp_mono hp0 hp1 hpt
    _ = ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ S,
          erExp n (d / n) (fun G => ∏ e ∈ G.edgeFinset, ‖1 + t * edgeA q σ e‖) :=
        rem_erExp_mul_sum _ _ (fun σ G => ∏ e ∈ G.edgeFinset, ‖1 + t * edgeA q σ e‖)
    _ ≤ ((q : ℝ) ^ n)⁻¹ * ∑ σ ∈ S, Real.exp (d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n) := by
        gcongr with σ _
        exact hσ σ
    _ = ((q : ℝ) ^ n)⁻¹ * ((S.card : ℝ) * Real.exp (d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((q : ℝ) ^ n)⁻¹ * ((C * (q : ℝ) ^ n * Real.exp (-κ * n)) *
          Real.exp (d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n)) := by
        gcongr
        exact hcount n hn0
    _ = (((q : ℝ) ^ n)⁻¹ * (q : ℝ) ^ n) * C *
          (Real.exp (-κ * n) * Real.exp (d / 2 + 2 * d * ((q : ℝ) - 1) * ρ * n)) := by ring
    _ = C * Real.exp (d / 2) * Real.exp (-(κ - 2 * d * ((q : ℝ) - 1) * ρ) * n) := by
        rw [inv_mul_cancel₀ hqn, he]
        ring

end

end ERZeroFreeness
