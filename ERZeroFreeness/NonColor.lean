/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.ErdosRenyi

/-! # `G(n,d/n)` is not `q`-colourable for `d ≥ (2q-1) log q`

`noncolorable_whp`: for an integer `q ≥ 2` and `d ≥ d_nc(q) = (2q-1) log q`, with probability
tending to one `G_n ∼ G(n,d/n)` has no proper `q`-colouring, i.e. `Z_{G_n}(q,0) = 0`.  This is
the direction of [Achlioptas–Naor, Theorems 1 and 2] used in the proof of Corollary 1.4
(`cor_all_but_one`); it is proved here by a first-moment argument.

## Main results

* `pottsZ_zero_eq_zero_iff`: `Z_G(q,0) = 0` iff `G` has no proper `q`-colouring.
* `dnc_margin`: the first-moment threshold `2 log q / (-log(1-1/q))` lies strictly below
  `d_nc(q)`.
* `noncolorable_whp`: non-colourability with high probability for `d ≥ d_nc(q)`.

## Proof

`pottsZ_zero_eq_zero_iff`: `0 ^ m = if m = 0 then 1 else 0` (`zero_pow_eq`, so `0^0 = 1`), hence
`Z_G(q,0) = #{σ : monoCount G σ = 0}` (cast to `ℂ`).

`dnc_margin`: with `a = q - 1`, `Real.hasSum_log_one_add_inv` gives
`-log(1-1/q) = log(1 + a⁻¹) = ∑_{k ≥ 0} 2 (2k+1)⁻¹ (2q-1)^{-(2k+1)}`; the terms `k = 0, 1`
give `(2q-1) · (-log(1-1/q)) > 2`; multiply by `log q > 0`.

`noncolorable_whp`: put `L = -log(1-1/q)`, `w = e^L = q/(q-1)` and, for a colouring `σ`,
`y_e = w · 1{e not monochromatic under σ}`, so that `∏_{e ∈ E(G)} y_e = w^{|E(G)|}` if `σ` is
proper on `G` and `0` otherwise.  Then `y_e - 1 = -A_{σe}/(q-1)` with `A = q · 1{mono} - 1`,
and `∑_{e ∈ E(K_n)} A_{σe} ≥ -n(q-1)/2` (Cauchy–Schwarz for the colour-class sizes), so
`E ∏_{e ∈ E(G)} y_e = ∏_{e ∈ E(K_n)} (1 + p(y_e - 1)) ≤ e^{d/2}` for every `σ`, where `p = d/n`.
With `log q / L < c < d/2` (possible by `dnc_margin`) and `b = (d/2 - c)/(2c)`, the pointwise
bound `1{∃σ proper} ≤ e^{bcn} e^{-b|E(G)|} + e^{-Lcn} ∑_σ ∏_{e ∈ E(G)} y_e` and Markov's
inequality give
`Pr[Z_G(q,0) ≠ 0] ≤ e^{(bc - (d/2)(1-e^{-b})) n + (d/2)(1-e^{-b})} + e^{(log q - Lc) n + d/2}`
for `n ≥ d` (`NonColor_main_bound`); both exponents have negative slope.

## References

* D. Achlioptas and A. Naor, *The two possible values of the chromatic number of a random
  graph*, Ann. of Math. 162(3) (2005), 1335–1351.
-/

open Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- `Z_G(q,0)` vanishes iff `G` has no proper `q`-colouring (`Z_G(q,0)` counts proper
`q`-colourings, with `0^0 = 1`). -/
theorem pottsZ_zero_eq_zero_iff {V : Type*} [Fintype V] (G : SimpleGraph V) (q : ℕ) :
    pottsZ G q 0 = 0 ↔ ∀ σ : V → Fin q, monoCount G σ ≠ 0 := by
  have h : pottsZ G q 0 =
      (((Finset.univ : Finset (V → Fin q)).filter fun σ => monoCount G σ = 0).card : ℂ) := by
    unfold pottsZ
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [zero_pow_eq]
    split_ifs <;> simp
  rw [h, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  simp

/-- The strict margin behind `d_nc(q) = (2q-1) log q`: the first-moment threshold
`2 log q / (-log(1-1/q))` lies strictly below `(2q-1) log q`, for every `q ≥ 2`. -/
theorem dnc_margin {q : ℕ} (hq : 2 ≤ q) :
    2 * Real.log q < (2 * (q : ℝ) - 1) * Real.log q * (-Real.log (1 - 1 / (q : ℝ))) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have ha : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hs := Real.hasSum_log_one_add_inv ha
  have hid : Real.log (1 + ((q : ℝ) - 1)⁻¹) = -Real.log (1 - 1 / (q : ℝ)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
    ring
  rw [hid] at hs
  have hle := sum_le_hasSum (Finset.range 2) (fun k _ => by positivity) hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
    Nat.cast_one, mul_zero, mul_one] at hle
  set X := -Real.log (1 - 1 / (q : ℝ)) with hX
  have h2q : (0 : ℝ) < 2 * ((q : ℝ) - 1) + 1 := by linarith
  have hpos : (0 : ℝ) < 2 * (1 / (2 * 1 + 1)) * (1 / (2 * ((q : ℝ) - 1) + 1)) ^ (2 * 1 + 1) := by
    positivity
  have hX2 : 2 < (2 * (q : ℝ) - 1) * X := by
    have h1 : 2 * (1 / (2 * 0 + 1)) * (1 / (2 * ((q : ℝ) - 1) + 1)) ^ (2 * 0 + 1) < X := by
      simp only [mul_zero, zero_add, pow_one] at hle hpos ⊢
      linarith
    simp only [mul_zero, zero_add, pow_one, div_one, mul_one] at h1
    have h3 : 2 * (1 / (2 * ((q : ℝ) - 1) + 1)) * (2 * (q : ℝ) - 1) = 2 := by
      field_simp
      ring
    nlinarith
  nlinarith

/-! ### Helpers for `noncolorable_whp` -/

/-! #### Monochromatic pairs of `K_n` -/

/-- The real edge entry `A_{σ_u σ_v}` (`q - 1` on monochromatic pairs, `-1` otherwise). -/
private def NonColor_remA (q : ℕ) {V : Type*} (σ : V → Fin q) (e : Sym2 V) : ℝ :=
  if (e.map σ).IsDiag then (q : ℝ) - 1 else -1

private lemma NonColor_remA_mk {V : Type*} (q : ℕ) (σ : V → Fin q) (u v : V) :
    NonColor_remA q σ s(u, v) = (q : ℝ) * (if σ u = σ v then 1 else 0) - 1 := by
  unfold NonColor_remA
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
  split_ifs <;> ring

/-- Ordered pairs of distinct vertices cover each edge of the complete graph twice. -/
private lemma NonColor_sum_offDiag {V : Type*} [Fintype V] [DecidableEq V] (F : Sym2 V → ℝ) :
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
private lemma NonColor_sum_pairs {V : Type*} [Fintype V] [DecidableEq V] (F : Sym2 V → ℝ) :
    ∑ u : V, ∑ v : V, F s(u, v) =
      ∑ u : V, F s(u, u) + 2 * ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, F e := by
  rw [← NonColor_sum_offDiag, ← Fintype.sum_prod_type' (f := fun u v => F s(u, v)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : V × V => p.1 = p.2)]
  congr 1
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  simp

/-- `∑_{u,v} A_{σ_u σ_v} = q ∑_i N_i² - n² ≥ 0` (Cauchy–Schwarz). -/
private lemma NonColor_sum_sq_nonneg {V : Type*} [Fintype V] (q : ℕ) (σ : V → Fin q) :
    0 ≤ ∑ u : V, ∑ v : V, NonColor_remA q σ s(u, v) := by
  have hF : ∀ c : Fin q, fiberCard σ c = (Finset.univ.filter (fun v => σ v = c)).card := by
    intro c
    unfold fiberCard
    convert rfl
  have hN : ∀ c : Fin q, (fiberCard σ c : ℝ) = ∑ v ∈ Finset.univ.filter (fun v => σ v = c), 1 := by
    intro c
    rw [hF c, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h1 : ∑ u : V, ∑ v : V, NonColor_remA q σ s(u, v) =
      (q : ℝ) * ∑ c : Fin q, (fiberCard σ c : ℝ) ^ 2 - (Fintype.card V : ℝ) ^ 2 := by
    have hrow : ∀ u : V, ∑ v : V, NonColor_remA q σ s(u, v) =
        (q : ℝ) * (fiberCard σ (σ u) : ℝ) - Fintype.card V := by
      intro u
      simp only [NonColor_remA_mk]
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
private lemma NonColor_sum_edges_ge {V : Type*} [Fintype V] [DecidableEq V] (q : ℕ)
    (σ : V → Fin q) :
    -((Fintype.card V : ℝ) * ((q : ℝ) - 1)) / 2 ≤
      ∑ e ∈ (⊤ : SimpleGraph V).edgeFinset, NonColor_remA q σ e := by
  have h := NonColor_sum_pairs (fun e => NonColor_remA q σ e)
  have hdiag : ∑ u : V, NonColor_remA q σ s(u, u) = (Fintype.card V : ℝ) * ((q : ℝ) - 1) := by
    simp [NonColor_remA_mk]
    ring
  have := NonColor_sum_sq_nonneg q σ
  linarith

/-! #### `G(n,p)` averages of products of nonnegative edge weights -/

/-- `E_G ∏_{e ∈ E(G)} y_e = ∏_{e ∈ E(K_n)} (1 + p(y_e - 1)) ≤ exp(p ∑_e (y_e - 1))`. -/
private lemma NonColor_erExp_prod_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
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

private lemma NonColor_erExp_mul_sum {n : ℕ} {p : ℝ} {ι : Type*} (c : ℝ) (S : Finset ι)
    (f : ι → SimpleGraph (Fin n) → ℝ) :
    erExp n p (fun G => c * ∑ i ∈ S, f i G) = c * ∑ i ∈ S, erExp n p (f i) := by
  simp only [erExp, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun G _ => by ring

/-! #### The tilted proper-colouring weight -/

/-- The edge weight `y_e = w · [e not monochromatic under σ]`: for a graph `G`,
`∏_{e ∈ E(G)} y_e = w^{|E(G)|} · 1{σ proper on G}`. -/
private def NonColor_y {n q : ℕ} (σ : Fin n → Fin q) (w : ℝ) (e : Sym2 (Fin n)) : ℝ :=
  if (e.map σ).IsDiag then 0 else w

private lemma NonColor_y_nonneg {n q : ℕ} (σ : Fin n → Fin q) {w : ℝ} (hw : 0 ≤ w)
    (e : Sym2 (Fin n)) : 0 ≤ NonColor_y σ w e := by
  unfold NonColor_y
  split_ifs
  · exact le_rfl
  · exact hw

private lemma NonColor_prod_y_of_proper {n q : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Fin q)
    (w : ℝ) (h : monoCount G σ = 0) :
    ∏ e ∈ G.edgeFinset, NonColor_y σ w e = w ^ G.edgeFinset.card := by
  unfold monoCount at h
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
  rw [← Finset.prod_const]
  refine Finset.prod_congr rfl fun e he => ?_
  unfold NonColor_y
  rw [if_neg]
  exact h (SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.mem_edgeFinset.mp he))

/-- With `w = q/(q-1)`: `y_e - 1 = -A_{σe}/(q-1)`, so `∑_{e ∈ E(K_n)} (y_e - 1) ≤ n/2`. -/
private lemma NonColor_sum_y_le {n q : ℕ} (hq : 2 ≤ q) (σ : Fin n → Fin q) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
      (NonColor_y σ ((q : ℝ) / ((q : ℝ) - 1)) e - 1) ≤ (n : ℝ) / 2 := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hs := NonColor_sum_edges_ge q σ
  rw [Fintype.card_fin] at hs
  have hterm : ∀ e : Sym2 (Fin n), NonColor_y σ ((q : ℝ) / ((q : ℝ) - 1)) e - 1 =
      -NonColor_remA q σ e / ((q : ℝ) - 1) := by
    intro e
    unfold NonColor_y NonColor_remA
    split_ifs
    · rw [neg_div, div_self hq1.ne']
      ring
    · field_simp
      ring
  rw [Finset.sum_congr rfl fun e _ => hterm e, ← Finset.sum_div, Finset.sum_neg_distrib,
    div_le_iff₀ hq1]
  linarith

/-- `exp(α n + β) → 0` for `α < 0`. -/
private lemma NonColor_tendsto_exp {α : ℝ} (hα : α < 0) (β : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (α * n + β)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => α * (n : ℝ) + β) atTop atBot :=
    tendsto_atBot_add_const_right _ β (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hα)
  exact Real.tendsto_exp_atBot.comp h1

/-! #### The choice of constants -/

/-- The constants of the first-moment argument: with `L = -log(1-1/q)`, a level `c` with
`log q < L c` and `c < d/2`, and `b > 0` with `b c < (d/2)(1 - e^{-b})`. -/
private lemma NonColor_constants {q : ℕ} (hq : 2 ≤ q) {d : ℝ}
    (hd : (2 * (q : ℝ) - 1) * Real.log q ≤ d) :
    0 < d ∧ 0 < -Real.log (1 - 1 / (q : ℝ)) ∧
      ∃ c b : ℝ, 0 < c ∧ 0 < b ∧ Real.log q < -Real.log (1 - 1 / (q : ℝ)) * c ∧
        b * c < d / 2 * (1 - Real.exp (-b)) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  have hmargin := dnc_margin hq
  set L := -Real.log (1 - 1 / (q : ℝ)) with hL
  have hL0 : 0 < L := by
    have h1 : 0 < 1 - 1 / (q : ℝ) := by
      rw [sub_pos, div_lt_one hq0]
      linarith
    have h2 : 1 - 1 / (q : ℝ) < 1 := by
      have : 0 < 1 / (q : ℝ) := by positivity
      linarith
    have := Real.log_neg h1 h2
    linarith
  have hd0 : 0 < d := by
    have : 0 < (2 * (q : ℝ) - 1) * Real.log q := mul_pos (by linarith) hlogq
    linarith
  have hdL : 2 * Real.log q < d * L := by
    have := mul_le_mul_of_nonneg_right hd hL0.le
    linarith
  have hlq : Real.log q / L < d / 2 := by
    rw [div_lt_iff₀ hL0]
    linarith
  have hlq0 : 0 < Real.log q / L := div_pos hlogq hL0
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (Real.log q / L + d / 2) / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  have hc1 : Real.log q < L * c := by
    have h2 : Real.log q / L < c := by rw [hc]; linarith
    have := (div_lt_iff₀ hL0).mp h2
    linarith
  have hc2 : c < d / 2 := by rw [hc]; linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (d / 2 - c) / (2 * c) := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; exact div_pos (by linarith) (by linarith)
  have hexpb : b * c < d / 2 * (1 - Real.exp (-b)) := by
    have h1 : Real.exp (-b) ≤ 1 / (1 + b) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp b])
    have hcb : c * b = (d / 2 - c) / 2 := by
      rw [hb]
      field_simp
    have h3 : b * c < d / 2 * (b / (1 + b)) := by
      have h1b : 0 < 1 + b := by linarith
      have key : b * c * (1 + b) < d / 2 * b := by
        nlinarith [mul_pos hb0 (show (0 : ℝ) < d / 2 - c - c * b by linarith)]
      have he : d / 2 * (b / (1 + b)) = d / 2 * b / (1 + b) := by ring
      rw [he, lt_div_iff₀ h1b]
      exact key
    have h4 : 1 / (1 + b) = 1 - b / (1 + b) := by
      field_simp
      ring
    have h5 : b / (1 + b) ≤ 1 - Real.exp (-b) := by linarith
    calc b * c < d / 2 * (b / (1 + b)) := h3
      _ ≤ d / 2 * (1 - Real.exp (-b)) := mul_le_mul_of_nonneg_left h5 (by linarith)
  exact ⟨hd0, hL0, c, b, hc0, hb0, hc1, hexpb⟩

/-! #### The first-moment bound -/

/-- The pointwise bound: if `G` has a proper `q`-colouring `σ₀`, then either `|E(G)| < c n`
(and the lower-tail term is `≥ 1`) or `|E(G)| ≥ c n` (and the tilted term of `σ₀` is `≥ 1`). -/
private lemma NonColor_pointwise {n q : ℕ} {b c L : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L)
    (G : SimpleGraph (Fin n)) (hG : ¬ pottsZ G q 0 = 0) :
    1 ≤ Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) +
      Real.exp (-(L * c * n)) *
        ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e := by
  rw [pottsZ_zero_eq_zero_iff] at hG
  push Not at hG
  obtain ⟨σ₀, hσ₀⟩ := hG
  have hw0 : 0 ≤ Real.exp L := (Real.exp_pos L).le
  have hprod_u : ∏ _e ∈ G.edgeFinset, Real.exp (-b) =
      Real.exp ((G.edgeFinset.card : ℝ) * (-b)) := by
    rw [Finset.prod_const, Real.exp_nat_mul]
  have hprod_y : ∏ e ∈ G.edgeFinset, NonColor_y σ₀ (Real.exp L) e =
      Real.exp ((G.edgeFinset.card : ℝ) * L) := by
    rw [NonColor_prod_y_of_proper G σ₀ (Real.exp L) hσ₀, Real.exp_nat_mul]
  have hsum : ∏ e ∈ G.edgeFinset, NonColor_y σ₀ (Real.exp L) e ≤
      ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e :=
    Finset.single_le_sum (f := fun σ => ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e)
      (fun σ _ => Finset.prod_nonneg fun e _ => NonColor_y_nonneg σ hw0 e)
      (Finset.mem_univ σ₀)
  have ht1 : 0 ≤ Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) := by
    rw [hprod_u]
    positivity
  have ht2 : Real.exp (-(L * c * n)) * ∏ e ∈ G.edgeFinset, NonColor_y σ₀ (Real.exp L) e ≤
      Real.exp (-(L * c * n)) *
        ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e :=
    mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
  have ht3 : 0 ≤ Real.exp (-(L * c * n)) * ∏ e ∈ G.edgeFinset, NonColor_y σ₀ (Real.exp L) e := by
    rw [hprod_y]
    positivity
  by_cases hEc : (G.edgeFinset.card : ℝ) < c * n
  · have : 1 ≤ Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) := by
      rw [hprod_u, ← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    linarith
  · push Not at hEc
    have : 1 ≤ Real.exp (-(L * c * n)) * ∏ e ∈ G.edgeFinset, NonColor_y σ₀ (Real.exp L) e := by
      rw [hprod_y, ← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    linarith

/-- **The first-moment bound.**  For `n ≥ d`,
`Pr[Z_G(q,0) ≠ 0] ≤ e^{α₁ n + β₁} + e^{α₂ n + β₂}` with `α₁, α₂ < 0`: the first term bounds
`Pr[|E(G)| < c n]` (tilt `e^{-b|E|}`), the second `∑_σ Pr[σ proper, |E(G)| ≥ c n]`
(tilt `w^{|E|}`, `w = q/(q-1) = e^L`). -/
private lemma NonColor_main_bound {q : ℕ} (hq : 2 ≤ q) {d : ℝ}
    (hd : (2 * (q : ℝ) - 1) * Real.log q ≤ d) :
    ∃ α₁ β₁ α₂ β₂ : ℝ, α₁ < 0 ∧ α₂ < 0 ∧ ∀ n : ℕ, d ≤ n →
      erProb n (d / n) {G | pottsZ G q 0 = 0}ᶜ ≤
        Real.exp (α₁ * n + β₁) + Real.exp (α₂ * n + β₂) := by
  obtain ⟨hd0, hL0, c, b, hc0, hb0, hc1, hexpb⟩ := NonColor_constants hq hd
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  set L := -Real.log (1 - 1 / (q : ℝ)) with hL
  have hwL : Real.exp L = (q : ℝ) / ((q : ℝ) - 1) := by
    have h1 : 0 < 1 - 1 / (q : ℝ) := by
      rw [sub_pos, div_lt_one hq0]
      linarith
    rw [hL, Real.exp_neg, Real.exp_log h1]
    field_simp
  refine ⟨b * c - d / 2 * (1 - Real.exp (-b)), d / 2 * (1 - Real.exp (-b)),
    Real.log q - L * c, d / 2, by linarith, by linarith, fun n hn => ?_⟩
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le hd0 hn
  have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd0.le hn
  have hsub : {G : SimpleGraph (Fin n) | pottsZ G q 0 = 0}ᶜ ⊆
      {G | 1 ≤ Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) +
        Real.exp (-(L * c * n)) *
          ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e} :=
    fun G hG => NonColor_pointwise hb0.le hL0.le G hG
  have hf0 : ∀ G : SimpleGraph (Fin n),
      0 ≤ Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) +
        Real.exp (-(L * c * n)) *
          ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e := by
    intro G
    have h1 : 0 ≤ ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e :=
      Finset.sum_nonneg fun σ _ =>
        Finset.prod_nonneg fun e _ => NonColor_y_nonneg σ (Real.exp_pos L).le e
    exact add_nonneg
      (mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le))
      (mul_nonneg (Real.exp_pos _).le h1)
  have hE1 : erExp n (d / n) (fun G => ∏ _e ∈ G.edgeFinset, Real.exp (-b)) ≤
      Real.exp (d / n * ∑ _e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (Real.exp (-b) - 1)) :=
    NonColor_erExp_prod_le hp0 hp1 (fun _ => Real.exp (-b)) (fun _ => (Real.exp_pos _).le)
  have hE2 : ∀ σ : Fin n → Fin q,
      erExp n (d / n) (fun G => ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e) ≤
        Real.exp (d / 2) := by
    intro σ
    refine (NonColor_erExp_prod_le hp0 hp1 _
      (NonColor_y_nonneg σ (Real.exp_pos L).le)).trans ?_
    apply Real.exp_le_exp.mpr
    have h := NonColor_sum_y_le (n := n) hq σ
    rw [← hwL] at h
    calc d / n * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (NonColor_y σ (Real.exp L) e - 1)
        ≤ d / n * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_left h hp0
      _ = d / 2 := by field_simp
  have hN : ∑ _e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (Real.exp (-b) - 1) =
      (n : ℝ) * ((n : ℝ) - 1) / 2 * (Real.exp (-b) - 1) := by
    rw [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_edgeFinset_top_eq_card_choose_two,
      Fintype.card_fin, Nat.cast_choose_two]
  have hcard : ((Finset.univ : Finset (Fin n → Fin q)).card : ℝ) = (q : ℝ) ^ n := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
  have hqn : (q : ℝ) ^ n = Real.exp (n * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq0]
  have e1 : Real.exp (b * c * n) *
      Real.exp (d / n * ((n : ℝ) * ((n : ℝ) - 1) / 2 * (Real.exp (-b) - 1))) =
      Real.exp ((b * c - d / 2 * (1 - Real.exp (-b))) * n + d / 2 * (1 - Real.exp (-b))) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have e2 : Real.exp (-(L * c * n)) * ((q : ℝ) ^ n * Real.exp (d / 2)) =
      Real.exp ((Real.log q - L * c) * n + d / 2) := by
    rw [hqn, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc erProb n (d / n) {G : SimpleGraph (Fin n) | pottsZ G q 0 = 0}ᶜ
      ≤ erProb n (d / n) {G | 1 ≤ Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) +
          Real.exp (-(L * c * n)) *
            ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e} :=
        erProb_mono hp0 hp1 hsub
    _ ≤ erExp n (d / n) (fun G => Real.exp (b * c * n) * ∏ _e ∈ G.edgeFinset, Real.exp (-b) +
          Real.exp (-(L * c * n)) *
            ∑ σ : Fin n → Fin q, ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e) / 1 :=
        erProb_le_erExp_div hp0 hp1 hf0 one_pos
    _ = Real.exp (b * c * n) * erExp n (d / n) (fun G => ∏ _e ∈ G.edgeFinset, Real.exp (-b)) +
          Real.exp (-(L * c * n)) * ∑ σ : Fin n → Fin q,
            erExp n (d / n) (fun G => ∏ e ∈ G.edgeFinset, NonColor_y σ (Real.exp L) e) := by
        rw [div_one, erExp_add, erExp_const_mul, NonColor_erExp_mul_sum]
    _ ≤ Real.exp (b * c * n) *
          Real.exp (d / n * ∑ _e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (Real.exp (-b) - 1)) +
          Real.exp (-(L * c * n)) * ∑ _σ : Fin n → Fin q, Real.exp (d / 2) := by
        gcongr with σ _
        exact hE2 σ
    _ = Real.exp ((b * c - d / 2 * (1 - Real.exp (-b))) * n + d / 2 * (1 - Real.exp (-b))) +
          Real.exp ((Real.log q - L * c) * n + d / 2) := by
        rw [hN, Finset.sum_const, nsmul_eq_mul, hcard, e1, e2]

/-- **First-moment non-colourability** (the direction of [Achlioptas–Naor, Theorems 1 and 2] used
in the proof of Corollary 1.4 `cor:all-but-one`).  For an integer `q ≥ 2` and
`d ≥ d_nc(q) = (2q-1) log q`, with probability tending to one `G_n ∼ G(n,d/n)` has no proper
`q`-colouring, i.e. `Z_{G_n}(q,0) = 0`. -/
theorem noncolorable_whp {q : ℕ} (hq : 2 ≤ q) {d : ℝ}
    (hd : (2 * (q : ℝ) - 1) * Real.log q ≤ d) :
    Tendsto (fun n : ℕ => erProb n (d / n) {G | pottsZ G q 0 = 0}) atTop (𝓝 1) := by
  obtain ⟨α₁, β₁, α₂, β₂, h₁, h₂, hbound⟩ := NonColor_main_bound hq hd
  obtain ⟨hd0, -⟩ := NonColor_constants hq hd
  have hlim0 : Tendsto (fun n : ℕ => Real.exp (α₁ * n + β₁) + Real.exp (α₂ * n + β₂)) atTop
      (𝓝 0) := by
    simpa using (NonColor_tendsto_exp h₁ β₁).add (NonColor_tendsto_exp h₂ β₂)
  have hlim : Tendsto (fun n : ℕ => erProb n (d / n) {G | pottsZ G q 0 = 0}ᶜ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim0 ?_ ?_
    · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
      have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hn)
      obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd0.le hdn
      exact erProb_nonneg hp0 hp1 _
    · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
      exact hbound n ((Nat.le_ceil d).trans (by exact_mod_cast hn))
  have heq : (fun n : ℕ => erProb n (d / n) {G | pottsZ G q 0 = 0}) =
      fun n => 1 - erProb n (d / n) {G | pottsZ G q 0 = 0}ᶜ := by
    funext n
    rw [erProb_compl]
    ring
  rw [heq]
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hlim

end

end ERZeroFreeness
