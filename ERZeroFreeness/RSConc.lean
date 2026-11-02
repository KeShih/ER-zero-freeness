/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSConcTensor

/-!
# Appendix C: conditional-Poisson concentration (Lemma C.6, `lem:rs-conc`)

Let `ξ = (ξ_1, …, ξ_n)` have independent coordinates `ξ_v ∼ p v` in a finite set `S`, and given `ξ`
let `G = (N_{uv})_{(u,v) ∈ [n]²}` have independent `Pois(K(ξ_u,ξ_v)/(2n))` counts, `0 ≤ K ≤ K₀`.  If
`|f(G+e) - f(G)| ≤ B` for every multigraph `G` and added edge `e` (loops included), then with
`c_f = E f(G)` and `C_⋆ = 1 + K₀ + K₀²`:

* `rs_cond_poisson_exp_le` (**`eq:rs-conc`, first bound**):
  `E e^{h(f(G) - c_f)} ≤ e^{C_⋆ h² B² n}` for `|h| ≤ 1/B`;
* `rs_cond_poisson_abs_le` (**`eq:rs-conc`, second bound**): `E|f(G) - c_f| ≤ 2 e^{C_⋆} B √n`;
* `rs_cond_poisson_exp_mul_le` and `rs_cond_poisson_tail_le`, both from the first bound: the
  un-centred exponential moment (used for `eq:rs-frac`) and the Chernoff tail (used in Lemma C.7,
  Step 5; via `1_{T ≤ y} ≤ e^{h(y - T)}` for `h ≥ 0`).

All expectations are `cpExp p K` (finite sum over labels, `tsum` over multigraphs).

## Proof

This is the paper's proof; the one-dimensional bounds are proved in `RSConcOneDim` and tensorized
in `RSConcTensor`.  Let `Φ(ξ) = E_{cpMean K ξ} f` (so `c_f = ∑_ξ P(ξ) Φ(ξ)`).  For fixed `ξ`, the
means `cpMean K ξ e ∈ [0, K₀/(2n)]` sum to at most `K₀ n/2`, so `rs_poisPiExp_exp_sub_le` bounds
`E[e^{h(f - Φ(ξ))} | ξ] ≤ e^{K₀ h² B² n}`.  Changing one label changes the means of the `2n-1`
pairs at that vertex by at most `K₀/(2n)` each, so `rs_abs_poisPiExp_sub_le` gives
`BddDiff (K₀ B) Φ`, and `rs_label_exp_sub_le` bounds `E e^{h(Φ(ξ) - c_f)} ≤ e^{K₀² h² B² n/2}`.
Factor `e^{h(f - c_f)} = e^{h(Φ - c_f)} e^{h(f - Φ)}` and multiply (`K₀ + K₀²/2 ≤ 1 + K₀ + K₀²`).
The second bound follows at `h = ±(B√n)^{-1}` from `|y| ≤ (e^{hy} + e^{-hy})/h` (`n ≥ 1`);
summability of every integrand comes from `rs_edgeLip_summable`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### Auxiliary lemmas: edge-mean bounds, the `cpExp` API, summability of the integrands -/

namespace RSConcAux

theorem cpMean_nonneg {n : ℕ} {S : Type*} {K : S → S → ℝ} (hK0 : ∀ a b, 0 ≤ K a b)
    (ξ : Fin n → S) (e : Fin n × Fin n) : 0 ≤ cpMean K ξ e :=
  div_nonneg (hK0 _ _) (by positivity)

/-- The total edge mean is at most `K₀ n / 2`. -/
theorem sum_cpMean_le {n : ℕ} {S : Type*} {K : S → S → ℝ} {K₀ : ℝ}
    (hK1 : ∀ a b, K a b ≤ K₀) (ξ : Fin n → S) :
    ∑ e, cpMean K ξ e ≤ K₀ * n / 2 := by
  unfold cpMean
  calc ∑ e : Fin n × Fin n, K (ξ e.1) (ξ e.2) / (2 * n)
      ≤ ∑ _e : Fin n × Fin n, K₀ / (2 * n) :=
        Finset.sum_le_sum fun e _ => div_le_div_of_nonneg_right (hK1 _ _) (by positivity)
    _ = K₀ * n / 2 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have : (n : ℝ) ≠ 0 := by positivity
        push_cast
        field_simp

/-- Changing one label moves the edge means by at most `K₀` in total. -/
theorem sum_abs_cpMean_sub_le {n : ℕ} {S : Type*} {K : S → S → ℝ} {K₀ : ℝ}
    (hK0 : ∀ a b, 0 ≤ K a b) (hK1 : ∀ a b, K a b ≤ K₀) {ξ ξ' : Fin n → S} {v : Fin n}
    (hξ : ∀ w, w ≠ v → ξ' w = ξ w) :
    ∑ e, |cpMean K ξ' e - cpMean K ξ e| ≤ K₀ := by
  have hn : (0 : ℝ) < n := by exact_mod_cast v.pos
  have hgen : ∀ e : Fin n × Fin n, |cpMean K ξ' e - cpMean K ξ e| ≤ K₀ / (2 * n) := by
    intro e
    unfold cpMean
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * n)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    rw [abs_sub_le_iff]
    constructor <;> linarith [hK0 (ξ' e.1) (ξ' e.2), hK1 (ξ' e.1) (ξ' e.2), hK0 (ξ e.1) (ξ e.2),
      hK1 (ξ e.1) (ξ e.2)]
  have hK₀ : 0 ≤ K₀ := (hK0 (ξ v) (ξ v)).trans (hK1 _ _)
  have hterm : ∀ e : Fin n × Fin n, |cpMean K ξ' e - cpMean K ξ e| ≤
      K₀ / (2 * n) * ((if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)) := by
    intro e
    have hq : 0 ≤ K₀ / (2 * n) := by positivity
    by_cases h1 : e.1 = v
    · have h2 : (0 : ℝ) ≤ if e.2 = v then 1 else 0 := by split_ifs <;> norm_num
      rw [if_pos h1]
      nlinarith [hgen e]
    by_cases h2 : e.2 = v
    · rw [if_neg h1, if_pos h2, zero_add, mul_one]
      exact hgen e
    · have : cpMean K ξ' e = cpMean K ξ e := by
        unfold cpMean
        rw [hξ _ h1, hξ _ h2]
      rw [this, sub_self, abs_zero, if_neg h1, if_neg h2]
      simp
  have hc1 : ∑ e : Fin n × Fin n, (if e.1 = v then (1 : ℝ) else 0) = n := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hc2 : ∑ e : Fin n × Fin n, (if e.2 = v then (1 : ℝ) else 0) = n := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  calc ∑ e, |cpMean K ξ' e - cpMean K ξ e|
      ≤ ∑ e : Fin n × Fin n,
          K₀ / (2 * n) * ((if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)) :=
        Finset.sum_le_sum fun e _ => hterm e
    _ = K₀ / (2 * n) * (∑ e : Fin n × Fin n, (if e.1 = v then (1 : ℝ) else 0) +
          ∑ e : Fin n × Fin n, (if e.2 = v then (1 : ℝ) else 0)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ = K₀ := by
        rw [hc1, hc2]
        field_simp
        ring

theorem cpExp_add {n : ℕ} {S : Type*} [Fintype S] {p : Fin n → S → ℝ} {K : S → S → ℝ}
    {F G : (Fin n → S) → RSGraph n → ℝ}
    (hF : ∀ ξ, Summable fun N => poisPi (cpMean K ξ) N * F ξ N)
    (hG : ∀ ξ, Summable fun N => poisPi (cpMean K ξ) N * G ξ N) :
    cpExp p K (fun ξ N => F ξ N + G ξ N) = cpExp p K F + cpExp p K G := by
  unfold cpExp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [rs_poisPiExp_add (hF ξ) (hG ξ), mul_add]

theorem cpExp_const_mul {n : ℕ} {S : Type*} [Fintype S] (p : Fin n → S → ℝ) (K : S → S → ℝ)
    (a : ℝ) (F : (Fin n → S) → RSGraph n → ℝ) :
    cpExp p K (fun ξ N => a * F ξ N) = a * cpExp p K F := by
  unfold cpExp
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [rs_poisPiExp_const_mul]
  ring

theorem summable_abs_sub {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) (c : ℝ) :
    Summable fun N => poisPi lam N * |f N - c| := by
  refine rs_edgeLip_summable hlam hf (φ := fun y => |y - c|) (A := 1 + |c|) (c := 1)
    fun y => ?_
  have h1 := Real.add_one_le_exp |y|
  have h2 := Real.one_le_exp (abs_nonneg y)
  rw [abs_abs, one_mul]
  calc |y - c| ≤ |y| + |c| := abs_sub _ _
    _ ≤ Real.exp |y| + |c| * Real.exp |y| := by nlinarith [abs_nonneg c]
    _ = (1 + |c|) * Real.exp |y| := by ring

theorem summable_mul_exp {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) (a h c : ℝ) :
    Summable fun N => poisPi lam N * (a * Real.exp (h * (f N - c))) := by
  refine rs_edgeLip_summable hlam hf (φ := fun y => a * Real.exp (h * (y - c)))
    (A := |a| * Real.exp (|h| * |c|)) (c := |h|) fun y => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg a)
  refine Real.exp_le_exp.mpr ?_
  calc h * (y - c) ≤ |h * (y - c)| := le_abs_self _
    _ = |h| * |y - c| := abs_mul _ _
    _ ≤ |h| * (|y| + |c|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
    _ = |h| * |c| + |h| * |y| := by ring

theorem summable_ind {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : ∀ i, 0 ≤ lam i)
    {B : ℝ} {f : (ι → ℕ) → ℝ} (hf : EdgeLip B f) (T c : ℝ) :
    Summable fun N => poisPi lam N * (if T ≤ f N - c then (1 : ℝ) else 0) := by
  refine rs_edgeLip_summable hlam hf (φ := fun y => if T ≤ y - c then (1 : ℝ) else 0)
    (A := 1) (c := 0) fun y => ?_
  rw [zero_mul, Real.exp_zero, one_mul]
  split_ifs <;> norm_num

end RSConcAux

/-- **Lemma C.6, `eq:rs-conc` (first bound).** -/
theorem rs_cond_poisson_exp_le {n : ℕ} {S : Type*} [Fintype S] {p : Fin n → S → ℝ}
    (hp0 : ∀ v a, 0 ≤ p v a) (hp1 : ∀ v, ∑ a, p v a = 1)
    {K : S → S → ℝ} {K₀ : ℝ} (hK0 : ∀ a b, 0 ≤ K a b) (hK1 : ∀ a b, K a b ≤ K₀)
    {B : ℝ} (hB : 0 < B) {f : RSGraph n → ℝ} (hf : EdgeLip B f)
    {h : ℝ} (hh : |h| ≤ 1 / B) :
    cpExp p K (fun _ N => Real.exp (h * (f N - cpExp p K (fun _ => f)))) ≤
      Real.exp ((1 + K₀ + K₀ ^ 2) * h ^ 2 * B ^ 2 * n) := by
  have hhB : |h| * B ≤ 1 := (le_div_iff₀ hB).mp hh
  have hm : ∀ ξ : Fin n → S, ∀ e, 0 ≤ cpMean K ξ e := fun ξ e => RSConcAux.cpMean_nonneg hK0 ξ e
  set Φ : (Fin n → S) → ℝ := fun ξ => poisPiExp (cpMean K ξ) f with hΦdef
  set c := cpExp p K (fun _ => f) with hc
  have hc' : c = ∑ ξ', (∏ v, p v (ξ' v)) * Φ ξ' := rfl
  -- the label average `Φ` has bounded differences `K₀ B`
  have hBD : BddDiff (K₀ * B) Φ := by
    intro ξ ξ' v hξ
    calc |Φ ξ' - Φ ξ| ≤ B * ∑ e, |cpMean K ξ' e - cpMean K ξ e| :=
          rs_abs_poisPiExp_sub_le (hm ξ') (hm ξ) hB.le hf
      _ ≤ B * K₀ := mul_le_mul_of_nonneg_left (RSConcAux.sum_abs_cpMean_sub_le hK0 hK1 hξ) hB.le
      _ = K₀ * B := mul_comm _ _
  have hlab := rs_label_exp_sub_le hp0 hp1 hBD h
  rw [← hc'] at hlab
  -- the edge counts given the labels
  have hin : ∀ ξ, poisPiExp (cpMean K ξ) (fun N => Real.exp (h * (f N - c))) ≤
      Real.exp (h * (Φ ξ - c)) * Real.exp (K₀ * h ^ 2 * B ^ 2 * n) := by
    intro ξ
    have e1 : (fun N => Real.exp (h * (f N - c))) =
        fun N => Real.exp (h * (Φ ξ - c)) * Real.exp (h * (f N - Φ ξ)) := by
      funext N
      rw [← Real.exp_add]
      ring_nf
    rw [e1, rs_poisPiExp_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    calc poisPiExp (cpMean K ξ) (fun N => Real.exp (h * (f N - Φ ξ)))
        ≤ Real.exp (2 * h ^ 2 * B ^ 2 * ∑ e, cpMean K ξ e) :=
          rs_poisPiExp_exp_sub_le (hm ξ) hB.le hf hhB
      _ ≤ Real.exp (K₀ * h ^ 2 * B ^ 2 * n) := by
        refine Real.exp_le_exp.mpr ?_
        have h2 : 0 ≤ 2 * h ^ 2 * B ^ 2 := by positivity
        calc 2 * h ^ 2 * B ^ 2 * ∑ e, cpMean K ξ e ≤ 2 * h ^ 2 * B ^ 2 * (K₀ * n / 2) :=
              mul_le_mul_of_nonneg_left (RSConcAux.sum_cpMean_le hK1 ξ) h2
          _ = K₀ * h ^ 2 * B ^ 2 * n := by ring
  calc cpExp p K (fun _ N => Real.exp (h * (f N - c)))
      = ∑ ξ, (∏ v, p v (ξ v)) * poisPiExp (cpMean K ξ) (fun N => Real.exp (h * (f N - c))) :=
        rfl
    _ ≤ ∑ ξ, (∏ v, p v (ξ v)) * (Real.exp (h * (Φ ξ - c)) * Real.exp (K₀ * h ^ 2 * B ^ 2 * n)) :=
        Finset.sum_le_sum fun ξ _ =>
          mul_le_mul_of_nonneg_left (hin ξ) (Finset.prod_nonneg fun v _ => hp0 v (ξ v))
    _ = (∑ ξ, (∏ v, p v (ξ v)) * Real.exp (h * (Φ ξ - c))) *
          Real.exp (K₀ * h ^ 2 * B ^ 2 * n) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun ξ _ => by ring
    _ ≤ Real.exp (n * h ^ 2 * (K₀ * B) ^ 2 / 2) * Real.exp (K₀ * h ^ 2 * B ^ 2 * n) :=
        mul_le_mul_of_nonneg_right hlab (Real.exp_pos _).le
    _ = Real.exp (n * h ^ 2 * (K₀ * B) ^ 2 / 2 + K₀ * h ^ 2 * B ^ 2 * n) :=
        (Real.exp_add _ _).symm
    _ ≤ Real.exp ((1 + K₀ + K₀ ^ 2) * h ^ 2 * B ^ 2 * n) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : 0 ≤ h ^ 2 * B ^ 2 * n := by positivity
        nlinarith [sq_nonneg K₀]

/-- **Lemma C.6, `eq:rs-conc` (second bound).** -/
theorem rs_cond_poisson_abs_le {n : ℕ} (hn : 0 < n) {S : Type*} [Fintype S]
    {p : Fin n → S → ℝ} (hp0 : ∀ v a, 0 ≤ p v a) (hp1 : ∀ v, ∑ a, p v a = 1)
    {K : S → S → ℝ} {K₀ : ℝ} (hK0 : ∀ a b, 0 ≤ K a b) (hK1 : ∀ a b, K a b ≤ K₀)
    {B : ℝ} (hB : 0 < B) {f : RSGraph n → ℝ} (hf : EdgeLip B f) :
    cpExp p K (fun _ N => |f N - cpExp p K (fun _ => f)|) ≤
      2 * Real.exp (1 + K₀ + K₀ ^ 2) * B * Real.sqrt n := by
  have hm : ∀ ξ : Fin n → S, ∀ e, 0 ≤ cpMean K ξ e := fun ξ e => RSConcAux.cpMean_nonneg hK0 ξ e
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
  have hsqpos : 0 < Real.sqrt n := by positivity
  have hBs : 0 < B * Real.sqrt n := by positivity
  set h₀ : ℝ := 1 / (B * Real.sqrt n) with hh₀
  have hh₀pos : 0 < h₀ := by positivity
  have hprod : B * Real.sqrt n * h₀ = 1 := by
    rw [hh₀]
    field_simp
  have hh₀le : |h₀| ≤ 1 / B := by
    rw [abs_of_pos hh₀pos, hh₀]
    exact one_div_le_one_div_of_le hB (by nlinarith)
  have hh₀le' : |-h₀| ≤ 1 / B := by rwa [abs_neg]
  have hkey : (1 + K₀ + K₀ ^ 2) * h₀ ^ 2 * B ^ 2 * n = 1 + K₀ + K₀ ^ 2 := by
    have : h₀ ^ 2 * B ^ 2 * n = 1 := by
      have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
      calc h₀ ^ 2 * B ^ 2 * n = h₀ ^ 2 * B ^ 2 * Real.sqrt n ^ 2 := by rw [hs2]
        _ = (B * Real.sqrt n * h₀) ^ 2 := by ring
        _ = 1 := by rw [hprod, one_pow]
    calc (1 + K₀ + K₀ ^ 2) * h₀ ^ 2 * B ^ 2 * n = (1 + K₀ + K₀ ^ 2) * (h₀ ^ 2 * B ^ 2 * n) := by
          ring
      _ = 1 + K₀ + K₀ ^ 2 := by rw [this, mul_one]
  have hkey' : (1 + K₀ + K₀ ^ 2) * (-h₀) ^ 2 * B ^ 2 * n = 1 + K₀ + K₀ ^ 2 := by
    rw [neg_sq]
    exact hkey
  have e1 := rs_cond_poisson_exp_le hp0 hp1 hK0 hK1 hB hf hh₀le
  have e2 := rs_cond_poisson_exp_le hp0 hp1 hK0 hK1 hB hf hh₀le'
  rw [hkey] at e1
  rw [hkey'] at e2
  set c := cpExp p K (fun _ => f) with hc
  have hpt : ∀ y : ℝ, |y| ≤ B * Real.sqrt n * Real.exp (h₀ * y) +
      B * Real.sqrt n * Real.exp (-h₀ * y) := by
    intro y
    have h1 : h₀ * |y| ≤ Real.exp (h₀ * y) + Real.exp (-h₀ * y) := by
      rcases le_total 0 y with hy | hy
      · rw [abs_of_nonneg hy]
        have := Real.add_one_le_exp (h₀ * y)
        have := Real.exp_pos (-h₀ * y)
        linarith
      · rw [abs_of_nonpos hy]
        have := Real.add_one_le_exp (-h₀ * y)
        have := Real.exp_pos (h₀ * y)
        have e : h₀ * -y = -h₀ * y := by ring
        linarith
    calc |y| = B * Real.sqrt n * (h₀ * |y|) := by rw [← mul_assoc, hprod, one_mul]
      _ ≤ B * Real.sqrt n * (Real.exp (h₀ * y) + Real.exp (-h₀ * y)) :=
          mul_le_mul_of_nonneg_left h1 hBs.le
      _ = _ := by ring
  have hs1 : ∀ ξ : Fin n → S, Summable fun N => poisPi (cpMean K ξ) N * |f N - c| :=
    fun ξ => RSConcAux.summable_abs_sub (hm ξ) hf c
  have hs2 : ∀ ξ : Fin n → S, Summable fun N =>
      poisPi (cpMean K ξ) N * (B * Real.sqrt n * Real.exp (h₀ * (f N - c))) :=
    fun ξ => RSConcAux.summable_mul_exp (hm ξ) hf _ _ _
  have hs3 : ∀ ξ : Fin n → S, Summable fun N =>
      poisPi (cpMean K ξ) N * (B * Real.sqrt n * Real.exp (-h₀ * (f N - c))) :=
    fun ξ => RSConcAux.summable_mul_exp (hm ξ) hf _ _ _
  have hs23 : ∀ ξ : Fin n → S, Summable fun N =>
      poisPi (cpMean K ξ) N * (B * Real.sqrt n * Real.exp (h₀ * (f N - c)) +
        B * Real.sqrt n * Real.exp (-h₀ * (f N - c))) := by
    intro ξ
    refine ((hs2 ξ).add (hs3 ξ)).congr fun N => ?_
    ring
  calc cpExp p K (fun _ N => |f N - c|)
      ≤ cpExp p K (fun _ N => B * Real.sqrt n * Real.exp (h₀ * (f N - c)) +
          B * Real.sqrt n * Real.exp (-h₀ * (f N - c))) :=
        rs_cpExp_mono hp0 hK0 hs1 hs23 fun _ N => hpt (f N - c)
    _ = cpExp p K (fun _ N => B * Real.sqrt n * Real.exp (h₀ * (f N - c))) +
          cpExp p K (fun _ N => B * Real.sqrt n * Real.exp (-h₀ * (f N - c))) :=
        RSConcAux.cpExp_add hs2 hs3
    _ = B * Real.sqrt n * cpExp p K (fun _ N => Real.exp (h₀ * (f N - c))) +
          B * Real.sqrt n * cpExp p K (fun _ N => Real.exp (-h₀ * (f N - c))) := by
        rw [RSConcAux.cpExp_const_mul p K (B * Real.sqrt n) (fun _ N => Real.exp (h₀ * (f N - c))),
          RSConcAux.cpExp_const_mul p K (B * Real.sqrt n) (fun _ N => Real.exp (-h₀ * (f N - c)))]
    _ ≤ B * Real.sqrt n * Real.exp (1 + K₀ + K₀ ^ 2) +
          B * Real.sqrt n * Real.exp (1 + K₀ + K₀ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hBs.le) (mul_le_mul_of_nonneg_left e2 hBs.le)
    _ = 2 * Real.exp (1 + K₀ + K₀ ^ 2) * B * Real.sqrt n := by ring

/-- Un-centred form of the first bound: `E e^{h f} ≤ e^{h c_f + C_⋆ h² B² n}` (`eq:rs-frac`). -/
theorem rs_cond_poisson_exp_mul_le {n : ℕ} {S : Type*} [Fintype S] {p : Fin n → S → ℝ}
    (hp0 : ∀ v a, 0 ≤ p v a) (hp1 : ∀ v, ∑ a, p v a = 1)
    {K : S → S → ℝ} {K₀ : ℝ} (hK0 : ∀ a b, 0 ≤ K a b) (hK1 : ∀ a b, K a b ≤ K₀)
    {B : ℝ} (hB : 0 < B) {f : RSGraph n → ℝ} (hf : EdgeLip B f)
    {h : ℝ} (hh : |h| ≤ 1 / B) :
    cpExp p K (fun _ N => Real.exp (h * f N)) ≤
      Real.exp (h * cpExp p K (fun _ => f) + (1 + K₀ + K₀ ^ 2) * h ^ 2 * B ^ 2 * n) := by
  have key := rs_cond_poisson_exp_le hp0 hp1 hK0 hK1 hB hf hh
  set c := cpExp p K (fun _ => f) with hc
  have e : (fun (_ : Fin n → S) (N : RSGraph n) => Real.exp (h * f N)) =
      fun _ N => Real.exp (h * c) * Real.exp (h * (f N - c)) := by
    funext _ N
    rw [← Real.exp_add]
    ring_nf
  rw [e]
  have hcm : cpExp p K (fun _ N => Real.exp (h * c) * Real.exp (h * (f N - c))) =
      Real.exp (h * c) * cpExp p K (fun _ N => Real.exp (h * (f N - c))) := by
    unfold cpExp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [rs_poisPiExp_const_mul]
    ring
  rw [hcm, Real.exp_add]
  exact mul_le_mul_of_nonneg_left key (Real.exp_pos _).le

/-- Chernoff tail: `Pr[f - c_f ≥ T] ≤ e^{-hT + C_⋆ h² B² n}` for `0 ≤ h ≤ 1/B`. -/
theorem rs_cond_poisson_tail_le {n : ℕ} {S : Type*} [Fintype S] {p : Fin n → S → ℝ}
    (hp0 : ∀ v a, 0 ≤ p v a) (hp1 : ∀ v, ∑ a, p v a = 1)
    {K : S → S → ℝ} {K₀ : ℝ} (hK0 : ∀ a b, 0 ≤ K a b) (hK1 : ∀ a b, K a b ≤ K₀)
    {B : ℝ} (hB : 0 < B) {f : RSGraph n → ℝ} (hf : EdgeLip B f)
    {h : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ 1 / B) (T : ℝ) :
    cpExp p K (fun _ N => if T ≤ f N - cpExp p K (fun _ => f) then 1 else 0) ≤
      Real.exp (-(h * T) + (1 + K₀ + K₀ ^ 2) * h ^ 2 * B ^ 2 * n) := by
  have hm : ∀ ξ : Fin n → S, ∀ e, 0 ≤ cpMean K ξ e := fun ξ e => RSConcAux.cpMean_nonneg hK0 ξ e
  have hh' : |h| ≤ 1 / B := by rwa [abs_of_nonneg hh0]
  have key := rs_cond_poisson_exp_le hp0 hp1 hK0 hK1 hB hf hh'
  set c := cpExp p K (fun _ => f) with hc
  have hpt : ∀ N : RSGraph n, (if T ≤ f N - c then (1 : ℝ) else 0) ≤
      Real.exp (-(h * T)) * Real.exp (h * (f N - c)) := by
    intro N
    rw [← Real.exp_add]
    split_ifs with hT
    · refine Real.one_le_exp ?_
      nlinarith
    · exact (Real.exp_pos _).le
  have hs1 : ∀ ξ : Fin n → S, Summable fun N =>
      poisPi (cpMean K ξ) N * (if T ≤ f N - c then (1 : ℝ) else 0) :=
    fun ξ => RSConcAux.summable_ind (hm ξ) hf T c
  have hs2 : ∀ ξ : Fin n → S, Summable fun N =>
      poisPi (cpMean K ξ) N * (Real.exp (-(h * T)) * Real.exp (h * (f N - c))) :=
    fun ξ => RSConcAux.summable_mul_exp (hm ξ) hf _ _ _
  calc cpExp p K (fun _ N => if T ≤ f N - c then 1 else 0)
      ≤ cpExp p K (fun _ N => Real.exp (-(h * T)) * Real.exp (h * (f N - c))) :=
        rs_cpExp_mono hp0 hK0 hs1 hs2 fun _ N => hpt N
    _ = Real.exp (-(h * T)) * cpExp p K (fun _ N => Real.exp (h * (f N - c))) :=
        RSConcAux.cpExp_const_mul p K _ (fun _ N => Real.exp (h * (f N - c)))
    _ ≤ Real.exp (-(h * T)) * Real.exp ((1 + K₀ + K₀ ^ 2) * h ^ 2 * B ^ 2 * n) :=
        mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
    _ = Real.exp (-(h * T) + (1 + K₀ + K₀ ^ 2) * h ^ 2 * B ^ 2 * n) := (Real.exp_add _ _).symm

end

end ERZeroFreeness
