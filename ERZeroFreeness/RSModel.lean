/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSDefs
import ERZeroFreeness.TwoReplica

/-!
# Appendix C: deterministic facts about the multigraph model

Pointwise (non-probabilistic) facts about `t(x)`, `M_t`, the weights `w_{G,t}(σ)`, the partition
function `F_G` and the pair quantities `H`, `Y` at a real anchor, used by Lemmas C.3–C.7:

* `rs_tRe_*`: `t(x) ∈ [-1/(q-1), 0]` on `[0,1]`, monotone, `t(1) = 0`,
  `|t(x)| ≥ 1/(2q-1)` for `x ≤ 1/2`;
* `rs_rsA_cast_eq_aa`, `rs_edgeA_eq`, `rs_sum_rsA`, `rs_sum_rsM`: links with
  `TwoReplicaAux.aa` and `edgeA`, and the row sums `∑_b A_{ab} = 0`, `∑_b M_t(a,b) = q`;
* `rs_rsW_ofReal`, `rs_rsF_ofReal`, `rs_rsH_ofReal`: real anchors in the complex `t`-plane;
* `rs_rsM_mem`: for `q ≥ 3` the entries `x/b(x)`, `1/b(x)` of `M_x` lie in `[x, 3/2]`
  (`app:rs-bad`, first paragraph);
* `rs_rsF_bounds`: `x^m ≤ F_G(x) ≤ (3/2)^m`;
* `rs_edgeLip_log_rsF`: adding an edge changes `log F_G(x)` by at most `ℓ = log(e/x)`
  (`app:rs-bad`, first paragraph);
* `rs_rsHR_bounds`, `rs_rsY_bounds`: `H ∈ [0, F²]`, `Y ∈ [0, F]` (`app:rs-local`);
* `rs_rsW_add`: `w_{G+G'} = w_G w_{G'}` (superposition of edge sets).

## Proofs

`tRe`: `div_le_div_iff₀` and `nlinarith` (`x + q - 1 > 0`).  Entries: the diagonal entry of `M_x` is
`xq/(x+q-1) ∈ [x, 1]`, the off-diagonal one `q/(x+q-1) ∈ [1, q/(q-1)] ⊂ [1, 3/2]`.  Bounds on `F`:
each `w(σ)` is a product of `m` entries in `[x, 3/2]` (`Finset.prod_le_prod`,
`Finset.prod_pow_eq_pow_sum`), and `F` is their average.  Edge-Lipschitz: if `N' = N + δ_{(u,v)}`,
then `F(N') = q^{-n} ∑_σ w_N(σ) M_x(σ_u,σ_v) ∈ [x F(N), (3/2) F(N)]`, so
`|log F(N') - log F(N)| ≤ max(log(1/x), log(3/2)) ≤ 1 - log x = ℓ` (`log(3/2) < 1`).  `H`, `Y`:
`F² = q^{-2n} ∑_{σ,τ} w(σ)w(τ)` (`Finset.sum_mul_sum`), and the window sum is a sub-sum of
nonnegative terms.  `ofReal`: `push_cast` (`Complex.ofReal_prod`, `Complex.ofReal_intCast`,
`Complex.conj_ofReal`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-! ### The real parameter `t(x)` -/

theorem rs_tRe_nonpos {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    tRe q x ≤ 0 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

theorem rs_tRe_neg {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    tRe q x < 0 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

theorem rs_tRe_ge {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) :
    -1 / ((q : ℝ) - 1) ≤ tRe q x := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < x + q - 1 := by linarith
  unfold tRe
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem rs_tRe_mono {q : ℕ} (hq : 2 ≤ q) {x y : ℝ} (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    tRe q x ≤ tRe q y := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hx : 0 < x + q - 1 := by linarith
  have hy : 0 < y + q - 1 := by linarith
  unfold tRe
  rw [div_le_div_iff₀ hx hy]
  nlinarith

theorem rs_tRe_one (q : ℕ) : tRe q 1 = 0 := by
  simp [tRe]

/-- For `x ≤ 1/2`, `|t(x)| ≥ |t(1/2)| = 1/(2q-1)` (Lemma C.7, Step 4). -/
theorem rs_tRe_le_half {q : ℕ} (hq : 2 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    tRe q x ≤ -1 / (2 * (q : ℝ) - 1) := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (0 : ℝ) < 2 * (q : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < x + q - 1 := by linarith
  unfold tRe
  rw [div_le_div_iff₀ h2 h1]
  nlinarith

/-! ### The matrices `A` and `M_t` -/

theorem rs_rsA_cast_eq_aa (q : ℕ) (a b : Fin q) :
    ((rsA q a b : ℤ) : ℝ) = TwoReplicaAux.aa q a b := by
  unfold rsA TwoReplicaAux.aa
  split_ifs <;> push_cast <;> rfl

theorem rs_edgeA_eq {V : Type*} (q : ℕ) (σ : V → Fin q) (u v : V) :
    edgeA q σ s(u, v) = ((rsA q (σ u) (σ v) : ℤ) : ℂ) := by
  unfold edgeA rsA
  simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
  split_ifs <;> push_cast <;> rfl

/-- The rows of `A = q·Id - J` sum to zero. -/
theorem rs_sum_rsA (q : ℕ) (a : Fin q) : ∑ b, ((rsA q a b : ℤ) : ℝ) = 0 := by
  have h : ∀ b, ((rsA q a b : ℤ) : ℝ) = (q : ℝ) * (if a = b then 1 else 0) - 1 := by
    intro b; unfold rsA; split_ifs <;> push_cast <;> ring
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The rows of `M_t = J + tA` sum to `q`. -/
theorem rs_sum_rsM (q : ℕ) (t : ℝ) (a : Fin q) : ∑ b, rsM q t a b = q := by
  unfold rsM
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, rs_sum_rsA]
  simp

/-! ### Real anchors in the complex plane -/

theorem rs_rsW_ofReal {q n : ℕ} (t : ℝ) (N : RSGraph n) (σ : Fin n → Fin q) :
    rsW q (t : ℂ) N σ = ((rsW q t N σ : ℝ) : ℂ) := by
  unfold rsW rsM
  push_cast
  rfl

theorem rs_rsF_ofReal {q n : ℕ} (t : ℝ) (N : RSGraph n) :
    rsF q (t : ℂ) N = ((rsF q t N : ℝ) : ℂ) := by
  unfold rsF
  simp only [rs_rsW_ofReal]
  push_cast
  rfl

theorem rs_rsH_ofReal {q n : ℕ} (η t : ℝ) (N : RSGraph n) :
    rsH q η (t : ℂ) N = rsHR q η t N := by
  unfold rsH rsHR
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rs_rsW_ofReal, rs_rsW_ofReal, Complex.conj_ofReal, ← Complex.ofReal_mul,
    Complex.ofReal_re]

/-! ### Entries, weights and partition functions at a real anchor -/

/-- The entries of `M_x` lie in `[x, 3/2]` for `q ≥ 3` and `x ∈ [0,1]`. -/
theorem rs_rsM_mem {q : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (a b : Fin q) :
    x ≤ rsM q (tRe q x) a b ∧ rsM q (tRe q x) a b ≤ 3 / 2 := by
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hd : 0 < x + q - 1 := by linarith
  unfold rsM rsA tRe
  split_ifs with h
  · have key : 1 + (x - 1) / (x + q - 1) * ((((q : ℤ) - 1 : ℤ)) : ℝ) = x * q / (x + q - 1) := by
      push_cast
      field_simp
      ring
    rw [key, le_div_iff₀ hd, div_le_iff₀ hd]
    constructor <;> nlinarith
  · have key : 1 + (x - 1) / (x + q - 1) * (((-1 : ℤ)) : ℝ) = q / (x + q - 1) := by
      push_cast
      field_simp
      ring
    rw [key, le_div_iff₀ hd, div_le_iff₀ hd]
    constructor <;> nlinarith

/-- `x^m ≤ F_G(x) ≤ (3/2)^m`, `m = |E(G)|` (`q ≥ 3`, `x ∈ (0,1]`). -/
theorem rs_rsF_bounds {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (N : RSGraph n) :
    x ^ rsEdges N ≤ rsF q (tRe q x) N ∧ rsF q (tRe q x) N ≤ (3 / 2) ^ rsEdges N := by
  have hM := fun a b => rs_rsM_mem hq hx0.le hx1 a b
  have hw : ∀ σ : Fin n → Fin q, x ^ rsEdges N ≤ rsW q (tRe q x) N σ ∧
      rsW q (tRe q x) N σ ≤ (3 / 2) ^ rsEdges N := by
    intro σ
    unfold rsW rsEdges
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
    constructor
    · exact Finset.prod_le_prod (fun _ _ => by positivity)
        (fun uv _ => pow_le_pow_left₀ hx0.le (hM _ _).1 _)
    · exact Finset.prod_le_prod (fun _ _ => pow_nonneg (hx0.le.trans (hM _ _).1) _)
        (fun uv _ => pow_le_pow_left₀ (hx0.le.trans (hM _ _).1) (hM _ _).2 _)
  have hQ : (0 : ℝ) < (q : ℝ) ^ n := by
    have : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    positivity
  have hcard : ((Finset.univ : Finset (Fin n → Fin q)).card : ℝ) = (q : ℝ) ^ n := by simp
  unfold rsF
  constructor
  · rw [le_inv_mul_iff₀ hQ]
    calc (q : ℝ) ^ n * x ^ rsEdges N = ∑ _σ : Fin n → Fin q, x ^ rsEdges N := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ ≤ ∑ σ : Fin n → Fin q, rsW q (tRe q x) N σ := Finset.sum_le_sum fun σ _ => (hw σ).1
  · rw [inv_mul_le_iff₀ hQ]
    calc ∑ σ : Fin n → Fin q, rsW q (tRe q x) N σ ≤ ∑ _σ : Fin n → Fin q, (3 / 2 : ℝ) ^ rsEdges N :=
          Finset.sum_le_sum fun σ _ => (hw σ).2
      _ = (q : ℝ) ^ n * (3 / 2) ^ rsEdges N := by rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-- Adding one edge `i` (loops included) multiplies every weight by the entry
`M_t(σ_{i.1}, σ_{i.2})`: `w_{N'}(σ) = w_N(σ) · M_t(σ_u, σ_v)` when `N' = N + δ_{(u,v)}`. -/
private lemma rs_rsW_succ_edge {R : Type*} [CommRing R] (q : ℕ) {n : ℕ} (t : R)
    {N N' : RSGraph n} {i : Fin n × Fin n} (hN : ∀ j, j ≠ i → N' j = N j)
    (hi : N' i = N i + 1) (σ : Fin n → Fin q) :
    rsW q t N' σ = rsW q t N σ * rsM q t (σ i.1) (σ i.2) := by
  unfold rsW
  have h : ∀ uv : Fin n × Fin n, rsM q t (σ uv.1) (σ uv.2) ^ N' uv =
      rsM q t (σ uv.1) (σ uv.2) ^ N uv *
        (if uv = i then rsM q t (σ uv.1) (σ uv.2) else 1) := by
    intro uv
    by_cases huv : uv = i
    · subst huv
      rw [hi, pow_succ, if_pos rfl]
    · rw [hN uv huv, if_neg huv, mul_one]
  rw [Finset.prod_congr rfl fun uv _ => h uv, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    if_pos (Finset.mem_univ _)]

/-- Adding one edge multiplies `F_G(x)` by a factor in `[x, 3/2]` (a Gibbs average of entries of
`M_x`, `rs_rsM_mem`). -/
private lemma rs_rsF_succ_edge_bounds {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) {N N' : RSGraph n} {i : Fin n × Fin n} (hN : ∀ j, j ≠ i → N' j = N j)
    (hi : N' i = N i + 1) :
    x * rsF q (tRe q x) N ≤ rsF q (tRe q x) N' ∧
      rsF q (tRe q x) N' ≤ 3 / 2 * rsF q (tRe q x) N := by
  have hM := fun a b => rs_rsM_mem hq hx0.le hx1 a b
  have hw0 : ∀ σ : Fin n → Fin q, 0 ≤ rsW q (tRe q x) N σ := fun σ =>
    Finset.prod_nonneg fun uv _ => pow_nonneg (hx0.le.trans (hM _ _).1) _
  have hQ : (0 : ℝ) ≤ ((q : ℝ) ^ n)⁻¹ := by positivity
  have hS1 : x * ∑ σ, rsW q (tRe q x) N σ ≤
      ∑ σ, rsW q (tRe q x) N σ * rsM q (tRe q x) (σ i.1) (σ i.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ => by
      rw [mul_comm x]
      exact mul_le_mul_of_nonneg_left (hM _ _).1 (hw0 σ)
  have hS2 : ∑ σ, rsW q (tRe q x) N σ * rsM q (tRe q x) (σ i.1) (σ i.2) ≤
      3 / 2 * ∑ σ, rsW q (tRe q x) N σ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun σ _ => by
      rw [mul_comm (3 / 2 : ℝ)]
      exact mul_le_mul_of_nonneg_left (hM _ _).2 (hw0 σ)
  unfold rsF
  simp only [rs_rsW_succ_edge q (tRe q x) hN hi]
  constructor
  · calc x * (((q : ℝ) ^ n)⁻¹ * ∑ σ, rsW q (tRe q x) N σ)
        = ((q : ℝ) ^ n)⁻¹ * (x * ∑ σ, rsW q (tRe q x) N σ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hS1 hQ
  · calc ((q : ℝ) ^ n)⁻¹ * ∑ σ, rsW q (tRe q x) N σ * rsM q (tRe q x) (σ i.1) (σ i.2)
        ≤ ((q : ℝ) ^ n)⁻¹ * (3 / 2 * ∑ σ, rsW q (tRe q x) N σ) :=
          mul_le_mul_of_nonneg_left hS2 hQ
      _ = _ := by ring

/-- Adding one edge (loops included) changes `log F_G(x)` by at most `ℓ = log(e/x)`. -/
theorem rs_edgeLip_log_rsF {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    EdgeLip (rsEll x) (fun N : RSGraph n => Real.log (rsF q (tRe q x) N)) := by
  intro N N' i hN hi
  obtain ⟨hlo, hhi⟩ := rs_rsF_succ_edge_bounds hq hx0 hx1 hN hi
  have hFpos : 0 < rsF q (tRe q x) N :=
    lt_of_lt_of_le (pow_pos hx0 _) (rs_rsF_bounds hq hx0 hx1 N).1
  have hF'pos : 0 < rsF q (tRe q x) N' := lt_of_lt_of_le (mul_pos hx0 hFpos) hlo
  have hell : rsEll x = 1 - Real.log x := by
    unfold rsEll
    rw [Real.log_div (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
  have hlogx : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  have hlog32 : Real.log (3 / 2) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    linarith
  have h1 : Real.log x + Real.log (rsF q (tRe q x) N) ≤ Real.log (rsF q (tRe q x) N') := by
    rw [← Real.log_mul hx0.ne' hFpos.ne']
    exact Real.log_le_log (mul_pos hx0 hFpos) hlo
  have h2 : Real.log (rsF q (tRe q x) N') ≤
      Real.log (3 / 2) + Real.log (rsF q (tRe q x) N) := by
    rw [← Real.log_mul (by norm_num) hFpos.ne']
    exact Real.log_le_log hF'pos hhi
  show |Real.log (rsF q (tRe q x) N') - Real.log (rsF q (tRe q x) N)| ≤ rsEll x
  rw [hell, abs_le]
  constructor <;> linarith

/-- `0 ≤ H ≤ F²` at a real anchor `x ∈ [0,1]` (any window radius `η`). -/
theorem rs_rsHR_bounds {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (η : ℝ)
    (N : RSGraph n) :
    0 ≤ rsHR q η (tRe q x) N ∧ rsHR q η (tRe q x) N ≤ rsF q (tRe q x) N ^ 2 := by
  have hw0 : ∀ σ : Fin n → Fin q, 0 ≤ rsW q (tRe q x) N σ := fun σ =>
    Finset.prod_nonneg fun uv _ => pow_nonneg (hx0.trans (rs_rsM_mem hq hx0 hx1 _ _).1) _
  have hF2 : rsF q (tRe q x) N ^ 2 = (((q : ℝ) ^ n)⁻¹) ^ 2 *
      ∑ y : (Fin n → Fin q) × (Fin n → Fin q), rsW q (tRe q x) N y.1 * rsW q (tRe q x) N y.2 := by
    unfold rsF
    rw [Fintype.sum_prod_type, mul_pow, sq (∑ σ : Fin n → Fin q, rsW q (tRe q x) N σ),
      Finset.sum_mul_sum]
  unfold rsHR
  constructor
  · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun y _ => mul_nonneg (hw0 _) (hw0 _))
  · rw [hF2]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun y _ _ => mul_nonneg (hw0 _) (hw0 _))) (by positivity)

/-- `0 ≤ Y ≤ F` at a real anchor `x ∈ (0,1]`. -/
theorem rs_rsY_bounds {q n : ℕ} (hq : 3 ≤ q) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (η : ℝ)
    (N : RSGraph n) :
    0 ≤ rsY q η (tRe q x) N ∧ rsY q η (tRe q x) N ≤ rsF q (tRe q x) N := by
  have hF := (rs_rsF_bounds hq hx0 hx1 N).1
  have hFpos : 0 < rsF q (tRe q x) N := lt_of_lt_of_le (pow_pos hx0 _) hF
  have hH := rs_rsHR_bounds hq hx0.le hx1 η N
  unfold rsY
  constructor
  · exact div_nonneg (by linarith [hH.2]) hFpos.le
  · rw [div_le_iff₀ hFpos]
    nlinarith [hH.1]

/-- `w_{G+G',t} = w_{G,t} w_{G',t}`. -/
theorem rs_rsW_add {R : Type*} [CommRing R] (q : ℕ) {n : ℕ} (t : R) (N N' : RSGraph n)
    (σ : Fin n → Fin q) : rsW q t (N + N') σ = rsW q t N σ * rsW q t N' σ := by
  unfold rsW
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun uv _ => by rw [Pi.add_apply, pow_add]

end

end ERZeroFreeness
