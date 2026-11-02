/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.Defs
import ERZeroFreeness.ErdosRenyi

/-!
# The two-replica edge-weight bound (`lem:moment-bound`, Step 1)

For `q ≥ 2`, `d > 0` and `T ≥ 0` there is `C` such that for all `n ≥ d`, all `t` with
`|t| ≤ T`, `Re t ≤ T²` and any set `B` of colourings,
`E_G |q^{-n} ∑_{σ∈B} ∏_e (1 + tA_{σe})|² ≤ C q^{-2n} ∑_{σ,τ∈B} exp((dnT²/2)(q²∑R_ij² - 1))`,
where `G ~ G(n, d/n)` and `R = overlap σ τ` (`two_replica_bound`).

Proof.  `|z|² = z·conj z` and `A` is real, so the left side is
`q^{-2n} ∑_{σ,τ} E_G ∏_{e∈E(G)} y_e` with `y_e = (1+tA_{σe})(1+t̄A_{τe})`, and
`E_G ∏ y_e = ∏_{u<v} (1 + p(y_{uv}-1))` (`sum_erWeight_mul_prod`).  Use
`|1+ζ| ≤ exp(Re ζ + |ζ|²/2)`.  The quadratic terms sum to `O(1)` (`p = d/n`).  For the linear
terms, `∑_{u<v} = (∑_{u,v} - ∑_{u=v})/2`; the diagonal costs `O(1)`, and
`∑_{u,v} Re(y-1) = n²[Re t (X_α + X_β) + |t|² X_R]` with
`X_α = q∑α² - 1 ≥ 0`, `X_β = q∑β² - 1 ≥ 0`,
`X_R = q²∑R² - q∑α² - q∑β² + 1 = q² ∑(R_ij - α_i/q - β_j/q + 1/q²)² ≥ 0`;
bounding `Re t, |t|² ≤ T²` gives `≤ n² T² (q² ∑ R² - 1)`.

Implementation notes (the auxiliary lemmas are in the namespace `TwoReplicaAux`).
* `aa q x y = A_{xy}` is the real entry of `A`; `edgeA_eq_ofReal` and `aRe_mk` identify `edgeA`
  with it.  Nonnegativity of `n² X_α` and `n² X_R` is proved in Gram form
  (`sum_aa_nonneg`, `sum_aa_mul_nonneg`): `A_{ab} = q ∑_i (1_{a=i} - 1/q)(1_{b=i} - 1/q)`, so
  `∑_{u,v} A_{σ_uσ_v} A_{τ_uτ_v} = q² ∑_{i,j} (∑_u (1_{σ_u=i} - 1/q)(1_{τ_u=j} - 1/q))²`
  (the inner sum is `n(R_ij - α_i/q - β_j/q + 1/q²)`, so this is the identity above).
* `two_mul_sum_top_add`: `2 ∑_{e ∈ E(K_n)} r e + ∑_u r(uu) = ∑_{u,v} r(uv)`.
* With `M = 2T(q-1) + T²(q-1)² ≥ |y_e - 1|` (`Mc`), the constant is
  `C = exp(dM/2 + d²M²/2)`: the diagonal costs `≤ dM/2` and the quadratic terms `≤ d²M²/2`
  (using `|E(K_n)| ≤ n²`).
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

namespace TwoReplicaAux

/-- `‖1 + ζ‖ ≤ exp(Re ζ + ‖ζ‖²/2)`. -/
theorem norm_one_add_le_exp (ζ : ℂ) : ‖1 + ζ‖ ≤ Real.exp (ζ.re + ‖ζ‖ ^ 2 / 2) := by
  have h1 : ‖1 + ζ‖ ^ 2 = 1 + 2 * ζ.re + ‖ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im]
    ring
  have h2 : ‖1 + ζ‖ ^ 2 ≤ Real.exp (ζ.re + ‖ζ‖ ^ 2 / 2) ^ 2 := by
    rw [h1, sq (Real.exp _), ← Real.exp_add]
    have := Real.add_one_le_exp (2 * ζ.re + ‖ζ‖ ^ 2)
    have e : ζ.re + ‖ζ‖ ^ 2 / 2 + (ζ.re + ‖ζ‖ ^ 2 / 2) = 2 * ζ.re + ‖ζ‖ ^ 2 := by ring
    rw [e]; linarith
  exact (sq_le_sq₀ (norm_nonneg _) (Real.exp_pos _).le).1 h2

/-- Sums over the edges of the complete graph: `2 ∑_{u<v} + ∑_{u=v} = ∑_{u,v}`. -/
theorem two_mul_sum_top_add {n : ℕ} (r : Sym2 (Fin n) → ℝ) :
    2 * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, r e + ∑ u, r s(u, u) =
      ∑ u, ∑ v, r s(u, v) := by
  have h1 : (⊤ : SimpleGraph (Fin n)).edgeFinset =
      (Finset.univ : Finset (Fin n)).sym2.filter (fun e => ¬ e.IsDiag) := by
    ext e; simp
  have h2 : (Finset.univ : Finset (Fin n)).offDiag.filter (fun i => i.1 < i.2) =
      Finset.univ.filter (fun i : Fin n × Fin n => i.1 < i.2) := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨ne_of_lt h, h⟩
  rw [h1, Finset.sum_sym2_filter_not_isDiag, h2, Finset.sum_filter, Fintype.sum_prod_type]
  have h3 : ∀ u v : Fin n, r s(u, v) = (if u < v then r s(u, v) else 0) +
      (if v < u then r s(v, u) else 0) + (if u = v then r s(u, u) else 0) := by
    intro u v
    rcases lt_trichotomy u v with h | rfl | h
    · simp [h, h.ne, not_lt.2 h.le]
    · simp
    · simp [h, h.ne', not_lt.2 h.le, Sym2.eq_swap]
  calc 2 * ∑ u, ∑ v, (if u < v then r s(u, v) else 0) + ∑ u, r s(u, u)
      = ∑ u, ∑ v, ((if u < v then r s(u, v) else 0) +
          (if v < u then r s(v, u) else 0) + (if u = v then r s(u, u) else 0)) := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun u v => if v < u then r s(v, u) else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring
    _ = ∑ u, ∑ v, r s(u, v) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => (h3 u v).symm

/-- `∑_{u,v} ∑_k w_k(u) w_k(v) = ∑_k (∑_u w_k(u))²`. -/
theorem sum_sum_sum_mul_eq {ι κ : Type*} [Fintype ι] [Fintype κ] (w : κ → ι → ℝ) :
    ∑ u, ∑ v, ∑ k, w k u * w k v = ∑ k, (∑ u, w k u) ^ 2 := by
  calc ∑ u, ∑ v, ∑ k, w k u * w k v = ∑ u, ∑ k, ∑ v, w k u * w k v :=
        Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ k, ∑ u, ∑ v, w k u * w k v := Finset.sum_comm
    _ = ∑ k, (∑ u, w k u) ^ 2 := by simp_rw [sq, Finset.sum_mul_sum]

theorem gram_nonneg {ι κ : Type*} [Fintype ι] [Fintype κ] (w : κ → ι → ℝ) :
    0 ≤ ∑ u, ∑ v, ∑ k, w k u * w k v := by
  rw [sum_sum_sum_mul_eq]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

/-- The real entries of `A = qI - J`. -/
def aa (q : ℕ) (x y : Fin q) : ℝ := if x = y then (q : ℝ) - 1 else -1

theorem aa_eq_gram {q : ℕ} (hq : q ≠ 0) (x y : Fin q) :
    aa q x y = q * ∑ i, ((if x = i then (1 : ℝ) else 0) - 1 / q) *
      ((if y = i then (1 : ℝ) else 0) - 1 / q) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have e1 : ∀ i, ((if x = i then (1 : ℝ) else 0) - 1 / q) *
      ((if y = i then (1 : ℝ) else 0) - 1 / q) =
      (if x = i then (if y = i then (1 : ℝ) else 0) else 0) - 1 / q * (if x = i then (1 : ℝ) else 0)
        - 1 / q * (if y = i then (1 : ℝ) else 0) + 1 / q ^ 2 := by
    intro i
    split_ifs <;> ring
  simp_rw [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold aa
  by_cases h : x = y
  · subst h; simp; field_simp; ring
  · simp [h, Ne.symm h]; field_simp; ring

theorem sum_aa_nonneg {ι : Type*} [Fintype ι] {q : ℕ} (hq : q ≠ 0) (σ : ι → Fin q) :
    0 ≤ ∑ u, ∑ v, aa q (σ u) (σ v) := by
  simp_rw [aa_eq_gram hq, ← Finset.mul_sum]
  exact mul_nonneg (Nat.cast_nonneg _)
    (gram_nonneg (fun i u => (if σ u = i then (1 : ℝ) else 0) - 1 / q))

theorem sum_aa_mul_nonneg {ι : Type*} [Fintype ι] {q : ℕ} (hq : q ≠ 0) (σ τ : ι → Fin q) :
    0 ≤ ∑ u, ∑ v, aa q (σ u) (σ v) * aa q (τ u) (τ v) := by
  set g : Fin q → ι → ℝ := fun i u => (if σ u = i then (1 : ℝ) else 0) - 1 / q with hg
  set h : Fin q → ι → ℝ := fun j u => (if τ u = j then (1 : ℝ) else 0) - 1 / q with hh
  have key : ∀ u v, aa q (σ u) (σ v) * aa q (τ u) (τ v) =
      (q : ℝ) ^ 2 * ∑ k : Fin q × Fin q, (g k.1 u * h k.2 u) * (g k.1 v * h k.2 v) := by
    intro u v
    rw [aa_eq_gram hq, aa_eq_gram hq, Fintype.sum_prod_type, mul_mul_mul_comm,
      Finset.sum_mul_sum, sq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, hh]
    ring
  simp_rw [key, ← Finset.mul_sum]
  clear_value g h
  have hG := gram_nonneg (fun (k : Fin q × Fin q) u => g k.1 u * h k.2 u)
  exact mul_nonneg (sq_nonneg _) hG

theorem sum_sum_ite_eq_fiberCard {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (ρ : ι → κ) :
    ∑ u, ∑ v, (if ρ u = ρ v then (1 : ℝ) else 0) = ∑ c, ((fiberCard ρ c : ℕ) : ℝ) ^ 2 := by
  have e1 : ∀ u v, (if ρ u = ρ v then (1 : ℝ) else 0) =
      ∑ c, (if ρ u = c then (1 : ℝ) else 0) * (if ρ v = c then (1 : ℝ) else 0) := by
    intro u v
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [eq_comm]
  simp_rw [e1]
  rw [sum_sum_sum_mul_eq (fun c u => if ρ u = c then (1 : ℝ) else 0)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_boole]
  unfold fiberCard
  congr 2
  exact congrArg Finset.card
    (Finset.filter_congr_decidable (s := Finset.univ) (p := fun v => ρ v = c) _).symm

theorem sum_aa_total {ι : Type*} [Fintype ι] {q : ℕ} (σ τ : ι → Fin q) :
    ∑ u, ∑ v, (aa q (σ u) (σ v) + aa q (τ u) (τ v) + aa q (σ u) (σ v) * aa q (τ u) (τ v)) =
      (q : ℝ) ^ 2 * ∑ c, ((fiberCard (fun v => (σ v, τ v)) c : ℕ) : ℝ) ^ 2 -
        (Fintype.card ι : ℝ) ^ 2 := by
  have e1 : ∀ u v, aa q (σ u) (σ v) + aa q (τ u) (τ v) + aa q (σ u) (σ v) * aa q (τ u) (τ v) =
      (q : ℝ) ^ 2 * (if (σ u, τ u) = (σ v, τ v) then (1 : ℝ) else 0) - 1 := by
    intro u v
    unfold aa
    by_cases h1 : σ u = σ v <;> by_cases h2 : τ u = τ v <;> simp [h1, h2] <;> ring
  simp_rw [e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_sum_ite_eq_fiberCard (fun v => (σ v, τ v))]
  simp [sq]

/-- The real value of `edgeA`. -/
def aRe {V : Type*} (q : ℕ) (σ : V → Fin q) (e : Sym2 V) : ℝ :=
  if (e.map σ).IsDiag then (q : ℝ) - 1 else -1

theorem edgeA_eq_ofReal {V : Type*} (q : ℕ) (σ : V → Fin q) (e : Sym2 V) :
    edgeA q σ e = (aRe q σ e : ℂ) := by
  unfold edgeA aRe
  split_ifs <;> push_cast <;> rfl

theorem aRe_mk {V : Type*} (q : ℕ) (σ : V → Fin q) (u v : V) :
    aRe q σ s(u, v) = aa q (σ u) (σ v) := by
  simp [aRe, aa, Sym2.map_mk, Sym2.mk_isDiag_iff]

theorem abs_aRe_le {V : Type*} {q : ℕ} (hq : 2 ≤ q) (σ : V → Fin q) (e : Sym2 V) :
    |aRe q σ e| ≤ (q : ℝ) - 1 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  unfold aRe
  split_ifs
  · rw [abs_of_nonneg (by linarith)]
  · rw [abs_neg, abs_one]; linarith

theorem re_y_sub_one (t : ℂ) (a b : ℝ) :
    ((1 + t * a) * (starRingEnd ℂ) (1 + t * b) - 1).re =
      t.re * a + t.re * b + ‖t‖ ^ 2 * (a * b) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

theorem norm_y_sub_one_le (t : ℂ) (a b : ℝ) :
    ‖(1 + t * a) * (starRingEnd ℂ) (1 + t * b) - 1‖ ≤
      ‖t‖ * |a| + ‖t‖ * |b| + ‖t‖ ^ 2 * (|a| * |b|) := by
  have e : (1 + t * a) * (starRingEnd ℂ) (1 + t * b) - 1 =
      t * a + (starRingEnd ℂ) t * b + (t * (starRingEnd ℂ) t) * ((a : ℂ) * b) := by
    simp only [map_add, map_one, map_mul, Complex.conj_ofReal]
    ring
  rw [e]
  refine (norm_add₃_le).trans (le_of_eq ?_)
  simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- The constant `M = 2T(q-1) + T²(q-1)² = (1 + T(q-1))² - 1` bounding `|y_e - 1|`. -/
def Mc (q : ℕ) (T : ℝ) : ℝ := 2 * T * ((q : ℝ) - 1) + T ^ 2 * ((q : ℝ) - 1) ^ 2

theorem norm_y_le_Mc {V : Type*} {q : ℕ} (hq : 2 ≤ q) {T : ℝ} (hT : 0 ≤ T) {t : ℂ}
    (ht : ‖t‖ ≤ T) (σ τ : V → Fin q) (e : Sym2 V) :
    ‖(1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e) - 1‖ ≤ Mc q T := by
  have hq1 : (0 : ℝ) ≤ (q : ℝ) - 1 := by
    have : (2 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have ha := abs_aRe_le hq σ e
  have hb := abs_aRe_le hq τ e
  rw [edgeA_eq_ofReal, edgeA_eq_ofReal]
  refine (norm_y_sub_one_le _ _ _).trans ?_
  calc ‖t‖ * |aRe q σ e| + ‖t‖ * |aRe q τ e| + ‖t‖ ^ 2 * (|aRe q σ e| * |aRe q τ e|)
      ≤ T * ((q : ℝ) - 1) + T * ((q : ℝ) - 1) + T ^ 2 * (((q : ℝ) - 1) * ((q : ℝ) - 1)) := by
        gcongr
    _ = Mc q T := by unfold Mc; ring

/-- The linear term, summed over all ordered pairs of vertices. -/
theorem sum_re_le {q : ℕ} (hq : 2 ≤ q) {T : ℝ} {n : ℕ} (σ τ : Fin n → Fin q) {t : ℂ}
    (ht : ‖t‖ ≤ T) (htre : t.re ≤ T ^ 2) :
    ∑ u, ∑ v, ((1 + t * edgeA q σ s(u, v)) * (starRingEnd ℂ) (1 + t * edgeA q τ s(u, v)) - 1).re ≤
      T ^ 2 * ((q : ℝ) ^ 2 * ∑ c, ((fiberCard (fun v => (σ v, τ v)) c : ℕ) : ℝ) ^ 2 -
        (n : ℝ) ^ 2) := by
  have hq0 : q ≠ 0 := by omega
  have e : ∀ u v, ((1 + t * edgeA q σ s(u, v)) * (starRingEnd ℂ) (1 + t * edgeA q τ s(u, v))
      - 1).re = t.re * aa q (σ u) (σ v) + t.re * aa q (τ u) (τ v) +
        ‖t‖ ^ 2 * (aa q (σ u) (σ v) * aa q (τ u) (τ v)) := by
    intro u v
    rw [edgeA_eq_ofReal, edgeA_eq_ofReal, re_y_sub_one, aRe_mk, aRe_mk]
  simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_aa_nonneg hq0 σ
  have h2 := sum_aa_nonneg hq0 τ
  have h3 := sum_aa_mul_nonneg hq0 σ τ
  have htot := sum_aa_total σ τ
  simp only [Finset.sum_add_distrib, Fintype.card_fin] at htot
  have hnt : ‖t‖ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ht 2
  rw [← htot]
  calc t.re * ∑ u, ∑ v, aa q (σ u) (σ v) + t.re * ∑ u, ∑ v, aa q (τ u) (τ v) +
        ‖t‖ ^ 2 * ∑ u, ∑ v, aa q (σ u) (σ v) * aa q (τ u) (τ v)
      ≤ T ^ 2 * ∑ u, ∑ v, aa q (σ u) (σ v) + T ^ 2 * ∑ u, ∑ v, aa q (τ u) (τ v) +
        T ^ 2 * ∑ u, ∑ v, aa q (σ u) (σ v) * aa q (τ u) (τ v) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_right htre h1)
          (mul_le_mul_of_nonneg_right htre h2)) (mul_le_mul_of_nonneg_right hnt h3)
    _ = _ := by ring

theorem sum_overlap_sq {n q : ℕ} (σ τ : Fin n → Fin q) :
    ∑ i, ∑ j, overlap σ τ i j ^ 2 =
      (∑ c, ((fiberCard (fun v => (σ v, τ v)) c : ℕ) : ℝ) ^ 2) / (n : ℝ) ^ 2 := by
  unfold overlap
  rw [Fintype.sum_prod_type, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_pow]

/-- The quadratic term: `∑_{e ∈ K_n} ‖p(y_e - 1)‖²/2 ≤ d²M²/2`. -/
theorem sum_quad_le {n : ℕ} {d : ℝ} (hd : 0 < d) (hn : d ≤ n) {M : ℝ}
    (y : Sym2 (Fin n) → ℂ) (hM : ∀ e, ‖y e - 1‖ ≤ M) :
    ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, ‖((d / n : ℝ) : ℂ) * (y e - 1)‖ ^ 2 / 2 ≤
      d ^ 2 * M ^ 2 / 2 := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have hp : 0 ≤ d / n := div_nonneg hd.le hn0.le
  have hterm : ∀ e, ‖((d / n : ℝ) : ℂ) * (y e - 1)‖ ^ 2 / 2 ≤ (d / n) ^ 2 * M ^ 2 / 2 := by
    intro e
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp, mul_pow]
    gcongr
    exact hM e
  have hcard : ((⊤ : SimpleGraph (Fin n)).edgeFinset.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_fin]
    exact_mod_cast Nat.choose_le_pow n 2
  calc ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, ‖((d / n : ℝ) : ℂ) * (y e - 1)‖ ^ 2 / 2
      ≤ ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (d / n) ^ 2 * M ^ 2 / 2 :=
        Finset.sum_le_sum fun e _ => hterm e
    _ = ((⊤ : SimpleGraph (Fin n)).edgeFinset.card : ℝ) * ((d / n) ^ 2 * M ^ 2 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ 2 * ((d / n) ^ 2 * M ^ 2 / 2) := by gcongr
    _ = d ^ 2 * M ^ 2 / 2 := by field_simp

/-- **Per-pair bound.**  For fixed colourings `σ, τ`, the `G(n,d/n)`-average of
`∏_{e∈E(G)} (1+tA_{σe}) conj(1+tA_{τe})` has modulus at most
`exp(dM/2 + d²M²/2) · exp((dnT²/2)(q²∑R² - 1))`. -/
theorem pair_bound {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (hn : d ≤ n) (σ τ : Fin n → Fin q) {t : ℂ} (ht : ‖t‖ ≤ T) (htre : t.re ≤ T ^ 2) :
    ‖∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
        (algebraMap ℝ ℂ (1 - d / n) + algebraMap ℝ ℂ (d / n) *
          ((1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e)))‖ ≤
      Real.exp (d * Mc q T / 2 + d ^ 2 * Mc q T ^ 2 / 2) *
        Real.exp (d * n * T ^ 2 / 2 * ((q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1)) := by
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have hp : 0 ≤ d / n := div_nonneg hd.le hn0.le
  set y : Sym2 (Fin n) → ℂ :=
    fun e => (1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e) with hy
  have hfac : ∀ e, algebraMap ℝ ℂ (1 - d / n) + algebraMap ℝ ℂ (d / n) * y e =
      1 + ((d / n : ℝ) : ℂ) * (y e - 1) := by
    intro e
    simp only [Complex.coe_algebraMap]
    push_cast
    ring
  have hM : ∀ e, ‖y e - 1‖ ≤ Mc q T := fun e => norm_y_le_Mc hq hT ht σ τ e
  rw [Finset.prod_congr rfl (fun e _ => hfac e), norm_prod, ← Real.exp_add]
  refine (Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun e _ => norm_one_add_le_exp _)).trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.2 ?_
  rw [Finset.sum_add_distrib]
  have hquad := sum_quad_le hd hn y hM
  -- the linear term
  set r : Sym2 (Fin n) → ℝ := fun e => (y e - 1).re with hr
  have hlin1 : ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, (((d / n : ℝ) : ℂ) * (y e - 1)).re =
      d / n * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, r e := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Complex.re_ofReal_mul]
  have htop := two_mul_sum_top_add r
  have hsum := sum_re_le hq σ τ ht htre
  have hdiag : -∑ u, r s(u, u) ≤ n * Mc q T := by
    rw [← Finset.sum_neg_distrib]
    calc ∑ u, -r s(u, u) ≤ ∑ _u : Fin n, Mc q T :=
          Finset.sum_le_sum fun u _ => (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (hM _))
      _ = n * Mc q T := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hov := sum_overlap_sq σ τ
  set S := ∑ c, ((fiberCard (fun v => (σ v, τ v)) c : ℕ) : ℝ) ^ 2 with hS
  rw [hov]
  have hsum' : ∑ u, ∑ v, r s(u, v) ≤ T ^ 2 * ((q : ℝ) ^ 2 * S - (n : ℝ) ^ 2) := hsum
  have hlin : d / n * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, r e ≤
      d * Mc q T / 2 + d * n * T ^ 2 / 2 * ((q : ℝ) ^ 2 * (S / (n : ℝ) ^ 2) - 1) := by
    have h2 : ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, r e ≤
        (T ^ 2 * ((q : ℝ) ^ 2 * S - (n : ℝ) ^ 2) + n * Mc q T) / 2 := by linarith
    calc d / n * ∑ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset, r e
        ≤ d / n * ((T ^ 2 * ((q : ℝ) ^ 2 * S - (n : ℝ) ^ 2) + n * Mc q T) / 2) :=
          mul_le_mul_of_nonneg_left h2 hp
      _ = _ := by field_simp; ring
  rw [hlin1]
  linarith

/-- `z · conj z` for `z = c ∑_σ ∏_e f_σ(e)` with `c` real. -/
theorem mul_conj_sum_prod {ι α : Type*} (c : ℂ) (hc : (starRingEnd ℂ) c = c) (B : Finset ι)
    (K : Finset α) (f : ι → α → ℂ) :
    (c * ∑ σ ∈ B, ∏ e ∈ K, f σ e) * (starRingEnd ℂ) (c * ∑ σ ∈ B, ∏ e ∈ K, f σ e) =
      c ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B, ∏ e ∈ K, (f σ e * (starRingEnd ℂ) (f τ e)) := by
  rw [map_mul, hc, map_sum]
  rw [show (c * ∑ σ ∈ B, ∏ e ∈ K, f σ e) * (c * ∑ τ ∈ B, (starRingEnd ℂ) (∏ e ∈ K, f τ e)) =
      c ^ 2 * ((∑ σ ∈ B, ∏ e ∈ K, f σ e) * ∑ τ ∈ B, (starRingEnd ℂ) (∏ e ∈ K, f τ e)) by ring]
  rw [Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib]

theorem sum_mul_mul_sum_sum {α ι : Type*} (s : Finset α) (B : Finset ι) (w : α → ℂ) (c : ℂ)
    (X : α → ι → ι → ℂ) :
    ∑ G ∈ s, w G * (c * ∑ σ ∈ B, ∑ τ ∈ B, X G σ τ) =
      c * ∑ σ ∈ B, ∑ τ ∈ B, ∑ G ∈ s, w G * X G σ τ := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun G _ => ?_
  ring

end TwoReplicaAux

/-- **`lem:moment-bound`, Step 1.** For `n ≥ d`, `|t| ≤ T` and `Re t ≤ T²`, the
`G(n,d/n)`-average of `|q^{-n} ∑_{σ∈B} ∏_e (1 + tA_{σe})|²` is at most
`C q^{-2n} ∑_{σ,τ∈B} exp((dnT²/2)(q² ∑ R_ij² - 1))`, with `C` independent of `n`, `B` and `t`. -/
theorem two_replica_bound {q : ℕ} (hq : 2 ≤ q) {d : ℝ} (hd : 0 < d) {T : ℝ} (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ n : ℕ, d ≤ n → ∀ (B : Finset (Fin n → Fin q)) (t : ℂ), ‖t‖ ≤ T → t.re ≤ T ^ 2 →
      erExp n (d / n) (fun G =>
          ‖((q : ℂ) ^ n)⁻¹ * ∑ σ ∈ B, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ^ 2) ≤
        C * (((q : ℝ) ^ n)⁻¹) ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B,
          Real.exp (d * n * T ^ 2 / 2 *
            ((q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1)) := by
  refine ⟨Real.exp (d * TwoReplicaAux.Mc q T / 2 + d ^ 2 * TwoReplicaAux.Mc q T ^ 2 / 2),
    fun n hn B t ht htre => ?_⟩
  set c : ℂ := ((q : ℂ) ^ n)⁻¹ with hc
  have hcc : (starRingEnd ℂ) c = c := by simp [hc]
  have hcn : ‖c‖ = ((q : ℝ) ^ n)⁻¹ := by simp [hc]
  -- `|z|² = Re(z conj z)` and expansion of `z conj z` into a double sum over `σ, τ`.
  have hz : ∀ G : SimpleGraph (Fin n),
      ‖c * ∑ σ ∈ B, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ^ 2 =
        (c ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B, ∏ e ∈ G.edgeFinset,
          ((1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e))).re := by
    intro G
    rw [Complex.sq_norm, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
      TwoReplicaAux.mul_conj_sum_prod c hcc]
  -- averaging over `G` edge by edge
  have step1 : erExp n (d / n) (fun G =>
      ‖c * ∑ σ ∈ B, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ^ 2) =
        (c ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B, ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (algebraMap ℝ ℂ (1 - d / n) + algebraMap ℝ ℂ (d / n) *
            ((1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e)))).re := by
    have h1 : ∀ G : SimpleGraph (Fin n), erWeight n (d / n) G *
        ‖c * ∑ σ ∈ B, ∏ e ∈ G.edgeFinset, (1 + t * edgeA q σ e)‖ ^ 2 =
        ((erWeight n (d / n) G : ℂ) * (c ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B, ∏ e ∈ G.edgeFinset,
          ((1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e)))).re := by
      intro G
      rw [hz G, Complex.re_ofReal_mul]
    simp only [erExp]
    rw [Finset.sum_congr rfl (fun G _ => h1 G), ← Complex.re_sum,
      TwoReplicaAux.sum_mul_mul_sum_sum]
    congr 2
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    rw [← sum_erWeight_mul_prod]
    simp only [Complex.coe_algebraMap]
  rw [step1]
  calc _ ≤ ‖c ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B, ∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (algebraMap ℝ ℂ (1 - d / n) + algebraMap ℝ ℂ (d / n) *
            ((1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e)))‖ :=
        Complex.re_le_norm _
    _ ≤ ‖c‖ ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B, ‖∏ e ∈ (⊤ : SimpleGraph (Fin n)).edgeFinset,
          (algebraMap ℝ ℂ (1 - d / n) + algebraMap ℝ ℂ (d / n) *
            ((1 + t * edgeA q σ e) * (starRingEnd ℂ) (1 + t * edgeA q τ e)))‖ := by
        rw [norm_mul, norm_pow]
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => norm_sum_le _ _)
    _ ≤ ‖c‖ ^ 2 * ∑ σ ∈ B, ∑ τ ∈ B,
          Real.exp (d * TwoReplicaAux.Mc q T / 2 + d ^ 2 * TwoReplicaAux.Mc q T ^ 2 / 2) *
            Real.exp (d * n * T ^ 2 / 2 * ((q : ℝ) ^ 2 * ∑ i, ∑ j, overlap σ τ i j ^ 2 - 1)) := by
        gcongr with σ _ τ _
        exact TwoReplicaAux.pair_bound hq hd hT hn σ τ ht htre
    _ = _ := by
        rw [hcn]
        simp_rw [← Finset.mul_sum]
        ring

end

end ERZeroFreeness
