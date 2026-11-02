/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.RSPoisPi

/-!
# Appendix C: the Poisson multigraph as a Poisson number of uniform edges

The bridge between the ordered Poisson multigraph `𝖯_s` and CKPZ's null model (used in the proof of
Lemma C.3, "the null model [CKPZ, Definition 2.5] is `𝖯_s`, with partition function `q^n F`"):
under `𝖯_s` the number of edges is `m ∼ Pois(sn/2)`, and given `m` the multigraph is the edge-count
vector of `m` i.i.d. uniform ordered pairs of `[n]²`.

* `rs_rsF_edgeCount`: `F` of the multigraph with edge list `e` is the `m`-edge partition function,
  `F(count(e)) = rsSeqF e`;
* `rs_poisson_split`: `E_{𝖯_s} Φ = ∑_m Pois(sn/2)(m) · n^{-2m} ∑_{e ∈ ([n]²)^m} Φ(count(e))`,
  together with summability, for every `Φ` whose absolute values satisfy the same summability.

## Proof

Write `C = [n]²` for the set of ordered pairs and `count(e)_c = #{j : e_j = c}`.

1. `∑_c count(e)_c = m` (`Finset.card_eq_sum_card_fiberwise`).
2. Multinomial fibre count: `#{e : Fin m → C | count(e) = N} = multinomial(N)` if `∑_c N_c = m`,
   and `0` otherwise.  Proof: in the additive monoid algebra `ℝ[C → ℕ]` with `x_c = single δ_c 1`,
   `(∑_c x_c)^m = ∑_e single(count e) 1` (`Finset.sum_pow'`, `AddMonoidAlgebra.prod_single`) and
   `(∑_c x_c)^m = ∑_{N ∈ piAntidiag univ m} single N multinomial(N)` (the multinomial theorem
   `Finset.sum_pow_eq_sum_piAntidiag`); compare the coefficients of `N`.
3. For `∑_c N_c = m`: `𝖯_s(N) = Pois(sn/2)(m) · n^{-2m} · m!/∏_c N_c!` (`Finset.prod_mul_distrib`,
   `Finset.prod_pow_eq_pow_sum`, `|C| = n²`, `n² · s/(2n) = sn/2`, `Nat.multinomial_spec`; the case
   `n = 0` is included, with `s/(2·0) = 0`).
4. Hence `∑_{N ∈ piAntidiag univ m} 𝖯_s(N) Φ(N) = Pois(sn/2)(m) n^{-2m} ∑_e Φ(count e)`
   (`Finset.sum_fiberwise_of_maps_to`, `Finset.mem_piAntidiag`).
5. Regroup the `tsum` over `N` by `m = ∑_c N_c` (`Equiv.sigmaFiberEquiv`, each fibre being the
   finite set `piAntidiag univ m`): `summable_sigma_of_nonneg` for `|Φ|` gives summability, and
   `HasSum.sigma` the value.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

/-- `F` of the multigraph with edge list `e` is the `m`-edge partition function `rsSeqF`. -/
theorem rs_rsF_edgeCount {q n m : ℕ} (t : ℝ) (e : Fin m → Fin n × Fin n) :
    rsF q t (rsEdgeCount e) = rsSeqF q t e := by
  unfold rsF rsSeqF rsW rsEdgeCount
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := e)
    (fun j _ => Finset.mem_univ _) (fun j => rsM q t (σ (e j).1) (σ (e j).2))]
  refine Finset.prod_congr rfl fun uv _ => ?_
  rw [Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.prod_const]

namespace RSPoisSplitAux

/-- `∑_c count(e)_c = m`. -/
lemma sum_edgeCount {n m : ℕ} (e : Fin m → Fin n × Fin n) : ∑ c, rsEdgeCount e c = m := by
  unfold rsEdgeCount
  rw [← Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (e j))]
  simp

lemma edgeCount_mem_piAntidiag {n m : ℕ} (e : Fin m → Fin n × Fin n) :
    rsEdgeCount e ∈ Finset.piAntidiag Finset.univ m := by
  rw [Finset.mem_piAntidiag]
  exact ⟨sum_edgeCount e, fun _ _ => Finset.mem_univ _⟩

/-- In `ℝ[C → ℕ]`: `(∑_c x_c)^m = ∑_{e : Fin m → C} single(count e) 1`, `x_c = single δ_c 1`. -/
lemma pow_sum_single {n m : ℕ} :
    (∑ c : Fin n × Fin n,
        AddMonoidAlgebra.single (Pi.single c 1 : Fin n × Fin n → ℕ) (1 : ℝ)) ^ m =
      ∑ e : Fin m → Fin n × Fin n, AddMonoidAlgebra.single (rsEdgeCount e) (1 : ℝ) := by
  rw [Finset.sum_pow', Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [AddMonoidAlgebra.prod_single]
  congr 1
  · funext c
    simp only [rsEdgeCount, Finset.sum_apply, Pi.single_apply, Finset.sum_boole, Nat.cast_id]
    exact congrArg Finset.card (Finset.filter_congr fun j _ => eq_comm)
  · simp

/-- The multinomial theorem in `ℝ[C → ℕ]`:
`(∑_c x_c)^m = ∑_{N ∈ piAntidiag univ m} single N multinomial(N)`. -/
lemma pow_sum_single' {n m : ℕ} :
    (∑ c : Fin n × Fin n,
        AddMonoidAlgebra.single (Pi.single c 1 : Fin n × Fin n → ℕ) (1 : ℝ)) ^ m =
      ∑ k ∈ Finset.piAntidiag Finset.univ m,
        AddMonoidAlgebra.single k (Nat.multinomial Finset.univ k : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.prod_single,
    Finset.prod_const_one]
  rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_mul_single, zero_add, mul_one]
  congr 1
  funext c
  simp [Finset.sum_apply, Pi.single_apply]

/-- **Multinomial fibre count.** `#{e : Fin m → C | count(e) = N} = multinomial(N)` if
`∑_c N_c = m`, and `0` otherwise. -/
lemma card_fiber_edgeCount {n : ℕ} (m : ℕ) (N : Fin n × Fin n → ℕ) :
    (((Finset.univ.filter fun e : Fin m → Fin n × Fin n => rsEdgeCount e = N).card : ℕ) : ℝ) =
      if N ∈ Finset.piAntidiag Finset.univ m then (Nat.multinomial Finset.univ N : ℝ) else 0 := by
  have h := congrArg (fun y => y.coeff N)
    ((pow_sum_single (n := n) (m := m)).symm.trans (pow_sum_single' (m := m)))
  simp only [AddMonoidAlgebra.coeff_sum, AddMonoidAlgebra.coeff_single, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.single_apply] at h
  rw [Finset.sum_boole] at h
  rw [h, Finset.sum_ite_eq']

/-- For `∑_c N_c = m`: `𝖯_s(N) = Pois(sn/2)(m) · n^{-2m} · multinomial(N)`. -/
lemma poisPi_rsMean_eq {n m : ℕ} (s : ℝ) (N : Fin n × Fin n → ℕ)
    (hN : N ∈ Finset.piAntidiag Finset.univ m) :
    poisPi (rsMean n s) N =
      poisPMF (s * n / 2) m * (((n : ℝ) ^ (2 * m))⁻¹ * (Nat.multinomial Finset.univ N : ℝ)) := by
  rw [Finset.mem_piAntidiag] at hN
  have hsum : ∑ c, N c = m := hN.1
  have hspec := Nat.multinomial_spec Finset.univ N
  rw [hsum] at hspec
  have hspecR : (∏ c, ((N c).factorial : ℝ)) * (Nat.multinomial Finset.univ N : ℝ) =
      (m.factorial : ℝ) := by
    exact_mod_cast hspec
  have hmult_pos : (0:ℝ) < Nat.multinomial Finset.univ N := by
    exact_mod_cast Nat.multinomial_pos _ _
  unfold poisPi poisPMF rsMean
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_pow_eq_pow_sum, hsum, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  rw [← hspecR]
  have hexp : Real.exp (-(s / (2 * n))) ^ (n * n) = Real.exp (-(s * n / 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n:ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
  have hpow : (s / (2 * n)) ^ m = (s * n / 2) ^ m * ((n : ℝ) ^ (2 * m))⁻¹ := by
    rw [pow_mul, ← inv_pow, ← mul_pow]
    congr 1
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n:ℝ) ≠ 0 := by positivity
      field_simp
  rw [hexp, hpow]
  field_simp

/-- The `m`-edge slice: `∑_{∑ N = m} 𝖯_s(N) Φ(N) = Pois(sn/2)(m) n^{-2m} ∑_e Φ(count e)`. -/
lemma sum_piAntidiag_eq {n : ℕ} (s : ℝ) (Φ : RSGraph n → ℝ) (m : ℕ) :
    ∑ N ∈ Finset.piAntidiag Finset.univ m, poisPi (rsMean n s) N * Φ N =
      poisPMF (s * n / 2) m * (((n : ℝ) ^ (2 * m))⁻¹ *
        ∑ e : Fin m → Fin n × Fin n, Φ (rsEdgeCount e)) := by
  have hfib : ∑ e : Fin m → Fin n × Fin n, Φ (rsEdgeCount e) =
      ∑ N ∈ Finset.piAntidiag Finset.univ m, (Nat.multinomial Finset.univ N : ℝ) * Φ N := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := rsEdgeCount)
      (t := Finset.piAntidiag Finset.univ m) (fun e _ => edgeCount_mem_piAntidiag e)]
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [Finset.sum_congr rfl (fun e he => by rw [(Finset.mem_filter.1 he).2]), Finset.sum_const,
      nsmul_eq_mul, card_fiber_edgeCount, if_pos hN]
  rw [hfib, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [poisPi_rsMean_eq s N hN]
  ring

/-- The same slice as a `HasSum` over the fibre `{N // rsEdges N = m}`
(of `Equiv.sigmaFiberEquiv rsEdges`). -/
lemma hasSum_fiber {n : ℕ} (s : ℝ) (Ψ : RSGraph n → ℝ) (m : ℕ) :
    HasSum (fun y : {N : RSGraph n // rsEdges N = m} => poisPi (rsMean n s) y.1 * Ψ y.1)
      (poisPMF (s * n / 2) m * (((n : ℝ) ^ (2 * m))⁻¹ *
        ∑ e : Fin m → Fin n × Fin n, Ψ (rsEdgeCount e))) := by
  rw [← sum_piAntidiag_eq s Ψ m]
  have H := (Finset.piAntidiag Finset.univ m).hasSum (fun N => poisPi (rsMean n s) N * Ψ N)
  let E : {N : RSGraph n // rsEdges N = m} ≃
      ((Finset.piAntidiag Finset.univ m : Finset (RSGraph n)) : Set (RSGraph n)) :=
    Equiv.subtypeEquivRight fun N => by
      simp [Finset.mem_piAntidiag, rsEdges]
  rw [← E.hasSum_iff] at H
  exact H

end RSPoisSplitAux

open RSPoisSplitAux in
/-- **Poisson splitting.** Under `𝖯_s` the number of edges is `Pois(sn/2)` and, given it, the edges
are i.i.d. uniform ordered pairs (loops allowed): if the right-hand side below converges with `|Φ|`
in place of `Φ`, then `𝖯_s(N) Φ(N)` is summable and
`E_{𝖯_s} Φ = ∑_m Pois(sn/2)(m) · n^{-2m} ∑_{e : Fin m → [n]²} Φ(count(e))`. -/
theorem rs_poisson_split {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (Φ : RSGraph n → ℝ)
    (hΦ : Summable fun m : ℕ => poisPMF (s * n / 2) m *
      (((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n, |Φ (rsEdgeCount e)|)) :
    Summable (fun N => poisPi (rsMean n s) N * Φ N) ∧
      rsExp n s Φ = ∑' m : ℕ, poisPMF (s * n / 2) m *
        (((n : ℝ) ^ (2 * m))⁻¹ * ∑ e : Fin m → Fin n × Fin n, Φ (rsEdgeCount e)) := by
  have hlam : ∀ c, 0 ≤ rsMean n s c := fun c => div_nonneg hs (by positivity)
  have hGsum : Summable fun N => poisPi (rsMean n s) N * |Φ N| := by
    rw [← (Equiv.sigmaFiberEquiv (rsEdges : RSGraph n → ℕ)).summable_iff]
    refine (summable_sigma_of_nonneg
      (fun x => mul_nonneg (rs_poisPi_nonneg hlam _) (abs_nonneg _))).mpr
      ⟨fun m => (hasSum_fiber s (fun N => |Φ N|) m).summable, ?_⟩
    refine hΦ.congr fun m => ?_
    exact ((hasSum_fiber s (fun N => |Φ N|) m).tsum_eq).symm
  have hFsum : Summable fun N => poisPi (rsMean n s) N * Φ N := by
    refine Summable.of_norm_bounded hGsum fun N => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rs_poisPi_nonneg hlam N)]
  refine ⟨hFsum, ?_⟩
  have h1 := (Equiv.sigmaFiberEquiv (rsEdges : RSGraph n → ℕ)).hasSum_iff.mpr hFsum.hasSum
  exact (h1.sigma fun m => hasSum_fiber s Φ m).tsum_eq.symm

end

end ERZeroFreeness
