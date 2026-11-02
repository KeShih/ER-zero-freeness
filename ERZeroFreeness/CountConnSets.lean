/-
Copyright (c) 2026 Ke Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ERZeroFreeness.CountDefs
import ERZeroFreeness.ErdosRenyi

/-! # `CountConnSets`: Lemma 8.2 `lem:connected-sets` (blueprint §8)

Plan.  Cayley's formula is not in Mathlib; it is replaced by parent maps.  `exists_parent_map`:
`f v` = the second vertex of a shortest walk from `v` to `r` in `G[S]`
(`Reachable.exists_walk_length_eq_dist`, `dist_le`); the distance to `r` strictly decreases
along `f`, so `s(v, f v) = s(w, f w)` with `v ≠ w` (i.e. `v = f w`, `w = f v`) is impossible.
`erProb_induce_connected_le`: union over the `≤ s^{s-1}` maps `g : S.erase r → S` with injective
non-loop edge map of `{E_g ⊆ E(G)}`, each of probability `p^{s-1}`
(`erProb_subset_edgeFinset`).  `erExp_connSetCount_le`: linearity, `binom(n,s) ≤ n^s/s!`
(`Nat.choose_le_pow_div`), `s^s/s! ≤ e^s` (`Real.pow_div_factorial_le_exp`).
`connected_sets`: `N_s = 0` for `s > n`; Markov (`erProb_le_erExp_div`) and the union bound over
`1 ≤ s ≤ n` give `≤ (1/n) ∑_{s ≥ 1} x^s ≤ 1/n`, `x = e(d+1)/B < 1/2`; so `C = 1`.
-/

open Polynomial Filter Topology

namespace ERZeroFreeness

open scoped Classical

noncomputable section

section CountConnSets

/-- [CS.1] The union bound for a finite family of events (public copy of the private
`denseSubgraph_erProb_biUnion_le`). -/
theorem Count.erProb_biUnion_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ι : Type*}
    (T : Finset ι) (A : ι → Set (SimpleGraph (Fin n))) :
    erProb n p (⋃ i ∈ T, A i) ≤ ∑ i ∈ T, erProb n p (A i) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine (Finset.sum_eq_zero fun G _ => if_neg ?_).le
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.mem_empty_iff_false,
      not_false_eq_true]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (erProb_union_le hp0 hp1 _ _).trans (add_le_add le_rfl ih)

/-- The distance to the root `r` inside `G[S]` (junk value `0` off `S`). -/
private def CountConnSets_delta {V : Type*} (G : SimpleGraph V) (S : Finset V) {r : V}
    (hr : r ∈ S) (x : V) : ℕ :=
  if hx : x ∈ S then (G.induce (S : Set V)).dist ⟨x, hx⟩ ⟨r, hr⟩ else 0

/-- One step of a shortest walk to the root: every `v ∈ S \ {r}` has a neighbour in `S` that is
strictly closer to `r` inside `G[S]`. -/
private lemma CountConnSets_exists_closer {V : Type*} (G : SimpleGraph V) {S : Finset V}
    (hS : (G.induce (S : Set V)).Connected) {r : V} (hr : r ∈ S) {v : V} (hv : v ∈ S)
    (hvr : v ≠ r) :
    ∃ u, u ∈ S ∧ G.Adj v u ∧ CountConnSets_delta G S hr u < CountConnSets_delta G S hr v := by
  obtain ⟨w, hw⟩ := (hS.preconnected ⟨v, hv⟩ ⟨r, hr⟩).exists_walk_length_eq_dist
  have hne : (⟨v, hv⟩ : (S : Set V)) ≠ ⟨r, hr⟩ := fun h => hvr (congrArg Subtype.val h)
  obtain ⟨u', hadj, w', rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hne w
  refine ⟨u'.1, u'.2, hadj, ?_⟩
  have hu : CountConnSets_delta G S hr u'.1 = (G.induce (S : Set V)).dist u' ⟨r, hr⟩ := by
    rw [CountConnSets_delta, dif_pos (Finset.mem_coe.mp u'.2)]
  have hv' : CountConnSets_delta G S hr v = (G.induce (S : Set V)).dist ⟨v, hv⟩ ⟨r, hr⟩ := by
    rw [CountConnSets_delta, dif_pos hv]
  rw [hu, hv', ← hw, SimpleGraph.Walk.length_cons]
  exact Nat.lt_succ_of_le (SimpleGraph.dist_le w')

/-- [CS.2] Parent maps (replacing spanning trees): a connected `G[S]` with root `r ∈ S` has a
map `f` sending each `v ∈ S \ {r}` to a neighbour `f v ∈ S`, with the edges `v f(v)` pairwise
distinct. -/
theorem exists_parent_map {V : Type*} [Fintype V] (G : SimpleGraph V) {S : Finset V}
    (hS : (G.induce (S : Set V)).Connected) {r : V} (hr : r ∈ S) :
    ∃ f : V → V, (∀ v ∈ S, v ≠ r → f v ∈ S ∧ G.Adj v (f v)) ∧
      Set.InjOn (fun v => s(v, f v)) (S.erase r : Set V) := by
  have hf : ∀ v ∈ S, v ≠ r → ∃ u, u ∈ S ∧ G.Adj v u ∧
      CountConnSets_delta G S hr u < CountConnSets_delta G S hr v :=
    fun v hv hvr => CountConnSets_exists_closer G hS hr hv hvr
  choose! f hfS hfadj hflt using hf
  refine ⟨f, fun v hv hvr => ⟨hfS v hv hvr, hfadj v hv hvr⟩, ?_⟩
  intro v hv w hw hvw
  rw [Finset.mem_coe, Finset.mem_erase] at hv hw
  rcases Sym2.eq_iff.mp hvw with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact h1
  · exfalso
    have a := hflt v hv.2 hv.1
    have b := hflt w hw.2 hw.1
    rw [h2] at a
    rw [← h1] at b
    omega

/-- [CS.3] `Pr[G[S] connected] ≤ s^{s-1} p^{s-1}` in `G(n,p)`, `s = |S|` (the paper's
`s^{s-2}` from Cayley's formula, weakened). -/
theorem erProb_induce_connected_le {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (S : Finset (Fin n)) :
    erProb n p {G | (G.induce (S : Set (Fin n))).Connected} ≤
      (S.card : ℝ) ^ (S.card - 1) * p ^ (S.card - 1) := by
  rcases S.eq_empty_or_nonempty with hS | ⟨r, hr⟩
  · subst hS
    simp only [Finset.card_empty, Nat.zero_sub, pow_zero, mul_one]
    exact erProb_le_one hp0 hp1 _
  set E : (↥(S.erase r) → ↥S) → Finset (Sym2 (Fin n)) :=
    fun g => Finset.univ.image (fun v => s(v.1, (g v).1)) with hE
  set Φ := Finset.univ.filter (fun g : ↥(S.erase r) → ↥S =>
    E g ⊆ (⊤ : SimpleGraph (Fin n)).edgeFinset ∧ (E g).card = S.card - 1) with hΦ
  have hsub : {G : SimpleGraph (Fin n) | (G.induce (S : Set (Fin n))).Connected} ⊆
      ⋃ g ∈ Φ, {G | E g ⊆ G.edgeFinset} := by
    intro G hG
    obtain ⟨f, hf, hinj⟩ := exists_parent_map G hG hr
    let g : ↥(S.erase r) → ↥S := fun v =>
      ⟨f v.1, (hf v.1 (Finset.mem_of_mem_erase v.2) (Finset.ne_of_mem_erase v.2)).1⟩
    have hEG : E g ⊆ G.edgeFinset := by
      intro x hx
      rw [hE, Finset.mem_image] at hx
      obtain ⟨v, _, rfl⟩ := hx
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (hf v.1 (Finset.mem_of_mem_erase v.2) (Finset.ne_of_mem_erase v.2)).2
    have hcard : (E g).card = S.card - 1 := by
      rw [hE, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_coe,
        Finset.card_erase_of_mem hr]
      intro v w hvw
      have hv := Finset.mem_erase.mp v.2
      have hw := Finset.mem_erase.mp w.2
      exact Subtype.ext (hinj (by simp [hv.1, hv.2]) (by simp [hw.1, hw.2]) hvw)
    have hgΦ : g ∈ Φ := by
      rw [hΦ, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hEG.trans (SimpleGraph.edgeFinset_mono le_top), hcard⟩
    exact Set.mem_iUnion₂.mpr ⟨g, hgΦ, hEG⟩
  calc erProb n p {G | (G.induce (S : Set (Fin n))).Connected}
      ≤ erProb n p (⋃ g ∈ Φ, {G | E g ⊆ G.edgeFinset}) := erProb_mono hp0 hp1 hsub
    _ ≤ ∑ g ∈ Φ, erProb n p {G | E g ⊆ G.edgeFinset} := Count.erProb_biUnion_le hp0 hp1 Φ _
    _ = ∑ g ∈ Φ, p ^ (S.card - 1) := by
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hΦ, Finset.mem_filter] at hg
        rw [erProb_subset_edgeFinset _ hg.2.1, hg.2.2]
    _ = (Φ.card : ℝ) * p ^ (S.card - 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (S.card : ℝ) ^ (S.card - 1) * p ^ (S.card - 1) := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hp0 _)
        have h1 : Φ.card ≤ Fintype.card (↥(S.erase r) → ↥S) := Finset.card_le_univ Φ
        rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_coe,
          Finset.card_erase_of_mem hr] at h1
        exact_mod_cast h1

/-- `N_s(G)` as a sum of indicators over the `s`-subsets. -/
private lemma CountConnSets_connSetCount_eq {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) :
    (connSetCount G s : ℝ) = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = s),
      if (G.induce (S : Set (Fin n))).Connected then (1 : ℝ) else 0 := by
  rw [connSetCount, ← Finset.filter_filter, Finset.card_filter]
  push_cast
  rfl

/-- Linearity: `E[N_s] = ∑_{|S| = s} Pr[G[S] connected]`. -/
private lemma CountConnSets_erExp_connSetCount {n : ℕ} (p : ℝ) (s : ℕ) :
    erExp n p (fun G => (connSetCount G s : ℝ)) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = s),
        erProb n p {G | (G.induce (S : Set (Fin n))).Connected} := by
  simp only [erExp, erProb, CountConnSets_connSetCount_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun G _ => ?_
  by_cases h : (G.induce (S : Set (Fin n))).Connected <;> simp [h]

/-- The numerical part of [CS.4]:
`binom(n,s) s^{s-1} (d/n)^{s-1} ≤ n (e(d+1))^s` for `0 ≤ d ≤ n`, `s ≥ 1`. -/
private lemma CountConnSets_numeric {d : ℝ} (hd : 0 ≤ d) {n : ℕ} {s : ℕ} (hs : 1 ≤ s) :
    (n.choose s : ℝ) * ((s : ℝ) ^ (s - 1) * (d / n) ^ (s - 1)) ≤
      n * (Real.exp 1 * (d + 1)) ^ s := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hF : (0 : ℝ) < ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have h1 : (n.choose (m + 1) : ℝ) ≤ (n : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) :=
    Nat.choose_le_pow_div (m + 1) n
  have h2 : ((m : ℝ) + 1) ^ m / ((m + 1).factorial : ℝ) ≤ Real.exp 1 ^ (m + 1) := by
    calc ((m : ℝ) + 1) ^ m / ((m + 1).factorial : ℝ)
        ≤ ((m : ℝ) + 1) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ hF.le
          exact pow_le_pow_right₀ (by linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]) (Nat.le_succ m)
      _ ≤ Real.exp ((m : ℝ) + 1) := by
          have := Real.pow_div_factorial_le_exp (x := (m : ℝ) + 1) (by positivity) (m + 1)
          exact_mod_cast this
      _ = Real.exp 1 ^ (m + 1) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
  have h3 : d ^ m ≤ (d + 1) ^ (m + 1) :=
    (pow_le_pow_left₀ hd (by linarith) m).trans (pow_le_pow_right₀ (by linarith) (Nat.le_succ m))
  calc (n.choose (m + 1) : ℝ) * (((m + 1 : ℕ) : ℝ) ^ m * (d / n) ^ m)
      ≤ (n : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ) * (((m + 1 : ℕ) : ℝ) ^ m * (d / n) ^ m) := by
        refine mul_le_mul_of_nonneg_right h1 ?_
        positivity
    _ = n * ((((m : ℝ) + 1) ^ m / ((m + 1).factorial : ℝ)) * d ^ m) := by
        rw [div_pow]
        push_cast
        field_simp
        ring
    _ ≤ n * (Real.exp 1 ^ (m + 1) * (d + 1) ^ (m + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hn'.le
        exact mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = n * (Real.exp 1 * (d + 1)) ^ (m + 1) := by rw [mul_pow]

/-- [CS.4] `E[N_s(G_n)] ≤ n [e(d+1)]^s` for `s ≥ 1` (proof of `lem:connected-sets`). -/
theorem erExp_connSetCount_le {d : ℝ} (hd : 0 ≤ d) {n : ℕ} (hn : d ≤ n) {s : ℕ} (hs : 1 ≤ s) :
    erExp n (d / n) (fun G => (connSetCount G s : ℝ)) ≤ n * (Real.exp 1 * (d + 1)) ^ s := by
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd hn
  rw [CountConnSets_erExp_connSetCount]
  calc ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = s),
        erProb n (d / n) {G | (G.induce (S : Set (Fin n))).Connected}
      ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = s),
          ((s : ℝ) ^ (s - 1) * (d / n) ^ (s - 1)) := by
        refine Finset.sum_le_sum fun S hS => ?_
        have h := erProb_induce_connected_le hp0 hp1 S
        rwa [(Finset.mem_filter.mp hS).2] at h
    _ = (n.choose s : ℝ) * ((s : ℝ) ^ (s - 1) * (d / n) ^ (s - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.univ_filter_card_eq, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]
    _ ≤ n * (Real.exp 1 * (d + 1)) ^ s := CountConnSets_numeric hd hs

/-- `N_s(G) = 0` for `s > n`: there is no `s`-subset of `Fin n`. -/
private lemma CountConnSets_connSetCount_eq_zero {n : ℕ} (G : SimpleGraph (Fin n)) {s : ℕ}
    (hs : n < s) : connSetCount G s = 0 := by
  unfold connSetCount
  rw [Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun S hS => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
  have := Finset.card_le_univ S
  rw [Fintype.card_fin] at this
  omega

/-- [CS.5] **Lemma 8.2 `lem:connected-sets`.** For every fixed `B > 2e(d+1)`, with probability
`1 - O(1/n)` over `G_n ∼ G(n,d/n)`, `N_s(G_n) ≤ n² B^s` simultaneously for all `s ≥ 1`
(here: the failure probability is `≤ C/n` for all `n ≥ d`). -/
theorem connected_sets {d : ℝ} (hd : 0 < d) {B : ℝ} (hB : 2 * Real.exp 1 * (d + 1) < B) :
    ∃ C : ℝ, ∀ n : ℕ, d ≤ n → erProb n (d / n) {G | ¬ ConnSetBound B G} ≤ C / n := by
  refine ⟨1, fun n hn => ?_⟩
  obtain ⟨hp0, hp1⟩ := div_natCast_mem_Icc hd.le hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hd hn
  have he : 0 < Real.exp 1 * (d + 1) := by positivity
  have hB0 : 0 < B := by linarith
  set x := Real.exp 1 * (d + 1) / B with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ hB0]
    linarith
  have hsub : {G : SimpleGraph (Fin n) | ¬ ConnSetBound B G} ⊆
      ⋃ i ∈ Finset.range n,
        {G | (n : ℝ) ^ 2 * B ^ (i + 1) ≤ (connSetCount G (i + 1) : ℝ)} := by
    intro G hG
    simp only [Set.mem_ofPred_eq, ConnSetBound, not_forall, not_le] at hG
    obtain ⟨s, hs1, hs⟩ := hG
    have hsn : s ≤ n := by
      by_contra h
      rw [CountConnSets_connSetCount_eq_zero G (by omega), Nat.cast_zero] at hs
      exact absurd hs (not_lt.mpr (by positivity))
    refine Set.mem_iUnion₂.mpr ⟨s - 1, Finset.mem_range.mpr (by omega), ?_⟩
    have h' : s - 1 + 1 = s := by omega
    rw [Set.mem_ofPred_eq, h']
    exact hs.le
  calc erProb n (d / n) {G | ¬ ConnSetBound B G}
      ≤ erProb n (d / n) (⋃ i ∈ Finset.range n,
          {G | (n : ℝ) ^ 2 * B ^ (i + 1) ≤ (connSetCount G (i + 1) : ℝ)}) :=
        erProb_mono hp0 hp1 hsub
    _ ≤ ∑ i ∈ Finset.range n, erProb n (d / n)
          {G | (n : ℝ) ^ 2 * B ^ (i + 1) ≤ (connSetCount G (i + 1) : ℝ)} :=
        Count.erProb_biUnion_le hp0 hp1 _ _
    _ ≤ ∑ i ∈ Finset.range n, (1 / n) * (1 / 2 : ℝ) ^ (i + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have ha : 0 < (n : ℝ) ^ 2 * B ^ (i + 1) := by positivity
        refine (erProb_le_erExp_div hp0 hp1 (fun G => Nat.cast_nonneg _) ha).trans ?_
        refine (div_le_div_of_nonneg_right
          (erExp_connSetCount_le hd.le hn (Nat.le_add_left 1 i)) ha.le).trans ?_
        have hxe : (n : ℝ) * (Real.exp 1 * (d + 1)) ^ (i + 1) / ((n : ℝ) ^ 2 * B ^ (i + 1)) =
            (1 / n) * x ^ (i + 1) := by
          rw [hx, div_pow]
          field_simp
        rw [hxe]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 _) (by positivity)
    _ = (1 / n) * ((1 / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ 1 / n := by
        have h := sum_geometric_two_le n
        have h' : (1 / 2 : ℝ) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i ≤ 1 := by linarith
        calc (1 / n : ℝ) * ((1 / 2) * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ i) ≤ (1 / n) * 1 :=
              mul_le_mul_of_nonneg_left h' (by positivity)
          _ = 1 / n := mul_one _

/-- [CS.6] The connected-set event has probability tending to one. -/
theorem tendsto_erProb_connSetBound {d : ℝ} (hd : 0 < d) {B : ℝ}
    (hB : 2 * Real.exp 1 * (d + 1) < B) :
    Tendsto (fun n : ℕ => erProb n (d / n) {G | ConnSetBound B G}) atTop (𝓝 1) := by
  obtain ⟨C, hC⟩ := connected_sets hd hB
  have hlim : Tendsto (fun n : ℕ => 1 - C / n) atTop (𝓝 1) := by
    have h := (tendsto_const_div_atTop_nhds_zero_nat C).const_sub 1
    rwa [sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    have hc : {G : SimpleGraph (Fin n) | ConnSetBound B G} = {G | ¬ ConnSetBound B G}ᶜ := by
      ext G
      simp
    rw [hc, erProb_compl]
    linarith [hC n hdn]
  · filter_upwards [eventually_ge_atTop ⌈d⌉₊] with n hn
    have hdn : d ≤ n := (Nat.le_ceil d).trans (by exact_mod_cast hn)
    obtain ⟨h0, h1⟩ := div_natCast_mem_Icc hd.le hdn
    exact erProb_le_one h0 h1 _

/-- [CS.7] On the event `eq:connected-set-bound` (with `B ≥ 1`), the decomposition
`lem:local-decomposition` of `ℓ_1, …, ℓ_k` uses at most `2k n² B^{2k}` connected sets (the
coefficient-level content of `lem:coefficient-oracle`). -/
theorem card_local_sets_le {n : ℕ} {B : ℝ} (hB : 1 ≤ B) {G : SimpleGraph (Fin n)}
    (hG : ConnSetBound B G) (k : ℕ) :
    ((Finset.univ.filter fun S : Finset (Fin n) =>
        1 ≤ S.card ∧ S.card ≤ 2 * k ∧ (G.induce (S : Set (Fin n))).Connected).card : ℝ) ≤
      2 * k * (n : ℝ) ^ 2 * B ^ (2 * k) := by
  have h1 : (Finset.univ.filter fun S : Finset (Fin n) =>
        1 ≤ S.card ∧ S.card ≤ 2 * k ∧ (G.induce (S : Set (Fin n))).Connected).card ≤
      ∑ s ∈ Finset.Icc 1 (2 * k), connSetCount G s := by
    unfold connSetCount
    refine (Finset.card_le_card ?_).trans Finset.card_biUnion_le
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    simp only [Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨S.card, ⟨hS.1, hS.2.1⟩, rfl, hS.2.2⟩
  calc ((Finset.univ.filter fun S : Finset (Fin n) =>
        1 ≤ S.card ∧ S.card ≤ 2 * k ∧ (G.induce (S : Set (Fin n))).Connected).card : ℝ)
      ≤ ∑ s ∈ Finset.Icc 1 (2 * k), (connSetCount G s : ℝ) := by
        exact_mod_cast h1
    _ ≤ ∑ s ∈ Finset.Icc 1 (2 * k), (n : ℝ) ^ 2 * B ^ (2 * k) := by
        refine Finset.sum_le_sum fun s hs => ?_
        rw [Finset.mem_Icc] at hs
        exact (hG s hs.1).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB hs.2) (by positivity))
    _ = 2 * k * (n : ℝ) ^ 2 * B ^ (2 * k) := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
        push_cast
        ring

end CountConnSets

end

end ERZeroFreeness
