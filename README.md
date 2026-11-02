# Zero-Freeness on Erdős–Rényi Random Graphs, in Lean 4

For the antiferromagnetic *q*-state Potts model, the zero-field Ising antiferromagnet and the
Viana–Bray spin glass on the Erdős–Rényi random graph *G*(*n*, *d*/*n*), the partition function has
no complex zeros in a fixed neighborhood of the physical parameter interval, with probability
tending to one. This repository holds a Lean 4 formalization, on Mathlib, of these zero-freeness
theorems from the paper

> **Zero-Freeness and Deterministic Counting on Erdős–Rényi Random Graphs**, by Ke Shi (2026),

together with the coefficient-level content of the counting part of its Theorem 1.5 (ii). The Lean code was
written by AI models (Claude, Anthropic) at the author's direction. Every proof is checked by Lean
and uses only Mathlib and Lean's three standard axioms; no result of the literature is assumed.

## What is proved

[`EndStatement.lean`](EndStatement.lean) states the claims below as propositions. It contains no
proofs and imports nothing but Mathlib; it defines every object the claims mention. Lean checks the
proofs, but no machine checks that this file says what the paper says, so the file is kept short
and commented, and its definitions are listed below for a reader to check.

| Claim | Paper |
|---|---|
| `Theorem_1_1` | **Theorem 1.1.** For every integer *q* ≥ 3 and 0 < *d* < *d*₂(*q*) there is ρ > 0 such that, with probability tending to one, *Z*\_{*G*ₙ}(*q*, *z*) ≠ 0 for every *z* with dist(*z*, [0, 1]) ≤ ρ. Here *d*₂(*q*) = 2(*q*−1)³ log(*q*−1)/(*q*(*q*−2)). |
| `Corollary_1_3` | **Corollary 1.3**, zero-freeness part: for every η > 0 and all large *d*, Theorem 1.1 applies to every integer *q* ≥ (1/2 + η) *d*/log *d*. |
| `Corollary_1_4` | **Corollary 1.4** for *q* ≥ 3, without the algorithm: for every *d* > 0 there is *q*\_*d* such that every integer *q* ≥ 3, *q* ≠ *q*\_*d*, has Potts zero-freeness near [0, 1] or no proper *q*-coloring, with probability tending to one. |
| `Appendix_B` | **Appendix B**, zero-freeness part: zero-freeness near [*x*₀, 1] for *d* < *d*₂(*q*) ((*q*−1+*x*₀)/((*q*−1)(1−*x*₀)))². |
| `Theorem_1_5_i` | **Theorem 1.5 (i)**: the zero-field Ising antiferromagnet, zero-free near [*x*\*, 1] when *d* ((1−*x*\*)/(1+*x*\*))² < 1. |
| `Theorem_1_5_ii` | **Theorem 1.5 (ii)**: the Viana–Bray spin glass, 𝓘\_{*G*ₙ,*J*}(*t*) ≠ 0 for \|*t*\| ≤ tanh β\* and *Z*^VB(β) ≠ 0 near [−β\*, β\*] when *d* tanh² β\* < 1. |
| `Theorem_1_5_ii_counting` | **Theorem 1.5 (ii), counting**, at the level of coefficients: with probability tending to one the graph has at most *n*² *B*^*s* connected vertex sets of each size *s*, and the truncated logarithm built from the first *k* ≥ *C* log(*n*/ε) coefficients ℓ\_*j* is a (1 ± ε)-approximation of *Z*^VB(β), uniformly for β ∈ [−β\*, β\*]. |
| `Lemma_8_1` | **Lemma 8.1**: each coefficient ℓ\_*j* is a sum over the connected induced subgraphs on at most 2*j* vertices; with the previous line, this is why ℓ\_1, …, ℓ\_*k* can be computed from few small subgraphs. |
| `Theorem_C_1` | **Theorem C.1**, zero-freeness part: Potts zero-freeness near [*x*\*, 1] for every *d* < *d*\_cond(*q*, *x*\*), up to the condensation threshold, including the proper-coloring endpoint *x*\* = 0. |
| `dCond_pos` | *d*\_cond(*q*, *x*) > 0 for *x* ∈ [0, 1), so Theorem C.1 is not vacuous. |

[`PaperStatements.lean`](PaperStatements.lean) states further numbered results of the paper in the
same way (it imports Mathlib and `EndStatement.lean` only):

| Claim | Paper |
|---|---|
| `Eq_1_4`, `Eq_1_5`, `Eq_2_2` | the identities (1.4) `eq:ising-af-relation`, (1.5) `eq:viana-bray` and (2.2) `eq:transformation` |
| `Proposition_6_1_tplane`, `Proposition_6_1`, `Proposition_6_1_return_to_z` | **Proposition 6.1** (zero-freeness from a first-moment bound), `t`-plane and `z`-plane forms |
| `Lemma_8_2` | **Lemma 8.2** (connected-set counts), with the `O(1/n)` as an explicit `C/n` |
| `Section_8_interpolation` | the interpolation estimate of Section 8 (Patel–Regts) |
| `Proposition_8_4_ii` | **Proposition 8.4 (ii)** at the level of coefficients, under its zero-freeness hypothesis |
| `Appendix_A_d2_asymptotic`, `Appendix_A_d2_strictMono`, `Appendix_A_dnc_strictMono`, `Appendix_A_dnc_lt_d2_succ`, `Appendix_A_disjoint` | the facts on *d*₂ and *d*\_nc in the proofs of Corollaries 1.3 and 1.4 (Appendix A) |
| `Corollary_1_4_noncolorable` | the non-colorability of *G*(*n*, *d*/*n*) for *d* ≥ (2*q*−1) log *q*, which the paper cites from Achlioptas–Naor |
| `Appendix_B_tplane` | **Appendix B**, `t`-plane form |
| `Proposition_C_2`, `Proposition_C_2_tube` | **Proposition C.2** (complex first moment below condensation), `z`-plane and `t`-plane forms |
| `Lemma_C_3_monotone`, `Lemma_C_3_ks_bound`, `Lemma_C_3_free_energy` | **Lemma C.3**: *d*\_cond(*q*, ·) is monotone, *d*\_cond(*q*, *x*) ≤ *t*(*x*)⁻², and the planted free-energy bound (C.5) |
| `CKPZ_Proposition_3_6` | [CKPZ, Proposition 3.6] for the Potts model, which Lemma C.3 cites |

The counting results of the paper are algorithms with running-time bounds (Theorem 1.2, the counting
parts of Theorems 1.5 and C.1); the algorithms are not formalized (see below).

## Checking the proofs

With [elan](https://github.com/leanprover/elan) installed, in this folder:

```sh
lake exe cache get
lake build
lake env lean scripts/PrintAxioms.lean
```

The first command downloads Mathlib already compiled. Building the library from scratch took about
30 minutes on an Apple-silicon laptop, and its largest process used about 6 GB of memory. The build
prints the warnings
`` declaration uses `sorry` `` only for the files in [`Challenge/`](Challenge/), which state the
claims without proofs for the check below. The last command prints, for every claim,

```
'ERZeroFreeness.endStatement_theorem_1_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's three standard axioms. Lean `v4.33.1` and the matching Mathlib, also `v4.33.1`, are
pinned.

The fuller check, run by this repository's CI on every push, is
`bash .github/scripts/comparator-check.sh` (Linux): [Comparator](https://github.com/leanprover/comparator)
checks that each theorem of [`Solution/`](Solution/) has exactly the statement of its namesake in
[`Challenge/`](Challenge/), that it uses only the standard axioms, and re-checks the proofs with a
second, independently written kernel, `nanoda`. This is the acceptance check of the
[Palomar](https://palomar-registry.org/) registry, whose layout this repository follows
(`comparator-endstatement.json`, `comparator-paperstatements.json`).

## The definitions

The objects of `EndStatement.lean`, each a verbatim copy of the library's definition of the same
name:

| Paper | Lean | Meaning |
|---|---|---|
| *Z*\_*G*(*q*, *z*) (`eq:partition`) | `pottsZ G q z` | ∑\_{σ : *V* → [*q*]} *z*^{*m*\_*G*(σ)}, *m*\_*G*(σ) = number of monochromatic edges (`monoCount`), with 0⁰ = 1 |
| *d*₂(*q*) | `d2 q` | 2(*q*−1)³ log(*q*−1)/(*q*(*q*−2)) |
| *K*\_ρ | `Kρ ρ` | {*z* : ∃ *x* ∈ [0, 1], ‖*z* − *x*‖ ≤ ρ} |
| *G*(*n*, *p*) | `erWeight`, `erProb` | weight *p*^{\|*E*\|}(1−*p*)^{C(*n*,2)−\|*E*\|} of each simple graph on `Fin n` |
| signed *G*(*n*, *p*) | `sgWeight`, `sgProb`, `boolSign` | *G*(*n*, *p*) with independent uniform signs on all pairs |
| *P*\_{*H*,*J*}(*t*), 𝓘\_{*H*,*J*} (`eq:algorithm-polynomial`, `eq:ising-normalization`) | `signedPoly H q J` | E\_σ ∏\_{*e* ∈ *E*(*H*)} (1 + *t J*\_*e A*\_{σ*e*}); for *q* = 2, *A*\_{σ*e*} = σ\_*u*σ\_*v* (`edgeA`) |
| *Z*^VB\_{*G*,*J*}(β) (`eq:viana-bray`) | `vbZ G J β` | ∑\_σ exp(β ∑\_{*uv* ∈ *E*} *J*\_{*uv*} σ\_*u*σ\_*v*) |
| ℓ\_*j* (`eq:log-coefficients`) | `ellCoeff H q J j` | coefficient of *t*^*j* in the formal logarithm of *P*\_{*H*,*J*} (Mathlib's `PowerSeries.logOf`) |
| *Z̃*\_*k*(β) | `vbApprox G J k β` | 2^*n* cosh(β)^{\|*E*\|} exp(∑\_{*j*≤*k*} ℓ\_*j* tanh(β)^*j*) |
| *N*\_*s*(*G*), `eq:connected-set-bound` | `connSetCount`, `ConnSetBound B G` | number of connected induced vertex sets of size *s*; *N*\_*s* ≤ *n*² *B*^*s* for all *s* ≥ 1 |
| *t*(*x*), *M*\_*t* | `tRe q x`, `rsM q t` | *t*(*x*) = (*x*−1)/(*x*+*q*−1), *M*\_*t*(*a*, *b*) = 1 + *t*(*q*[*a*=*b*] − 1) |
| 𝒫\_*u* | `rsPu q` | Borel probability measures on the simplex with mean (1/*q*, …, 1/*q*) |
| Ψ\_{*r*,*x*}(ν) (`eq:bethe-condensation`) | `bethePsi q r x ν` | E[*V*\_*D* log *V*\_*D*] − (*r*/2) E[*E*\_*x* log *E*\_*x*], *D* ∼ Pois(*r*), integrals against ν^{⊗*k*} |
| *d*\_cond(*q*, *x*) | `dCond q x` | inf {*r* > 0 : Ψ\_{*r*,*x*}(ν) > 0 for some ν ∈ 𝒫\_*u*} |

For *n* < *d* the number *d*/*n* exceeds 1 and *G*(*n*, *d*/*n*) is not a probability law; the paper
only considers *n* ≥ *d*, and every claim is a limit, so those finitely many *n* do not matter.

## Paper ↦ Lean

The library is in [`ERZeroFreeness/`](ERZeroFreeness/), one file per step of the proofs.

| Paper | Lean (file) |
|---|---|
| Theorem 1.1 `thm:zero-free` | `potts_zero_free` (`Main`) |
| Proposition 6.1 `prop:zero-free-moment` | `prop_zero_free_moment` (`Main`); `t`-plane part `zero_free_of_first_moment` (`Transfer`) |
| `eq:transformation` | `pottsZ_eq_zhat`, `zplane_of_tplane` (`Normalize`) |
| Theorem 3.1 `lem:analytic-transfer` (as used) | `exists_norm_le_of_isBigO_pow` (`Vanishing`) and the argument of `zero_free_of_first_moment` (`Transfer`) |
| Lemma 3.2 `lem:holomorphic-tightness` (as used) | `erProb_exists_norm_gt_le` (`SupBound`) |
| Lemma 3.3 `lem:cycle-general` (finite form) | `cycleModel_differentiableOn`, `cycleModel_sub_cyclePoly_isBigO`, `cycleModel_bounds` (`CycleModel`) |
| Lemma 4.1 `lem:cycle-counts` | `cycleCounts_tendsto_poisson` (`CycleLimits`); factorial moments `tendsto_erExp_cycle_descFactorial` (`CycleMoments`); method of moments `tendsto_prob_eq_of_factorial_moments` (`Bonferroni`) |
| Lemma 4.2 `lem:jets` | `zhat_coeff_eq_cyclePoly_whp` (`CycleLimits`), `zhat_coeff_eq_cyclePoly_coeff` (`TaylorGood`), `tendsto_erProb_hasDenseSubgraph` (`DenseSubgraph`) |
| Lemma 5.1 `lem:remainder` | `remainder_bound` (`Remainder`) |
| Lemma 5.2 `lem:entropy-comparison` | `entropy_comparison` (`Entropy`) |
| Theorem 5.3 `thm:multinomial-moment` [Agrawal] | `exists_sum_exp_empKL_le` (`Multinomial`) |
| Lemma 5.4 `lem:moment-bound` | `second_moment_bound` (`SecondMoment`), with `two_replica_bound` (`TwoReplica`) and `overlap_energy_le_empKL` (`Overlap`) |
| `eq:potts-first-moment` | `first_moment_bound` (`FirstMoment`) |
| Corollary 1.3 `cor:range` | `cor_range`, `cor_range_d2` (`CountColor`) |
| Corollary 1.4 `cor:all-but-one` | `cor_all_but_one`, `cor_all_but_one_arith` (`CountColor`); non-colorability for *d* ≥ (2*q*−1) log *q*: `noncolorable_whp` (`NonColor`) |
| Appendix A: *d*₂ increasing, *d*₂(*q*) ∼ 2*q* log *q*, *d*\_nc increasing | `d2_strictMonoOn`, `tendsto_d2_div_two_mul_log`, `dnc_strictMonoOn` (`CountColor`) |
| Appendix B `app:positive-temperature` | `potts_zero_free_positive_temperature`, `pt_zero_free_tplane` (`PTMain`); `pt_second_moment_bound` (`PTSecondMoment`), `pt_first_moment_bound` (`PTFirstMoment`) |
| Theorem 1.5 (i) | `ising_af_zero_free` (`IsingMain`); `ising_second_moment` (`IsingSecondMoment`); `eq:rademacher-moment`: `rademacher_moment_display` (`IsingRademacher`) |
| `eq:ising-af-relation` | `ising_af_relation` (`IsingRelation`) |
| Theorem 1.5 (ii), zero-freeness | `viana_bray_zero_free` (`VBMain`); `vb_second_moment` (`VBSecondMoment`); signed cycle counts `sgCycleCounts_tendsto_poisson` (`VBCycleMoments`); `vb_disk_zero_free` (`VBTransfer`) |
| `eq:viana-bray` | `vbZ_eq` (`VBRelation`) |
| Theorem 1.5, zero-freeness, (i) and (ii) together | `ising_applications_zero_free` (`VBMain`) |
| `eq:log-coefficients` and the recursion of Lemma 8.3 | `logCoeff`, `logCoeff_recursion`, `logCoeff_eq_coeff_logOf` (`CountLogCoeff`) |
| Lemma 8.1 `lem:local-decomposition` | `local_decomposition`, `omegaCoeff_eq_zero_of_card_lt` (`CountLocal`) |
| Lemma 8.2 `lem:connected-sets` | `connected_sets`, `card_local_sets_le` (`CountConnSets`) |
| Interpolation estimate (Section 8) | `interpolation_estimate`, `exists_eval_eq_exp_logCoeff` (`CountInterp`) |
| Proposition 8.4 (ii) `prop:counting`, coefficient level | `vb_counting_real`, `vb_counting_coefficients` (`CountVB`) |
| Theorem 1.5 (ii), counting, coefficient level | `viana_bray_counting` (`CountVBMain`) |
| Theorem C.1 `thm:rs-extension`, zero-freeness | `potts_zero_free_up_to_condensation` (`AppendixC`); form with the explicit hypothesis `CKPZProp36 q`: `potts_zero_free_condensation` (`RSMain`) |
| Proposition C.2 `prop:rs-first-moment` | `rs_first_moment_tube_unconditional`, `rs_first_moment_zplane_unconditional` (`AppendixC`) |
| Lemma C.3 `lem:rs-ckpz` | `rs_dCond_mono` (`RSBetheMono`), `rs_dCond_le_inv_sq` (`RSBetheKS`), `rs_free_energy_unconditional` (`AppendixC`) |
| Lemma C.4 `lem:rs-transfer` | `rs_transfer` (`RSSplit`) |
| Lemma C.5 `lem:rs-local` | `rs_local_i`, `rs_local_ii` (`RSLocal`) |
| Lemma C.6 `lem:rs-conc` | `rs_cond_poisson_exp_le`, `rs_cond_poisson_abs_le` (`RSConc`) |
| Lemma C.7 `lem:rs-anchor` | `rs_anchor` (`RSAnchor`) |
| [CKPZ, Proposition 3.6], Potts case (cited by Lemma C.3) | `ckpz_prop36` (`CKMain`), proved in the `CK*` files; the mathematics is written out in [`docs/ckpz-proof.md`](docs/ckpz-proof.md) |
| *d*\_cond(*q*, *x*) > 0 (not in the paper) | `rs_dCond_pos` (`RSBethePos`) |

## Where the formal proofs differ from the paper's

The statements are the paper's. In several places the proofs take a more elementary route, chosen so
that everything follows from Mathlib alone.

1. **Analytic transfer (Theorem 3.1).** Instead of tightness in the space of holomorphic functions,
   Prokhorov, Montel and Portmanteau, a *quantitative identity theorem*
   (`exists_norm_le_of_isBigO_pow`): a function bounded by 1 near the tube and vanishing to order
   *k* at 0 is at most ε(*k*) → 0 on a thinner tube. Since the short-cycle counts are
   integer-valued, convergence in law is replaced by convergence of mass functions.
2. **The cycle model (Lemma 3.3).** Instead of the almost-sure infinite product 𝒲, for each degree
   *m* the compensated finite product 𝒲\_*m*; no infinite product measure is needed.
3. **Agrawal's bound (Theorem 5.3)** is proved with *some* constant uniform in *n* (a binomial
   Chernoff bound and the chain rule for relative entropy) rather than the sharp one; only
   uniformity in *n* is used.
4. **Hoeffding (Lemma 5.1).** The rarity of unbalanced colorings follows from the same
   relative-entropy bound.
5. **Appendix B** re-proves only the parameter-choice wrappers of Lemma 5.4 and
   `eq:potts-first-moment` for a general interval; the two-replica bound is reused unchanged.
6. **Theorem 1.5 (i).** The Hölder step is replaced by convexity of exp, with the same bound;
   `eq:rademacher-moment` is proved with Gaussian integrals.
7. **Theorem 1.5 (ii).** Signs are uniform on all pairs, which is equivalent for every event that
   depends on the signs of edges only. The joint factorial moments of the signed cycle counts are
   computed directly instead of by conditioning on the graph and Poisson thinning. Disk versions of
   the analytic tools replace the tube versions.
8. **Section 8.** ℓ\_*j* is computed by the recursion of Lemma 8.3 and identified with the formal
   logarithm (`logCoeff_eq_coeff_logOf`). Lemma 8.1's support bound is proved by a Möbius-locality
   calculus. Lemma 8.2 counts parent maps (*s*^{*s*−1} of them) instead of spanning trees by
   Cayley's formula, with an explicit *C*/*n*. Proposition 8.4 (ii) is stated for the exact
   truncated value instead of the algorithm's numerical output.
9. **Corollaries 1.3 and 1.4.** Corollary 1.3 goes through *d*₂(*q*) > 2(*q*−1) log(*q*−1).
   For Corollary 1.4 the non-colorability of *G*(*n*, *d*/*n*) for *d* ≥ (2*q*−1) log *q*, which
   the paper cites from Achlioptas–Naor, is proved by a first-moment computation
   (`noncolorable_whp`).
10. **Appendix C.** "sup\_*n*" is read as sup over *n* ≥ *d*; the conditioning of the Poisson model
   on simplicity is replaced by a direct likelihood comparison; Lemma C.4 and the compactness
   argument are carried out in the *t*-plane.
11. **[CKPZ, Proposition 3.6].** Instead of citing it, the Potts case is proved by a self-contained
   Aizenman–Sims–Starr argument ([`docs/ckpz-proof.md`](docs/ckpz-proof.md)): Nishimori identities
   for a pinned planted model, a bridge from the literal to the planted free energy, the cavity
   decomposition, the edge term by convexity in the rate, the vertex term by decorrelation, an
   entropy-telescoping pinning lemma and a Cesàro average. It uses only finite entropy, absolutely
   convergent Poisson series and elementary real analysis.

## Not formalized

* **Algorithms and running times:** Theorem 1.2, the algorithms of Corollaries 1.3 and 1.4
  (including the exact algorithms for *q* = 1, 2), the FPTAS of Appendix B, the counting parts
  of Theorem 1.5 (i) and of Theorem C.1, Proposition 8.4 (i) (Barvinok's method with the
  polynomial φ\_δ), and Lemma 8.3 as an algorithm (the exact computation of the ℓ\_*j* and their
  bit lengths). For
  Theorem 1.5 (ii) the coefficient-level content is formalized (`Theorem_1_5_ii_counting`).
* **Remarks outside the theorems:** *d*₂(*q*) ≤ *d*\_cond(*q*, 0) (which uses [CKPZ, Theorem 1.2];
  so the formalization does not show that Theorem C.1 at *x*\* = 0 contains Theorem 1.1),
  the asymptotics of *d*\_cond(*q*, 0), the identification of *d*\_cond with the threshold of
  [CKPZ], and the sharpness of the constant 1/2 in Corollary 1.3 (which uses the colorability
  lower bound of Achlioptas–Naor).

## Layout

| Path | Contents |
|---|---|
| `EndStatement.lean`, `PaperStatements.lean` | trusted: the claims, with every definition they use; Mathlib only |
| `Challenge/` | trusted: the claims with `sorry`, for Comparator |
| `Solution/` | the claims, imported from the library |
| `ERZeroFreeness/` | the proofs; `ERZeroFreeness/Statements/` derives the claims from the library |
| `docs/ckpz-proof.md` | the proof of [CKPZ, Proposition 3.6] for the Potts model, as formalized |
| `scripts/PrintAxioms.lean` | prints the axioms of every claim |
| `comparator-*.json`, `.github/` | the Comparator configurations and the CI that runs them |

## License

Apache 2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE).
