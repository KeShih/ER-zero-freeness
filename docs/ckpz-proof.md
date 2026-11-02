# A self-contained proof of the planted free-energy bound [CKPZ, Prop. 3.6] for the Potts antiferromagnet

## Introduction

**The result.** Coja-Oghlan, Krzakala, Perkins and Zdeborová [CKPZ, Proposition 3.6] bound the free energy of planted random factor-graph models, under their hypotheses SYM and BAL, from above by the supremum of the Bethe functional. This document proves the case of their result that is used in Appendix C of the paper *Zero-Freeness and Deterministic Counting on Erdős–Rényi Random Graphs* by Ke Shi (below, "the paper"): the antiferromagnetic $q$-state Potts model in which a monochromatic edge has weight $x\in(0,1)$ relative to a bichromatic one, on multigraphs with a Poisson number of independent, uniformly random ordered edges.

Let $q\ge2$ and $x\in(0,1)$, and let $M$ be the symmetric $q\times q$ matrix with diagonal entries $xq/(x+q-1)$ and off-diagonal entries $q/(x+q-1)$. For an edge list $e=(e_1,\dots,e_m)\in([n]^2)^m$ put $F_e=q^{-n}\sum_{\sigma\in[q]^n}\prod_{j=1}^mM(\sigma_{e_j^1},\sigma_{e_j^2})$, and let $\bar c_m(n)=\sum_eF_e\log F_e/\sum_eF_e$ be the mean of $\log F_e$ when $e$ is drawn with probability proportional to $F_e$ (the planted model with $m$ edges). Theorem 0.1 (§0.1) states: for every $s>0$, every real $\eta$ with $\Psi_s(\nu)\le\eta$ for all $\nu\in\mathcal P_u$, and every $\varepsilon>0$, the series $\sum_{m\ge0}\mathrm{Pois}(sn/2)(m)\,\bar c_m(n)$ converges absolutely and is at most $(\eta+\varepsilon)n$ for all large $n$. Here $\Psi_s$ is the Bethe functional and $\mathcal P_u$ is the set of probability measures on the simplex $\Delta_q$ with mean $u=(1/q,\dots,1/q)$. In other words,
$$\limsup_{n\to\infty}\frac1n\sum_{m\ge0}\mathrm{Pois}(sn/2)(m)\,\bar c_m(n)\ \le\ \sup_{\nu\in\mathcal P_u}\Psi_s(\nu).$$
Throughout, $q\ge2$. Appendix C of the paper needs only $q\ge3$, and nothing below uses $q\ge3$.

**Its role in the paper.** Appendix C of the paper extends Potts zero-freeness and deterministic approximate counting on $G(n,d/n)$ up to the condensation threshold $d_{\rm cond}(q,x_*)$ (Theorem C.1). Its Lemma C.3 deduces from [CKPZ, Proposition 3.6] that $\mathbb E[F_G\log F_G]=o(n)$ for $x\in(0,1)$ and $0<s<d_{\rm cond}(q,x)$, where $G$ is the Poisson multigraph with independent $\mathrm{Pois}(s/(2n))$ edge counts on the ordered pairs of $[n]^2$ (equation (C.5)). For such $s$, $\sup_{\nu\in\mathcal P_u}\Psi_s(\nu)\le0$ by the definition of $d_{\rm cond}$, so the bound is used with $\eta=0$. Theorem 0.1 is stated directly with the objects of that proof: $\bar c_m(n)$ is the quantity $\bar c_m$ there, and $\Psi_s$ is the functional $\Psi_{s,x}$ of equation (C.1). The identification of these objects with the factor-graph model and the Bethe functional of [CKPZ], carried out in the proof of Lemma C.3, is therefore not needed. This document replaces the citation of [CKPZ, Proposition 3.6] in Lemma C.3 by a self-contained proof.

**Formalization.** The proof is formalized in Lean 4 with Mathlib. The files CKDefs.lean, CKMatrix.lean, CKAnalysis.lean, CKInfo.lean, CKBern.lean, CKBetheFin.lean, CKBethe.lean, CKBridge.lean, CKPlanted.lean, CKEdge.lean, CKPinPost.lean, CKCavity.lean, CKVertex.lean and CKMain.lean prove the theorem `ckpz_prop36 : CKPZProp36 q` for every $q\ge2$, where `CKPZProp36 q` is the statement of Theorem 0.1. The formal proof is complete and uses only Mathlib and Lean's standard axioms. Section 9 lists the Lean theorems that formalize each result, and the places where the formal proof takes a different route.

**Method.** The proof is an Aizenman–Sims–Starr argument for a planted model with random pinning; §0.4 describes its architecture and the order of limits. Lemma 3.3 replaces the literal average by an average over the planted Poisson model, Lemma 4.5 bounds the latter by the planted free energy $a_n(0)$, and Lemma 4.6 controls the cost of revealing the colours of a random set of vertices (pinning). When a vertex is added, the pinned planted free energy grows by at most a vertex term minus an edge term, plus a pin cost (§7); by the Nishimori identities of §4, both terms are expectations of functionals of the posterior law of the colouring given the graph and the pins. The edge term is bounded below by convexity in the edge rate (§5). Both terms are then compared with the Bethe functional at the empirical law of the posterior marginals, with errors controlled by the magnetization and by mutual informations under the posterior; the pinning lemma of §6, proved by entropy telescoping, makes the mutual informations small on average over the pinning level. Mean fixing and a change of rate (§2) turn the comparison into a value of $\Psi_s$ on $\mathcal P_u$, and a Cesàro average over the number of vertices and the pinning level (§8) completes the proof.

**What the proof uses.** Only finite sums and absolutely convergent series over countable sets (Poisson and product-Poisson series); Shannon entropy and mutual information of finite random variables (chain rule, submodularity); and elementary real analysis: convexity, the mean value theorem, Cauchy–Schwarz, Jensen's inequality for finite and countable convex combinations, $\log y\le y-1$, the binomial and multinomial theorems, and the existence of a maximal coupling of two laws on a finite set. Measure theory enters only through Fact 0.2, which evaluates the Bethe functional at finitely supported laws. The proof uses no regularity lemma, no topology on spaces of measures, no continuity of the Bethe functional and no concentration inequality (Azuma, Chernoff, Efron–Stein); in particular, it does not use the conditional-Poisson concentration lemma of the paper (Lemma C.6).

**Organization.** §0 states the theorem and fixes the constants, the notation and the order of limits. §1 collects elementary tools, §§2–7 prove the ingredients listed in §0.4, and §8 assembles them. §9 gives the correspondence with the Lean files.

**References.**
- [CKPZ] A. Coja-Oghlan, F. Krzakala, W. Perkins and L. Zdeborová, *Information-theoretic thresholds from the cavity method*, Advances in Mathematics 333 (2018), 694–795. Results are cited with the numbering of the full version, arXiv:1611.00814v4.
- K. Shi, *Zero-Freeness and Deterministic Counting on Erdős–Rényi Random Graphs*. Its results are cited by their numbers there: Theorem C.1, Lemmas C.3 and C.6, equations (C.1) and (C.5).

---

## 0. Statement, constants, notation, architecture

### 0.1 Objects and statement

Fix $x\in(0,1)$ and put
$$t=t(x)=\frac{x-1}{x+q-1}\in\Bigl(-\frac1{q-1},0\Bigr),\qquad M(a,b)=1+t\,(q\,\mathbf 1[a=b]-1)\quad(a,b\in[q]).$$
This is the matrix $M_x=J+tA$ of Appendix C of the paper, where $J$ is the all-ones matrix and $A=q\,\mathrm{Id}-J$.

**Edge-list partition function and planted free energy.** Let $n\ge1$, $m\ge0$, and let $e=(e_1,\dots,e_m)\in([n]^2)^m$ be an edge list with $e_j=(e_j^1,e_j^2)$. Put
$$F_e=q^{-n}\sum_{\sigma\in[q]^n}\prod_{j=1}^m M(\sigma_{e_j^1},\sigma_{e_j^2}),\qquad
\bar c_m=\bar c_m(n)=\frac{\sum_e F_e\log F_e}{\sum_e F_e}.$$

**The Bethe functional.**
- $\Delta_q$ is the probability simplex in $\mathbb R^q$ and $u=(1/q,\dots,1/q)$.
- For $\mu_1,\mu_2,\ldots\in\Delta_q$ put
$$\mathcal V_d(\mu_1,\dots,\mu_d)=\frac1q\sum_{c\in[q]}\prod_{i=1}^d (M\mu_i)_c,\qquad \mathcal E(\mu_1,\mu_2)=\mu_1^\top M\mu_2 .$$
- For a Borel probability measure $\nu$ on $\Delta_q$ and $r\ge0$, the Bethe functional is
$$\Psi_r(\nu)=\mathrm{BV}_r(\nu)-\frac r2\,\mathrm{BE}(\nu),\qquad
\mathrm{BV}_r(\nu)=\sum_{d\ge0}\mathrm{Pois}(r)(d)\int\Lambda(\mathcal V_d)\,d\nu^{\otimes d},\qquad
\mathrm{BE}(\nu)=\int\Lambda(\mathcal E)\,d\nu^{\otimes2}.$$
- Here $\Lambda(y)=y\log y$ with $\Lambda(0)=0$, and $\mathrm{Pois}(\lambda)(k)=e^{-\lambda}\lambda^k/k!$.
- $\mathcal P_u$ is the set of such $\nu$ with $\int\mu\,d\nu(\mu)=u$.

**Theorem 0.1.** Let $q\ge2$, $x\in(0,1)$ and $s>0$. Let $\eta\in\mathbb R$ satisfy $\Psi_s(\nu)\le\eta$ for every $\nu\in\mathcal P_u$, and let $\varepsilon>0$. Then there is $n_\star$ such that for all $n\ge n_\star$:
- the series $\sum_{m\ge0}\mathrm{Pois}(sn/2)(m)\,\bar c_m(n)$ converges absolutely, and
- $\sum_{m\ge0}\mathrm{Pois}(sn/2)(m)\,\bar c_m(n)\le(\eta+\varepsilon)\,n$.

**Fact 0.2 (Ψ at finitely supported laws).** Let $\nu=\sum_{j=1}^J w_j\delta_{\mu^{(j)}}$ with $w_j\ge0$, $\sum_j w_j=1$ and $\mu^{(j)}\in\Delta_q$.
- Then $\nu^{\otimes d}=\sum_{j_1,\dots,j_d}w_{j_1}\cdots w_{j_d}\,\delta_{(\mu^{(j_1)},\dots,\mu^{(j_d)})}$, so every integral in $\Psi_r(\nu)$ is a finite sum:
$$\int\Lambda(\mathcal V_d)\,d\nu^{\otimes d}=\sum_{j_1,\dots,j_d}\Bigl(\prod_i w_{j_i}\Bigr)\Lambda\bigl(\mathcal V_d(\mu^{(j_1)},\dots,\mu^{(j_d)})\bigr),$$
  and similarly for $\mathrm{BE}$.
- $\nu\in\mathcal P_u$ if and only if $\sum_j w_j\mu^{(j)}=u$.
- The $d$-series converges absolutely by Lemma 1.1(d).

The proof evaluates $\Psi$ only at such finitely supported laws. Continuity of $\Psi$ is never needed.

### 0.2 Constants

All constants depend only on $(q,x,s)$ and are given by explicit formulas at the point where they are introduced.

- **Entries of $M$.** $m_-:=M(a,a)=\frac{xq}{x+q-1}\in(0,1)$ and $m_+:=M(a,b)=\frac{q}{x+q-1}\in\bigl(1,\frac q{q-1}\bigr]$ for $a\ne b$.
- **Their difference.** $\theta:=m_+-m_-=q|t|\in(0,2)$.
- **Logarithmic size.** $\ell_0:=\log(1/m_-)>0$. Then $|\log M(a,b)|\le\ell_0$ for all $a,b$ (Lemma 1.4(e)).
- **Growth constant.** $c_1:=2m_+$.

### 0.3 Notation

- $\mathrm{kl}(y)=\Lambda(y)-y+1$ for $y\ge0$.
- $V$ is a finite vertex set with $n=|V|\ge1$.
- **Colourings.** $\tau\in[q]^V$, with colour-proportion vector $\lambda_\tau\in\Delta_q$, $\lambda_\tau(c)=|\tau^{-1}(c)|/n$.
- **Multigraphs.** $G\in\mathbb N^{V\times V}$ assigns edge counts to all $n^2$ ordered pairs, loops included; $|G|=\sum_{e}G_e$. For $e=(v,w)$ write $M_e(\tau)=M(\tau_v,\tau_w)$, and write $w_G(\tau)=\prod_e M_e(\tau)^{G_e}$.
- **Averages under $\mu$.** For a probability measure $\mu$ on $[q]^V$:
  - $\langle f\rangle_\mu=\sum_\tau\mu(\tau)f(\tau)$;
  - $\mu_v\in\Delta_q$ is the marginal at $v$, and $\mu_{vw}$ the joint marginal of $(\tau_v,\tau_w)$;
  - $\rho_\mu=\frac1n\sum_{v\in V}\delta_{\mu_v}$ is the empirical law of the marginals;
  - $\bar m_\mu=\frac1n\sum_v\mu_v=\langle\lambda_\tau\rangle_\mu$ is its mean;
  - $\mathrm{dev}(\mu):=\langle\|\lambda_\tau-u\|_2\rangle_\mu$.
- **Entropies under $\mu$.** For $S\subseteq V$, $h_\mu(S)=H(\tau_S)$ is the Shannon entropy (natural log) of the marginal of $\tau_S$. Conditional quantities are defined in Lemma 1.5.
- **Bernoulli sets.** $U\sim\mathrm{Bern}(\pi)^V$ means $U\subseteq V$ contains each $v$ independently with probability $\pi_v$; a scalar $\pi$ means $\pi_v\equiv\pi$. Its weight is $\mathrm B_\pi(U)=\prod_{v\in U}\pi_v\prod_{v\notin U}(1-\pi_v)$.

### 0.4 Architecture and order of limits

1. **Literal versus planted form (§3).** Put $f^{\rm lit}_n:=\sum_m\mathrm{Pois}(sn/2)(m)\bar c_m(n)$. Let $\bar f_n$ be the planted average of $\log F$ in which the colouring $\sigma$ is uniform and, given $\sigma$, the edge counts are independent $\mathrm{Pois}(\frac s{2n}M(\sigma_v,\sigma_w))$. Then
$$|f^{\rm lit}_n-\bar f_n|\le C_{\rm br}\sqrt n\qquad(n\ge2).$$
2. **Domination (§4).** $\bar f_n\le a_n(0)$, where $a_n(k)$ is the pinned planted free energy $\mathcal K_{[n]}(\frac s{2n},\pi_k(n))$ with $\pi_k(N)=1-e^{-ks/N}$.
3. **Averaged step bound (§8).** For every integer $T\ge1$ and every $n\ge2$,
$$\frac1T\sum_{k<T}\bigl(a_{n+1}(k)-a_n(k)\bigr)\le\eta+C_{\rm step}\bigl(n^{-1/2}+T^{-1/2}\bigr)+\frac{Ts\log q}{n+1}.$$
   It combines:
   - the exact cavity decomposition (§7);
   - the edge term by convexity in the rate (§5);
   - the vertex term (§7);
   - the pinning lemma (§6);
   - mean fixing and the rate change (§2).
4. **Cesàro (§8).** Combine with $a_N(0)\le\frac1T\sum_{k<T}a_N(k)+Ts\log q$.
5. **Order of limits.** Given $\varepsilon$, first fix $T=T(\varepsilon,q,x,s)$ so that $C_{\rm step}T^{-1/2}\le\varepsilon/3$. Then choose $n_\star(T,\varepsilon,q,x,s,\eta)$. No other limit is taken, except $J\to\infty$ in an explicit real error term inside Lemma 5.3, at fixed $n$ (no limit is interchanged with an expectation).

---

## 1. Elementary tools

**Lemma 1.1 (Λ and kl).**
- **(a)** $\Lambda\ge-1/e$ on $[0,\infty)$, and $\Lambda$ is convex there. $\mathrm{kl}\ge0$, and $\mathrm{kl}'(y)=\log y$ for $y>0$.
- **(b)** If $y,y'\in[e^{-a},e^{a}]$ with $a\ge0$, then $|\Lambda(y)-\Lambda(y')|\le(1+a)|y-y'|$. If $y,y'\in[b_1,b_2]\subset(0,\infty)$, then $|\mathrm{kl}(y)-\mathrm{kl}(y')|\le\max(|\log b_1|,|\log b_2|)\,|y-y'|$.
- **(c)** (Countable Jensen.) Let $w_j\ge0$ be countably many weights with $\sum_jw_j=1$, and let $y_j\in[b_1,b_2]\subset(0,\infty)$. Then $\Lambda(\sum_jw_jy_j)\le\sum_jw_j\Lambda(y_j)$.
- **(d)** If $v\in[m_-^d,m_+^d]$, then $|\Lambda(v)|\le1+d\ell_0m_+^d\le(1+\ell_0)c_1^d$. If $v\in[m_-,m_+]$, then $|\Lambda(v)|\le1+\ell_0m_+$.

*Proof.*
- **(a)** We have $\Lambda'(y)=1+\log y$ and $\Lambda''(y)=1/y>0$, and the minimum is $\Lambda(1/e)=-1/e$. Moreover $\mathrm{kl}(1)=0$, $\mathrm{kl}'(y)=\log y$ and $\mathrm{kl}''>0$.
- **(b)** Use the mean value theorem with $|\Lambda'(y)|=|1+\log y|\le1+a$ on $[e^{-a},e^a]$, and with $|\mathrm{kl}'|=|\log|$.
- **(c)** Put $\bar y=\sum_jw_jy_j\in[b_1,b_2]$. By convexity, $\Lambda(y_j)\ge\Lambda(\bar y)+(1+\log\bar y)(y_j-\bar y)$. Multiply by $w_j$ and sum; all series converge absolutely because the $y_j$ are bounded.
- **(d)** If $v\le1$ then $|\Lambda(v)|\le1/e$. If $v>1$ then $0\le\Lambda(v)\le m_+^d\log(m_+^d)\le d\ell_0m_+^d$, using $\log m_+\le\ell_0$ (Lemma 1.4(e)). Finally, $1+d\ell_0m_+^d\le(1+\ell_0)(1+d)m_+^d\le(1+\ell_0)(2m_+)^d$. ∎

**Lemma 1.2 (Poisson facts).** Let $N\sim\mathrm{Pois}(\lambda)$.
- **(a) Tilt.** For $\lambda\ge0$ and $\kappa>0$: $\mathrm{Pois}(\lambda\kappa)(k)=\mathrm{Pois}(\lambda)(k)\,e^{-\lambda(\kappa-1)}\kappa^k$.
- **(b) Superposition.** If $N_1\sim\mathrm{Pois}(a)$ and $N_2\sim\mathrm{Pois}(b)$ are independent, then $N_1+N_2\sim\mathrm{Pois}(a+b)$. Applied coordinatewise, this holds for product-Poisson fields.
- **(c) Moments.**
  - $\mathbb E\,y^N=e^{\lambda(y-1)}$ for $y\ge0$;
  - $\mathbb E[(1+N)^jy^N]\le e^{\lambda(2^jy-1)}$ for $j\in\mathbb N$, because $1+N\le2^N$;
  - $\mathbb E[Ny^N]=\lambda y\,e^{\lambda(y-1)}$;
  - $\mathbb P(N\ge1)\le\lambda$ and $\mathbb P(N\ge2)\le\lambda^2/2$;
  - $\mathbb E[(1+N)\mathbf 1_{N\ge1}]\le2\lambda$;
  - $\mathbb E|N-\lambda|\le\sqrt\lambda$.
- **(d) Splitting.** Let $I$ be finite and $(w_i)_{i\in I}$ a probability vector. Let $D\sim\mathrm{Pois}(r)$, and given $D$ let $Y_1,\dots,Y_D$ be i.i.d. with law $w$. Then the count vector $(\#\{j\le D:Y_j=i\})_{i\in I}$ has independent $\mathrm{Pois}(rw_i)$ coordinates. Concretely, for every $f:\mathbb N^I\to\mathbb R$ with $\sum_{D}\prod_i\mathrm{Pois}(rw_i)(D_i)|f(D)|<\infty$,
$$\sum_{d\ge0}\mathrm{Pois}(r)(d)\sum_{y\in I^d}\Bigl(\prod_{j=1}^dw_{y_j}\Bigr)f(\mathrm{count}(y))=\sum_{D\in\mathbb N^I}\prod_i\mathrm{Pois}(rw_i)(D_i)\,f(D).$$
- **(e) Rate coupling.** If $0\le r\le s$, $D_r\sim\mathrm{Pois}(r)$ and $D'\sim\mathrm{Pois}(s-r)$ are independent, then $D_r+D'\sim\mathrm{Pois}(s)$, and $\mathbb E[c^{D'}\mathbf 1_{D'\ge1}]\le(s-r)\,c\,e^{(s-r)(c-1)}$ for $c\ge1$.

*Proof.*
- (a) and (b) are direct computations; (b) is the binomial theorem.
- **(c)** The first and third identities are direct; the second follows from $1+N\le2^N$. The tail bounds follow from $1-e^{-\lambda}\le\lambda$ and $\sum_{k\ge2}\lambda^ke^{-\lambda}/k!\le\lambda^2/2$. Next, $(1+N)\mathbf 1_{N\ge1}\le2N$. Finally, $\mathbb E|N-\lambda|\le\sqrt{\mathrm{Var}N}$.
- **(d)** Group $y$ by $D=\mathrm{count}(y)$. The fibre has $d!/\prod_iD_i!$ elements, and
$$\mathrm{Pois}(r)(d)\frac{d!}{\prod D_i!}\prod_iw_i^{D_i}=\prod_ie^{-rw_i}\frac{(rw_i)^{D_i}}{D_i!}.$$
  Rearranging is legitimate because both sides converge absolutely.
- **(e)** $\mathbb E[c^{D'}\mathbf 1_{D'\ge1}]=e^{(s-r)(c-1)}-e^{-(s-r)}=e^{-(s-r)}(e^{(s-r)c}-1)\le(s-r)ce^{(s-r)(c-1)}$. ∎

**Lemma 1.3 (Bernoulli sets).** Let $|V|=n$.
- **(a) Union.** If $A\sim\mathrm{Bern}(a)^V$ and $W\sim\mathrm{Bern}(b)^V$ are independent, then $A\cup W\sim\mathrm{Bern}(1-(1-a)(1-b))^V$.
- **(b) Insertion.** Let $p\in[0,1)$, $W\sim\mathrm{Bern}(p)^V$, and $g:V\times2^V\to\mathbb R$. Then
$$\mathbb E\sum_{w\in W}g(w,W\setminus\{w\})=\frac p{1-p}\sum_{w\in V}\mathbb E\bigl[\mathbf 1_{w\notin W}\,g(w,W)\bigr].$$
- **(c)** Let $n\ge2$, $p\in(0,1)$, $W\sim\mathrm{Bern}(p)^V$, and $u\ne v$. Then
$$\mathbb E\Bigl[\frac{\mathbf 1_{v\in W}}{|W\setminus\{u\}|}\Bigr]\ge\frac{p}{1+np}.$$

*Proof.*
- **(a)** Coordinates are independent, and $\mathbb P(v\notin A\cup W)=(1-a)(1-b)$.
- **(b)** The map $(W,w)\mapsto(W\setminus\{w\},w)$ is a bijection from $\{(W,w):w\in W\}$ onto $\{(W',w):w\notin W'\}$, and $\mathrm B_p(W'\cup\{w\})=\frac p{1-p}\mathrm B_p(W')$.
- **(c)** On $\{v\in W\}$ we have $|W\setminus\{u\}|=1+B$ with $B=|W\setminus\{u,v\}|\sim\mathrm{Bin}(n-2,p)$, and $B$ is independent of $\mathbf 1_{v\in W}$. So the quantity equals $p\,\mathbb E[1/(1+B)]$. By Jensen for the convex map $y\mapsto1/(1+y)$, this is at least $p/(1+(n-2)p)\ge p/(1+np)$. ∎

**Lemma 1.4 (the matrix).** Let $\mu,\nu\in\Delta_q$, $\tau\in[q]^V$ and $|V|=n$.
- **(a)** $M$ is symmetric, its entries are $m_-$ (diagonal) and $m_+$ (off-diagonal), and every row sum is $q$.
- **(b)** $(M\mu)_c=1+qt(\mu_c-1/q)$ and $\mu^\top M\nu=1+qt\langle\mu-u,\nu-u\rangle$. Both lie in $[m_-,m_+]$, being convex combinations of entries. In particular $\mu^\top M\mu\le1$, because $t<0$.
- **(c)** $\sum_{(v,w)\in V^2}(M(\tau_v,\tau_w)-1)=tqn^2\|\lambda_\tau-u\|_2^2\in(-n^2,0]$, and $\sum_{v\in V}(M(\tau_v,c)-1)=tqn(\lambda_\tau(c)-1/q)$.
- **(d)** If $\sigma$ is uniform on $[q]^V$, then $\mathbb E\|\lambda_\sigma-u\|_2^2=\frac{q-1}{qn}$.
- **(e)** $m_-m_+<1$. Hence $\log m_+<\ell_0$, and $|\log M(a,b)|\le\ell_0$.
- **(f)** For $\phi(\tau):=n^{-2}\sum_{v,w}M(\tau_v,\tau_w)=1+tq\|\lambda_\tau-u\|^2$ we have $m_-\le\phi(\tau)\le1$.

*Proof.*
- **(a)** Clear from the definition.
- **(b)** $(M\mu)_c=\sum_b(1+t(q\mathbf 1[b=c]-1))\mu_b=1+t(q\mu_c-1)$. Then
$$\mu^\top M\nu=\sum_c\mu_c(1+t(q\nu_c-1))=1+tq(\langle\mu,\nu\rangle-1/q)=1+tq\langle\mu-u,\nu-u\rangle.$$
- **(c)** $\sum_{v,w}(M-1)=t\sum_{v,w}(q\mathbf 1[\tau_v=\tau_w]-1)=t(q\sum_cN_c^2-n^2)=tqn^2\|\lambda_\tau-u\|^2$, where $N_c=|\tau^{-1}(c)|$. This lies in $(-n^2,0]$ because $\|\lambda-u\|^2\le1-1/q$ and $|t|(q-1)<1$. The second identity is $t\sum_v(q\mathbf 1[\tau_v=c]-1)=t(qN_c-n)$.
- **(d)** $\mathbb E\|\lambda_\sigma-u\|^2=\sum_c\mathrm{Var}(N_c/n)=q\cdot\frac{(1/q)(1-1/q)}n$.
- **(e)** $(x+q-1)^2-xq^2=(x-1)(x-(q-1)^2)>0$ for $x\in(0,1)$.
- **(f)** $\phi\le1$ since $t<0$. Also $\|\lambda-u\|^2\le1-1/q$ gives $\phi\ge1+t(q-1)=\frac{xq}{x+q-1}=m_-$. ∎

**Lemma 1.5 (finite entropy calculus).** Let $\mu$ be a probability measure on $[q]^V$ and write $h=h_\mu$.
- For $S\subseteq V$ and $\xi\in[q]^S$ with $\mu(\tau_S=\xi)>0$, let $\mu^{\xi}=\mu(\cdot\mid\tau_S=\xi)$.
- Define the conditional entropy $H(\tau_B\mid\tau_S):=h(B\cup S)-h(S)$.
- Define the conditional mutual information
$$I(\tau_A;\tau_B\mid\tau_S):=h(A\cup S)+h(B\cup S)-h(A\cup B\cup S)-h(S),$$
  and $I(\tau_A;\tau_B):=I(\tau_A;\tau_B\mid\tau_\emptyset)$.

Then:
- **(E1)** $h(\emptyset)=0$ and $0\le h(S)\le|S|\log q$.
- **(E2) Pin averaging.** $\sum_{\xi}\mu(\tau_S=\xi)\,H_{\mu^\xi}(\tau_B)=h(B\cup S)-h(S)$, where $H_{\mu^\xi}$ is entropy under $\mu^\xi$. Consequently
$$\sum_\xi\mu(\tau_S=\xi)\,I_{\mu^\xi}(\tau_A;\tau_B)=I_\mu(\tau_A;\tau_B\mid\tau_S)\qquad\text{for all }A,B\subseteq V.$$
- **(E3)** $h$ is monotone and submodular: $h(S\cup T)+h(S\cap T)\le h(S)+h(T)$. In particular $H(\tau_B\mid\tau_S)\ge H(\tau_B\mid\tau_{S'})$ for $S\subseteq S'$, and $I(\tau_A;\tau_B\mid\tau_S)\ge0$.
- **(E4)** $I(\tau_A;\tau_B)=D(\mu_{A\cup B}\,\|\,\mu_A\otimes\mu_B)$ when $A\cap B=\emptyset$. Here $\mu_A$ is the law of $\tau_A$ and $D$ the Kullback–Leibler divergence.
- **(E5) Monotonicity in the second argument.** If $B\subseteq B'$, then $I(\tau_A;\tau_B\mid\tau_S)\le I(\tau_A;\tau_{B'}\mid\tau_S)$.
- **(E6)** For every $w\in V$ and $W,S\subseteq V$: $I(\tau_w;\tau_W\mid\tau_S)=H(\tau_w\mid\tau_S)-H(\tau_w\mid\tau_{S\cup W})$.

*Proof.*
- **(E1)** Standard: $-y\log y\ge0$ on $[0,1]$, and the uniform law maximizes entropy, by concavity of $y\mapsto-y\log y$ and Jensen.
- **(E2)** Chain rule. Writing $\mu(\xi)=\mu(\tau_S=\xi)$ and $P(\zeta,\xi)=\mu(\tau_{B\setminus S}=\zeta,\tau_S=\xi)$, we have $-\sum_{\zeta,\xi}P\log P=-\sum_\xi\mu(\xi)\log\mu(\xi)-\sum_\xi\mu(\xi)\sum_\zeta\frac{P}{\mu(\xi)}\log\frac P{\mu(\xi)}$. Coordinates of $B\cap S$ are deterministic under $\mu^\xi$. Apply this to $A$, $B$ and $A\cup B$ and take the alternating sum to get the statement for $I$.
- **(E3)** By (E2), $h(S\cup T)-h(S)=\sum_\xi\mu(\tau_S=\xi)H_{\mu^\xi}(\tau_{T\setminus S})$ and $h(T)-h(S\cap T)=\sum_\zeta\mu(\tau_{S\cap T}=\zeta)H_{\mu^\zeta}(\tau_{T\setminus S})$. For fixed $\zeta$, the law of $\tau_{T\setminus S}$ under $\mu^\zeta$ is the mixture, over the $\xi$ extending $\zeta$, of its laws under $\mu^\xi$, with weights $\mu(\tau_S=\xi)/\mu(\tau_{S\cap T}=\zeta)$. Entropy is concave because $-y\log y$ is concave, so $H_{\mu^\zeta}\ge$ the weighted average of the $H_{\mu^\xi}$. This gives submodularity. Monotonicity is (E2) with $H\ge0$. Next, $I\ge0$ is submodularity applied to $A\cup S$ and $B\cup S$, together with monotonicity $h((A\cap B)\cup S)\ge h(S)$.
- **(E4)** Direct computation.
- **(E5)** The difference is $h(B'\cup S)-h(B\cup S)-h(A\cup B'\cup S)+h(A\cup B\cup S)=I(\tau_A;\tau_{B'}\mid\tau_{B\cup S})\ge0$.
- **(E6)** Expand both sides. If $w\in W$, both sides equal $H(\tau_w\mid\tau_S)$. ∎

**Lemma 1.6 (L¹ versus KL).** Let $p$ and $p'$ be probability vectors on a finite set with $p\ll p'$. Then $\sum|p-p'|\le2\sqrt{D(p\|p')}$.

*Proof.*
- For $a\ge0$ and $b>0$ we have $a\log(a/b)-a+b\ge(\sqrt a-\sqrt b)^2$. For $a>0$, put $y=\sqrt{b/a}$; the claim becomes $-2\log y\ge2-2y$, which is $\log y\le y-1$. The case $a=0$ is trivial.
- Summing and using $\sum p=\sum p'$ gives $\sum(\sqrt p-\sqrt{p'})^2\le D(p\|p')$.
- By Cauchy–Schwarz,
$$\sum|p-p'|=\sum|\sqrt p-\sqrt{p'}|(\sqrt p+\sqrt{p'})\le\sqrt{D}\sqrt{\sum(\sqrt p+\sqrt{p'})^2}\le\sqrt D\sqrt{2\sum(p+p')}=2\sqrt D.\ \ ∎$$

**Lemma 1.7 (decorrelation).** Let $\mu$ be a probability measure on $[q]^V$.
- **(a) Covariance.** Let $X=\tau_A$ and $Y=\tau_B$ with $A\cap B=\emptyset$, and let $F$ be any bounded function of $(X,Y)$. Write $\mu_X,\mu_Y$ for the laws of $X,Y$ under $\mu$. Then
$$\Bigl|\langle F(X,Y)\rangle_\mu-\sum_{x,y}\mu_X(x)\mu_Y(y)F(x,y)\Bigr|\le2\|F\|_\infty\sqrt{I_\mu(X;Y)}.$$
  In particular, for bounded $g$ and $f$: $|\langle g(X)f(Y)\rangle_\mu-\langle g(X)\rangle_\mu\langle f(Y)\rangle_\mu|\le2\|g\|_\infty\|f\|_\infty\sqrt{I_\mu(X;Y)}$.
- **(b) Products.** Let $W\subseteq V$ be finite and $f_w:[q]\to[0,b]$ for $w\in W$. Then
$$\Bigl|\Bigl\langle\prod_{w\in W}f_w(\tau_w)\Bigr\rangle_\mu-\prod_{w\in W}\langle f_w(\tau_w)\rangle_\mu\Bigr|\le2b^{|W|}\sum_{w\in W}\sqrt{I_\mu(\tau_w;\tau_{W\setminus w})}.$$
- **(c) Pairs.** For $v\ne w$: $|\langle M(\tau_v,\tau_w)\rangle_\mu-\mu_v^\top M\mu_w|\le2m_+\sqrt{I_\mu(\tau_v;\tau_w)}$.

*Proof.*
- **(a)** The left side is $|\sum_{x,y}F(x,y)(\mu_{XY}(x,y)-\mu_X(x)\mu_Y(y))|\le\|F\|_\infty\sum|\mu_{XY}-\mu_X\otimes\mu_Y|$. Apply Lemma 1.6 and (E4). The product case is $F(x,y)=g(x)f(y)$, for which $\|F\|_\infty\le\|g\|_\infty\|f\|_\infty$ and the second sum is $\langle g(X)\rangle_\mu\langle f(Y)\rangle_\mu$.
- **(b)** Order $W=\{w_1,\dots,w_k\}$, put $f_i=f_{w_i}(\tau_{w_i})$ and $P_j=\langle\prod_{i\le j}f_i\rangle$, so $P_0=1$. Telescoping,
$$P_k-\prod_{i\le k}\langle f_i\rangle=\sum_{j=1}^k\bigl(P_j-P_{j-1}\langle f_j\rangle\bigr)\prod_{i>j}\langle f_i\rangle .$$
  The bracket is a covariance of the product form, with $\|\prod_{i<j}f_i\|_\infty\le b^{j-1}$ and $\|f_j\|_\infty\le b$. By (a) and (E5), it is at most $2b^j\sqrt{I(\tau_{w_j};\tau_{w_{<j}})}\le2b^j\sqrt{I(\tau_{w_j};\tau_{W\setminus w_j})}$. Finally $\prod_{i>j}\langle f_i\rangle\le b^{k-j}$.
- **(c)** Apply (a) with $A=\{v\}$, $B=\{w\}$ and $F(a,b)=M(a,b)$, which is not of product form; $\|M\|_\infty=m_+$. The second sum in (a) is $\sum_{a,b}\mu_v(a)M(a,b)\mu_w(b)=\mu_v^\top M\mu_w$. ∎

---

## 2. The Bethe functional at empirical laws; rate change; mean fixing

Throughout this section $s>0$ and $q,x$ are fixed, and $\nu$ ranges over finitely supported probability measures on $\Delta_q$ (Fact 0.2).

**Lemma 2.1 (Poisson splitting for empirical laws).** Let $\mu$ be a probability measure on $[q]^V$ with $|V|=n$, and let $r\ge0$. For $D\in\mathbb N^V$ put
$$Y_\mu(D):=\frac1q\sum_{c\in[q]}\prod_{v\in V}(M\mu_v)_c^{D_v}.$$
Then
- **(a)** $\displaystyle\mathrm{BV}_r(\rho_\mu)=\sum_{D\in\mathbb N^V}\Bigl(\prod_{v}\mathrm{Pois}(r/n)(D_v)\Bigr)\Lambda\bigl(Y_\mu(D)\bigr)$, with absolute convergence;
- **(b)** $\displaystyle\mathrm{BE}(\rho_\mu)=\frac1{n^2}\sum_{(v,w)\in V^2}\Lambda(\mu_v^\top M\mu_w)$.

*Proof.* Apply Fact 0.2 to $\rho_\mu=\sum_v\frac1n\delta_{\mu_v}$ (atoms may repeat):
$$\int\Lambda(\mathcal V_d)\,d\rho_\mu^{\otimes d}=n^{-d}\sum_{y\in V^d}\Lambda\bigl(\mathcal V_d(\mu_{y_1},\dots,\mu_{y_d})\bigr),\qquad \mathcal V_d(\mu_{y_1},\dots,\mu_{y_d})=Y_\mu(\mathrm{count}(y)).$$
Now apply Lemma 1.2(d) with $I=V$ and uniform $w$. For absolute convergence: $Y_\mu(D)\in[m_-^{|D|},m_+^{|D|}]$ by Lemma 1.4(b), so $|\Lambda(Y_\mu(D))|\le(1+\ell_0)c_1^{|D|}$ by Lemma 1.1(d), and $\sum_D\prod_v\mathrm{Pois}(r/n)(D_v)c_1^{|D|}=e^{r(c_1-1)}$. Part (b) is Fact 0.2. ∎

**Lemma 2.2 (rate change).** For $0\le r\le s$ and every finitely supported $\nu$,
$$|\Psi_s(\nu)-\Psi_r(\nu)|\le C_{\rm rate}(s-r),\qquad C_{\rm rate}:=2(1+\ell_0)c_1e^{s(c_1-1)}+\tfrac12(1+\ell_0m_+).$$

*Proof.*
- **Vertex part.** Put $g_d=\int\Lambda(\mathcal V_d)\,d\nu^{\otimes d}$, so $|g_d|\le(1+\ell_0)c_1^d$ (Lemma 1.1(d)). With $D_r$ and $D'$ as in Lemma 1.2(e), $\mathrm{BV}_s(\nu)-\mathrm{BV}_r(\nu)=\mathbb E[g_{D_r+D'}-g_{D_r}]$. The difference vanishes unless $D'\ge1$, and then it is at most $2(1+\ell_0)c_1^{D_r+D'}$ in absolute value. By independence and Lemma 1.2(c),(e), its expectation is at most $2(1+\ell_0)e^{r(c_1-1)}(s-r)c_1e^{(s-r)(c_1-1)}$.
- **Edge part.** It changes by $\frac{s-r}2|\mathrm{BE}(\nu)|\le\frac{s-r}2(1+\ell_0m_+)$, by Lemma 1.1(d), since $\mathcal E\in[m_-,m_+]$. ∎

**Lemma 2.3 (mean fixing).** Let $\nu=\sum_jw_j\delta_{\mu^{(j)}}$ have mean $\bar m=\sum_jw_j\mu^{(j)}$, and put $\alpha:=\min\{1,q\|\bar m-u\|_\infty\}$.
- If $\alpha=0$, put $\nu':=\nu$.
- If $\alpha>0$, put $\zeta:=(u-(1-\alpha)\bar m)/\alpha$ and $\nu':=(1-\alpha)\nu+\alpha\,\delta_\zeta$.

Then: if $\alpha>0$, $\zeta\in\Delta_q$; in both cases $\nu'$ is finitely supported (with at most one atom more than $\nu$), $\nu'\in\mathcal P_u$, and for every $0\le r\le s$
$$|\Psi_r(\nu')-\Psi_r(\nu)|\le C_{\rm mf}\,\alpha,\qquad C_{\rm mf}:=2(1+\ell_0)sc_1e^{s(c_1-1)}+2s(1+\ell_0m_+).$$

*Proof.* If $\alpha=0$ then $\bar m=u$, $\nu'=\nu\in\mathcal P_u$ and there is nothing to prove; assume $\alpha>0$.
- **$\zeta$ is a probability vector.** Its coordinates sum to $(1-(1-\alpha))/\alpha=1$. If $\alpha=1$ then $\zeta=u$. If $\alpha<1$ then $\alpha=q\|\bar m-u\|_\infty$, so $\bar m_c\le(1+\alpha)/q$ and $(1-\alpha)\bar m_c\le(1-\alpha^2)/q\le1/q$, i.e. $\zeta_c\ge0$.
- **Mean.** The mean of $\nu'$ is $(1-\alpha)\bar m+\alpha\zeta=u$.
- **Coupling.** Let $\mu_1,\mu_2,\dots$ be i.i.d. with law $\nu$, let $B_1,B_2,\ldots$ be i.i.d. $\mathrm{Bern}(\alpha)$, independent of the $\mu_i$, and set $\mu_i'=\zeta$ if $B_i=1$ and $\mu_i'=\mu_i$ otherwise. Then the $\mu'_i$ are i.i.d. with law $\nu'$.
- **Vertex part.** For each $d$, the two integrals of $\Lambda(\mathcal V_d)$ differ by at most $2(1+\ell_0)c_1^d\,\mathbb P(\exists i\le d:B_i=1)\le2(1+\ell_0)c_1^d\,d\alpha$. Summing against $\mathrm{Pois}(r)$ and using $\mathbb E[Dc_1^D]=rc_1e^{r(c_1-1)}$ with $r\le s$ gives the first term of $C_{\rm mf}$.
- **Edge part.** The integrals of $\Lambda(\mathcal E)$ differ by at most $2(1+\ell_0m_+)\,\mathbb P(B_1=1\text{ or }B_2=1)\le4(1+\ell_0m_+)\alpha$, and this is multiplied by $r/2\le s/2$. ∎

---

## 3. Literal form versus planted Poisson form

Fix $n\ge2$ and use the vertex set $[n]$.
- **Edge law.** For $\sigma\in[q]^n$, the single-edge law is $p_\sigma(v,w):=M(\sigma_v,\sigma_w)/(n^2\phi(\sigma))$ on $[n]^2$, where $\phi$ is as in Lemma 1.4(f). The list law is $P_{\sigma,m}:=p_\sigma^{\otimes m}$ on $([n]^2)^m$.
- **The function $g$.** $g(\sigma,m):=\sum_eP_{\sigma,m}(e)\log F_e$.
- **Tilted colouring law.** $\nu_m(\sigma):=\phi(\sigma)^m/\sum_{\sigma'}\phi(\sigma')^m$.
- **Planted Poisson law.** $\mathsf P^\sigma_\varrho:=\bigotimes_{e\in[n]^2}\mathrm{Pois}(\varrho M_e(\sigma))$ on $\mathbb N^{[n]^2}$.
- **Partition function of a multigraph.** For $G\in\mathbb N^{[n]^2}$, $F_G=q^{-n}\sum_\tau w_G(\tau)$. Thus $F_{\mathrm{count}(e)}=F_e$, where $\mathrm{count}(e)_c=\#\{j:e_j=c\}$.
- **The two averages.**
$$f^{\rm lit}_n:=\sum_{m\ge0}\mathrm{Pois}(sn/2)(m)\,\bar c_m(n),\qquad
\bar f_n:=q^{-n}\sum_{\sigma}\sum_{G}\mathsf P^\sigma_{s/(2n)}(G)\log F_G .$$

**Lemma 3.1 (two representations).**
- **(a)** $F_e\in[m_-^m,m_+^m]$, so $|\log F_e|\le m\ell_0$, $|g(\sigma,m)|\le m\ell_0$ and $|\bar c_m|\le m\ell_0$. Hence $f^{\rm lit}_n$ and all series below converge absolutely.
- **(b)** $\bar c_m=\sum_\sigma\nu_m(\sigma)\,g(\sigma,m)$.
- **(c)** $\bar f_n=q^{-n}\sum_\sigma\sum_{m\ge0}\mathrm{Pois}(sn\phi(\sigma)/2)(m)\,g(\sigma,m)$.
- **(d)** $\nu_m(\sigma)\le q^{-n}(1-1/n)^{-m}$.

*Proof.*
- **(a)** Each product $\prod_jM(\cdot)$ lies in $[m_-^m,m_+^m]$; $\bar c_m$ is an average of the $\log F_e$; and $\log m_+\le\ell_0$.
- **(b)** We have $\sum_{e}\prod_jM(\sigma_{e_j^1},\sigma_{e_j^2})=(n^2\phi(\sigma))^m$. Hence
$$\sum_eF_e\log F_e=q^{-n}\sum_\sigma(n^2\phi(\sigma))^m g(\sigma,m),\qquad \sum_eF_e=q^{-n}\sum_\sigma(n^2\phi(\sigma))^m .$$
  Divide.
- **(c)** Apply Lemma 1.2(d) with $I=[n]^2$, total rate $r=\frac s{2n}n^2\phi(\sigma)$ and weights $w=p_\sigma$, so that $rw_e=\frac s{2n}M_e(\sigma)$. Use $f(D)=\log F_D$, for which $|f(D)|\le|D|\ell_0$ gives absolute convergence, and $F_{\mathrm{count}(e)}=F_e$.
- **(d)** By Jensen for $y\mapsto y^m$ and Lemma 1.4(d),
$$q^{-n}\sum_\sigma\phi(\sigma)^m\ge\Bigl(1+tq\,\tfrac{q-1}{qn}\Bigr)^m\ge(1-1/n)^m,$$
  since $|t|(q-1)<1$. Moreover $\phi\le1$. ∎

**Lemma 3.2 (regularity of $g$).** Let $\sigma,\sigma'\in[q]^n$ and $m\ge0$.
- **(a)** $|g(\sigma,m+1)-g(\sigma,m)|\le\ell_0$.
- **(b)** $g(\sigma\circ\pi,m)=g(\sigma,m)$ for every permutation $\pi$ of $[n]$.
- **(c)** If $\sigma$ and $\sigma'$ differ in exactly $d$ vertices, then $|g(\sigma,m)-g(\sigma',m)|\le4\ell_0\theta\,md/(nm_-)$.
- **(d)** $|g(\sigma,m)-g(\sigma',m)|\le L_1\,m\,\|\lambda_\sigma-\lambda_{\sigma'}\|_1$ with $L_1:=2\ell_0\theta/m_-$.

*Proof.*
- **(a)** For a list $e$ and an extra edge $f$, $F_{(e,f)}=F_e\langle M_f\rangle_{\mu_e}$, where $\mu_e(\tau)\propto\prod_jM(\tau_{e_j^1},\tau_{e_j^2})$. Since $\langle M_f\rangle\in[m_-,m_+]$, we get $|\log F_{(e,f)}-\log F_e|\le\ell_0$. Since $P_{\sigma,m+1}=P_{\sigma,m}\otimes p_\sigma$, it follows that $g(\sigma,m+1)-g(\sigma,m)=\mathbb E[\log F_{(e,f)}-\log F_e]$.
- **(b)** Write $\pi\circ e$ for the list with entries $(\pi(e_j^1),\pi(e_j^2))$. Substituting $\tau\mapsto\tau\circ\pi$ gives $F_{\pi\circ e}=F_e$. Also $\phi(\sigma\circ\pi)=\phi(\sigma)$ and $P_{\sigma\circ\pi,m}(e)=P_{\sigma,m}(\pi\circ e)$. Reindex the sum by $e\mapsto\pi\circ e$.
- **(c)**
  - *One replaced edge.* Replacing one entry of a list changes $\log F$ by at most $2\ell_0$: remove it, then add the new one, each step as in (a).
  - *Total variation.* Let $\Delta$ be the set where $\sigma\ne\sigma'$. Then
$$\sum_{(v,w)}|p_\sigma-p_{\sigma'}|\le\sum\frac{|M_{vw}(\sigma)-M_{vw}(\sigma')|}{n^2\phi(\sigma)}+\frac{|\phi(\sigma)-\phi(\sigma')|}{\phi(\sigma)}.$$
    Only the at most $2dn$ pairs meeting $\Delta$ contribute, each by at most $\theta$, and $\phi\ge m_-$. Hence both terms are at most $2d\theta/(nm_-)$, and $\mathrm{TV}(p_\sigma,p_{\sigma'})\le2d\theta/(nm_-)$.
  - *Coupling.* Couple $e\sim P_{\sigma,m}$ and $e'\sim P_{\sigma',m}$ coordinatewise by maximal couplings: put mass $\min(p_\sigma,p_{\sigma'})$ on the diagonal. Then $\mathbb E\#\{j:e_j\ne e'_j\}=m\,\mathrm{TV}$, and $|g(\sigma,m)-g(\sigma',m)|\le2\ell_0m\,\mathrm{TV}$.
- **(d)** Let $N_c$ and $N'_c$ be the colour counts. Match, for each $c$, $\min(N_c,N'_c)$ vertices of $\sigma'^{-1}(c)$ bijectively with vertices of $\sigma^{-1}(c)$, and extend to a permutation $\pi$. Then $\sigma\circ\pi$ and $\sigma'$ differ in $d=n-\sum_c\min(N_c,N'_c)=\frac n2\|\lambda_\sigma-\lambda_{\sigma'}\|_1$ vertices. Apply (b), then (c). ∎

**Lemma 3.3 (literal versus planted average).** For $n\ge2$,
$$|f^{\rm lit}_n-\bar f_n|\le C_{\rm br}\sqrt n,\qquad C_{\rm br}:=L_1\bigl(2se^s\sqrt q+qs\bigr)+\ell_0\bigl(2\sqrt s+s+2\bigr).$$

*Proof.*
- **Two laws.** By Lemma 3.1(b),(c), $f^{\rm lit}_n$ and $\bar f_n$ are the expectations of $g$ under two probability laws on $[q]^n\times\mathbb N$:
$$\mathsf P_{\rm lit}(\sigma,m)=\mathrm{Pois}(sn/2)(m)\,\nu_m(\sigma),\qquad \mathsf P_{\rm pl}(\sigma,m)=q^{-n}\,\mathrm{Pois}(sn\phi(\sigma)/2)(m).$$
- **Reference value.** Fix $\sigma_0$ with $\|\lambda_{\sigma_0}-u\|_1\le q/n$ (colour classes of sizes $\lfloor n/q\rfloor$ or $\lceil n/q\rceil$) and $m_0=\lfloor sn/2\rfloor$. Put $\bar g=g(\sigma_0,m_0)$. By Lemma 3.2(a),(d),
$$|g(\sigma,m)-\bar g|\le L_1m\bigl(\|\lambda_\sigma-u\|_1+q/n\bigr)+\ell_0|m-m_0|,$$
  and $|f^{\rm lit}_n-\bar f_n|\le\mathbb E_{\rm lit}|g-\bar g|+\mathbb E_{\rm pl}|g-\bar g|$.
- **Moments of $\|\lambda_\sigma-u\|_1$.** By Lemma 1.4(d) and Cauchy–Schwarz, $\mathbb E_\sigma\|\lambda_\sigma-u\|_1\le\sqrt q\sqrt{(q-1)/(qn)}\le\sqrt{q/n}$ for uniform $\sigma$.
- **Under $\mathsf P_{\rm pl}$.**
  - $\mathbb E[m\|\lambda_\sigma-u\|_1]=\mathbb E_\sigma[\frac{sn\phi}2\|\lambda_\sigma-u\|_1]\le\frac s2\sqrt{qn}$.
  - $\mathbb E[m]q/n\le sq/2$.
  - $\mathbb E|m-m_0|\le\sqrt{sn/2}+\frac{sn}2\mathbb E_\sigma(1-\phi)+1\le\sqrt{sn/2}+\frac s2+1$, because $1-\phi=|t|q\|\lambda-u\|^2$ has mean $|t|(q-1)/n<1/n$.
- **Under $\mathsf P_{\rm lit}$.** By Lemma 3.1(d) and Lemma 1.2(c), with $y=n/(n-1)\le2$ and $\frac{sn}2(y-1)\le s$,
$$\mathbb E[m\|\lambda_\sigma-u\|_1]\le\sum_m\mathrm{Pois}(\tfrac{sn}2)(m)\,m\,y^m\sqrt{q/n}=\tfrac{sn}2\,y\,e^{\frac{sn}2(y-1)}\sqrt{q/n}\le se^s\sqrt{qn}.$$
  Moreover $\mathbb E[m]q/n=sq/2$ and $\mathbb E|m-m_0|\le\sqrt{sn/2}+1$.
- **Conclusion.** Adding up, and using $\sqrt n\ge1$, gives the claim. ∎

**Remark 3.4.** A comparison of $f^{\rm lit}_n$ and $\bar f_n$ through the density $e^{\kappa_s(\sigma)}/\bar a_m$ of $\mathsf P_{\rm lit}$ with respect to $\mathsf P_{\rm pl}$, where $\kappa_s(\sigma)=\frac{sn}2(\phi(\sigma)-1)$ and $\bar a_m=q^{-n}\sum_\sigma\phi(\sigma)^m$, would be combined with $\mathrm{Var}(\log F)=O(n)$; the latter needs a concentration inequality, such as Lemma C.6 of the paper. Lemma 3.3 avoids it. Both $f^{\rm lit}_n$ and $\bar f_n$ are expectations of the same function $g(\sigma,m)$ of the colouring and the edge count, so only the regularity of $g$ in $(\sigma,m)$ is needed, and that is deterministic (Lemma 3.2).

---

## 4. The planted triple law and the Nishimori identities

**Definition 4.1.** Let $V$ be finite with $n=|V|\ge1$, let $\varrho\ge0$ and $\pi\in[0,1]^V$.
- **Null and planted laws.** $\mathsf P_\varrho:=\bigotimes_{e\in V\times V}\mathrm{Pois}(\varrho)$ (null) and $\mathsf P^\tau_\varrho:=\bigotimes_{e}\mathrm{Pois}(\varrho M_e(\tau))$ (planted), on $\mathbb N^{V\times V}$.
- **Likelihood ratio.** By Lemma 1.2(a),
$$L_\varrho(G,\tau):=\frac{\mathsf P^\tau_\varrho(G)}{\mathsf P_\varrho(G)}=e^{-\varrho S(\tau)}w_G(\tau),\qquad S(\tau):=\sum_{e\in V\times V}(M_e(\tau)-1)=tqn^2\|\lambda_\tau-u\|_2^2\in(-n^2,0].$$
- **Planted triple law.** $\mathsf Q=\mathsf Q_{V,\varrho,\pi}$ is the probability on $[q]^V\times\mathbb N^{V\times V}\times2^V$ given by
$$\mathsf Q(\sigma,G,U)=q^{-n}\,\mathsf P^\sigma_\varrho(G)\,\mathrm B_\pi(U).$$
  In words: $\sigma$ is uniform; given $\sigma$, $G\sim\mathsf P^\sigma_\varrho$; and $U\sim\mathrm{Bern}(\pi)^V$ independently. The *observation* is $(G,U,\sigma_U)$.
- **Pinned partition function and posterior.** For $\varsigma\in[q]^V$ and $U\subseteq V$,
$$\tilde F_\varrho(G,U,\varsigma):=q^{-n}\sum_{\tau:\tau_U=\varsigma_U}L_\varrho(G,\tau),\qquad
\mathrm{post}_{G,U,\varsigma}(\tau):=\frac{\mathbf 1[\tau_U=\varsigma_U]\,L_\varrho(G,\tau)}{q^n\tilde F_\varrho(G,U,\varsigma)} .$$
  The unpinned posterior is $\mu_G:=\mathrm{post}_{G,\emptyset,\cdot}\propto L_\varrho(G,\cdot)$, so $\mathrm{post}_{G,U,\varsigma}=\mu_G(\cdot\mid\tau_U=\varsigma_U)$.
- **Pinned planted free energy.** $\mathcal K_V(\varrho,\pi):=\mathbb E_{\mathsf Q}\log\tilde F_\varrho(G,U,\sigma)$.
- When $\varrho$ must be shown, we write $\mathrm{post}^\varrho$.

**Lemma 4.2 (bounds).**
- **(a)** $L_\varrho(G,\tau)\in[m_-^{|G|},e^{\varrho n^2}m_+^{|G|}]$, and $L_\varrho(G,\tau)\ge w_G(\tau)$.
- **(b)** $|\log\tilde F_\varrho(G,U,\varsigma)|\le n\log q+\varrho n^2+|G|\ell_0$.
- **(c)** For $c\ge1$, $\mathbb E_{\mathsf Q}c^{|G|}\le e^{\varrho n^2m_+(c-1)}$; in particular $\mathbb E_{\mathsf Q}|G|\le\varrho n^2m_+$.

Hence $\mathcal K_V$ is finite, and every function bounded by $C\,c^{|G|}$ is $\mathsf Q$-integrable.

*Proof.*
- **(a)** We have $-\varrho S\in[0,\varrho n^2)$ and $w_G\in[m_-^{|G|},m_+^{|G|}]$.
- **(b)** The term $\tau=\varsigma$ gives $\tilde F\ge q^{-n}m_-^{|G|}$, and $\tilde F\le\max_\tau L\le e^{\varrho n^2}m_+^{|G|}$.
- **(c)** Lemma 1.2(c), coordinatewise, using $M_e\le m_+$. ∎

**Lemma 4.3 (exact Nishimori identity).** Let $f(\tau,G,U,\varsigma)$ be a real number defined for every $(\tau,G,U,\varsigma)$ with $\tau_U=\varsigma_U$ (no value is needed elsewhere; it may be undefined, e.g. $\log0$, there). Assume that $f$ depends on $\varsigma$ only through $\varsigma_U$ and that $\mathbb E_{\mathsf Q}|f(\sigma,G,U,\sigma)|<\infty$. Then
$$\mathbb E_{\mathsf Q}f(\sigma,G,U,\sigma)=\mathbb E_{\mathsf Q}\sum_{\tau:\,\tau_U=\sigma_U}\mathrm{post}_{G,U,\sigma}(\tau)\,f(\tau,G,U,\sigma),$$
and the right side converges absolutely. (Since $\mathrm{post}_{G,U,\sigma}(\tau)=0$ unless $\tau_U=\sigma_U$, the right side is $\mathbb E_{\mathsf Q}\langle f(\cdot,G,U,\sigma)\rangle_{\mathrm{post}_{G,U,\sigma}}$ whenever $f$ is defined everywhere.)

*Proof.*
- Put $Z_\xi(G,U):=\sum_{\tau:\tau_U=\xi}L_\varrho(G,\tau)$ for $\xi\in[q]^U$. Since $\mathsf P^\sigma_\varrho(G)=\mathsf P_\varrho(G)L_\varrho(G,\sigma)$, the right side equals
$$\sum_{G,U}q^{-n}\mathsf P_\varrho(G)\mathrm B_\pi(U)\sum_\sigma L_\varrho(G,\sigma)\sum_{\tau:\tau_U=\sigma_U}\frac{L_\varrho(G,\tau)f(\tau,G,U,\sigma)}{Z_{\sigma_U}(G,U)} .$$
  Only values of $f$ with $\tau_U=\sigma_U$ occur.
- The inner expression depends on $\sigma$ only through $\xi=\sigma_U$, and $\sum_{\sigma:\sigma_U=\xi}L_\varrho(G,\sigma)=Z_\xi$. The sum therefore equals
$$\sum_{G,U}q^{-n}\mathsf P_\varrho(G)\mathrm B_\pi(U)\sum_\tau L_\varrho(G,\tau)f(\tau,G,U,\tau)=\mathbb E_{\mathsf Q}f(\sigma,G,U,\sigma).$$
  Here $f(\tau,G,U,\sigma)=f(\tau,G,U,\tau)$ because $\sigma_U=\tau_U$.
- The same computation with $|f|$, in which all terms are nonnegative so that rearrangement is free (Tonelli), shows absolute convergence. ∎

**Lemma 4.4 (consequences).**
- **(a) Law of the observation; pin averaging.** Under $\mathsf Q$, the pair $(G,U)$ has law $\bar{\mathsf P}_\varrho(G)\mathrm B_\pi(U)$, where $\bar{\mathsf P}_\varrho(G)=q^{-n}\sum_\sigma\mathsf P^\sigma_\varrho(G)$. Given $(G,U)$, the pins $\sigma_U$ have the law $\mu_G(\tau_U=\cdot)$. Consequently, for every functional $\Upsilon$ of probability measures on $[q]^V$ with $\mathbb E_{\mathsf Q}|\Upsilon(\mathrm{post})|<\infty$,
$$\mathbb E_{\mathsf Q}\Upsilon(\mathrm{post}_{G,U,\sigma})=\sum_{G,U}\bar{\mathsf P}_\varrho(G)\mathrm B_\pi(U)\sum_{\xi\in[q]^U}\mu_G(\tau_U=\xi)\,\Upsilon\bigl(\mu_G(\cdot\mid\tau_U=\xi)\bigr).$$
- **(b) Magnetization.** $\mathbb E_{\mathsf Q}\langle\|\lambda_\tau-u\|_2^2\rangle_{\mathrm{post}}=\frac{q-1}{qn}$. Hence $\mathbb E_{\mathsf Q}\,\mathrm{dev}(\mathrm{post})\le n^{-1/2}$ and $\mathbb E_{\mathsf Q}\|\bar m_{\mathrm{post}}-u\|_2\le n^{-1/2}$.
- **(c) Predictive law of an extra observation.** Let:
  - $\mathcal H$ be a countable set and $R^0$ a probability on $\mathcal H$;
  - $\ell:\mathcal H\times[q]^V\to(0,\infty)$ satisfy $\sum_hR^0(h)\ell(h,\tau)=1$ for every $\tau$;
  - given $(\sigma,G,U)\sim\mathsf Q$, the extra observation $h$ be drawn with law $R^\sigma(h)=R^0(h)\ell(h,\sigma)$.

  Let $\varphi(h,G,U,\varsigma)$ be real, depend on $\varsigma$ only through $\varsigma_U$, and be *dominated*: $|\varphi(h,G,U,\varsigma)|\le\Phi(h)$ for some $\Phi:\mathcal H\to[0,\infty)$ with
$$C_\Phi:=\max_{\tau\in[q]^V}\sum_hR^0(h)\ell(h,\tau)\Phi(h)<\infty .$$
  Then all series below converge absolutely, and
$$\mathbb E\,\varphi(h,G,U,\sigma)=\mathbb E_{\mathsf Q}\sum_{h\in\mathcal H}R^0(h)\,\langle\ell(h,\cdot)\rangle_{\mathrm{post}_{G,U,\sigma}}\,\varphi(h,G,U,\sigma).$$
  In words: given the observation, $h$ has law $R^0(h)\langle\ell(h,\cdot)\rangle_{\mathrm{post}}$. (The normalization $\sum_hR^0\ell=1$ is needed only for this interpretation, not for the identity.) The three applications are dominated: $\Phi(H)=\delta n^2+|H|\ell_0$ in Lemma 5.1(b), $\Phi\equiv\sup_\mu\Xi_\delta(\mu)$ in Lemma 5.2(iii), and $\Phi=\Gamma$ in Lemma 7.1(iv); in each case $C_\Phi<\infty$ by the exponential moments of Lemma 1.2(c).

*Proof.*
- **(a)** We have $\mathsf Q(G,U,\sigma_U=\xi)=\mathrm B_\pi(U)q^{-n}\mathsf P_\varrho(G)Z_\xi(G,U)$. Also $\bar{\mathsf P}_\varrho(G)=q^{-n}\mathsf P_\varrho(G)\sum_\tau L_\varrho(G,\tau)$ and $\mu_G(\tau_U=\xi)=Z_\xi/\sum_\tau L_\varrho(G,\tau)$. Finally, $\mathrm{post}_{G,U,\sigma}=\mu_G(\cdot\mid\tau_U=\sigma_U)$.
- **(b)** Apply Lemma 4.3 to the bounded $f=\|\lambda_\sigma-u\|^2$, and use Lemma 1.4(d) for uniform $\sigma$. Then $\mathrm{dev}\le\langle\|\lambda-u\|^2\rangle^{1/2}$ and $\mathbb E\sqrt{\cdot}\le\sqrt{\mathbb E\,\cdot}$. Also $\|\bar m_\mu-u\|_2=\|\langle\lambda_\tau-u\rangle_\mu\|_2\le\mathrm{dev}(\mu)$, by convexity of the norm. Finally, $(q-1)/(qn)\le1/n$.
- **(c)** We have $\mathbb E\varphi=\mathbb E_{\mathsf Q}\sum_hR^0(h)\ell(h,\sigma)\varphi(h,G,U,\sigma)$. For **every** $\tau$ (not only $\tau=\sigma$) the series $f(\tau,G,U,\varsigma):=\sum_hR^0(h)\ell(h,\tau)\varphi(h,G,U,\varsigma)$ converges absolutely, with $|f|\le C_\Phi$, by domination. It depends on $\varsigma$ only through $\varsigma_U$. Apply Lemma 4.3 to this bounded $f$, and exchange the finite $\tau$-sum with the absolutely convergent $h$-sums. ∎

**Lemma 4.5 (domination).** For $n\ge1$, $\bar f_n\le\mathcal K_{[n]}(\tfrac s{2n},0)$.

*Proof.* With $\pi\equiv0$ we have $U=\emptyset$, and $\tilde F_\varrho(G,\emptyset,\cdot)=q^{-n}\sum_\tau L_\varrho(G,\tau)\ge q^{-n}\sum_\tau w_G(\tau)=F_G$ by Lemma 4.2(a). Both sides are expectations under the same law of $(\sigma,G)$. ∎

**Lemma 4.6 (pin cost).** Let $\pi,\pi_x\in[0,1]^V$ and define $\pi'$ by $1-\pi'_v=(1-\pi_v)(1-\pi_{x,v})$. Then
$$\mathcal K_V(\varrho,\pi)-\Bigl(\sum_v\pi_{x,v}\Bigr)\log q\ \le\ \mathcal K_V(\varrho,\pi')\ \le\ \mathcal K_V(\varrho,\pi).$$

*Proof.*
- **Realization.** Realize $U'\sim\mathrm{Bern}(\pi')^V$ as $U\cup X$, with $U\sim\mathrm{Bern}(\pi)^V$ and $X\sim\mathrm{Bern}(\pi_x)^V$ independent of each other and of $(\sigma,G)$ (Lemma 1.3(a)). Pointwise, $\tilde F(G,U\cup X,\sigma)=\tilde F(G,U,\sigma)\cdot\mathrm{post}_{G,U,\sigma}(\tau_X=\sigma_X)$. Therefore
$$\mathcal K(\pi')=\mathcal K(\pi)+\mathbb E\log\mathrm{post}_{G,U,\sigma}(\tau_X=\sigma_X).$$
- **Upper bound.** The posterior probability is at most $1$.
- **Lower bound.** Fix $X$ and apply Lemma 4.3 to $f(\tau,G,U,\varsigma)=\log\mathrm{post}_{G,U,\varsigma}(\tau'_X=\tau_X)$ (here $\tau'\sim\mathrm{post}_{G,U,\varsigma}$). This $f$ is needed, and is real, only where $\tau_U=\varsigma_U$: there $\mathrm{post}_{G,U,\varsigma}(\tau'_X=\tau_X)\ge\mathrm{post}_{G,U,\varsigma}(\tau)>0$. (Elsewhere it may equal $\log0$; Lemma 4.3 never uses those values.) It depends on $\varsigma$ only through $\varsigma_U$. Hence
$$\mathbb E_{\mathsf Q}f=\mathbb E_{\mathsf Q}\sum_{\tau:\tau_U=\sigma_U}\mathrm{post}(\tau)\log\mathrm{post}(\tau'_X=\tau_X)=-\mathbb E_{\mathsf Q}H_{\mathrm{post}}(\tau_X)\ge-|X|\log q .$$
  Then average over $X$.
- **Integrability.** $0\le-\log\mathrm{post}(\tau_X=\sigma_X)\le-\log\mathrm{post}(\sigma)\le n\log q+\varrho n^2+2|G|\ell_0$, by Lemma 4.2(a) and $\log(m_+/m_-)\le2\ell_0$. ∎

**Lemma 4.7 (relabelling).** For a bijection $\iota:V\to V'$, $\mathcal K_V(\varrho,\pi)=\mathcal K_{V'}(\varrho,\pi\circ\iota^{-1})$. *(Transport every object along $\iota$.)*

**Definition 4.8 (the pinned sequence).** For $N\ge1$ and $k\in\mathbb N$ put
$$\pi_k(N):=1-e^{-ks/N},\qquad a_N(k):=\mathcal K_{[N]}\Bigl(\frac s{2N},\pi_k(N)\Bigr).$$

**Corollary 4.9.**
- **(a)** $a_N(0)\le a_N(k)+ks\log q$.
- **(b)** $|a_N(k)|\le N\log q+\frac{sN}2(1+m_+\ell_0)$.

*Proof.* (a) Lemma 4.6 with $\pi=0$ and $\pi_x=\pi_k(N)\le ks/N$. (b) Lemma 4.2(b),(c) with $\varrho N^2=sN/2$. ∎

**Remark 4.10 (a converse bound; not used).** For $n\ge1$,
$$\bar f_n\ \ge\ \mathcal K_{[n]}\Bigl(\frac s{2n},0\Bigr)-\frac s2\,|t|(q-1)\ >\ \mathcal K_{[n]}\Bigl(\frac s{2n},0\Bigr)-\frac s2 .$$
So $\bar f_n$ and $\mathcal K_{[n]}(\frac s{2n},0)$ differ by at most $s/2$ (Lemma 4.5 gives the other side).

*Proof.* Put $\varrho=\frac s{2n}$ and let $\mu_G\propto L_\varrho(G,\cdot)$ be the unpinned posterior. Since $w_G=e^{\varrho S}L_\varrho(G,\cdot)$,
$$\frac{F_G}{\tilde F_\varrho(G,\emptyset,\cdot)}=\frac{\sum_\tau e^{\varrho S(\tau)}L_\varrho(G,\tau)}{\sum_\tau L_\varrho(G,\tau)}=\langle e^{\varrho S}\rangle_{\mu_G}\ge e^{\varrho\langle S\rangle_{\mu_G}}$$
by Jensen for $\exp$. Take logarithms and the expectation over $\sigma$ uniform and $G\sim\mathsf P^\sigma_\varrho$ (that is, $\mathsf Q$ with $\pi\equiv0$). Lemma 4.3 with the bounded $f=S(\tau)$ gives $\mathbb E\langle S\rangle_{\mu_G}=\mathbb E\,S(\sigma)=tqn^2\cdot\frac{q-1}{qn}=t(q-1)n$, by Lemma 1.4(c),(d). Hence $\bar f_n\ge\mathcal K_{[n]}(\varrho,0)+\varrho t(q-1)n=\mathcal K_{[n]}(\varrho,0)-\frac s2|t|(q-1)$, and $|t|(q-1)<1$. ∎

---

## 5. Superposition, convexity in the rate, and the edge term

Throughout, $V$ and $\pi$ are fixed and $n=|V|$. For $\delta\ge0$ and a probability measure $\mu$ on $[q]^V$ put
$$\Xi_\delta(\mu):=\sum_{H\in\mathbb N^{V\times V}}\mathsf P_\delta(H)\,\Lambda\bigl(\langle L_\delta(H,\cdot)\rangle_\mu\bigr).$$

**Lemma 5.1 (superposition).**
- **(a)** The series $\Xi_\delta(\mu)$ converges absolutely, $\Xi_\delta(\mu)=\sum_H\mathsf P_\delta(H)\,\mathrm{kl}(\langle L_\delta(H,\cdot)\rangle_\mu)\ge0$, and $\sup_\mu\Xi_\delta(\mu)<\infty$.
- **(b)** For $\varrho,\delta\ge0$,
$$\mathcal K_V(\varrho+\delta,\pi)=\mathcal K_V(\varrho,\pi)+\mathbb E_{\mathsf Q_{V,\varrho,\pi}}\Xi_\delta(\mathrm{post}_{G,U,\sigma}).$$

*Proof.*
- **(a)** By Lemma 4.2(a), $\langle L_\delta(H,\cdot)\rangle_\mu\in[m_-^{|H|},e^{\delta n^2}m_+^{|H|}]$, so $|\Lambda(\cdot)|\le1+(\delta n^2+|H|\ell_0)e^{\delta n^2}m_+^{|H|}$, uniformly in $\mu$. This is $\mathsf P_\delta$-summable by Lemma 1.2(c). Moreover $\sum_H\mathsf P_\delta(H)L_\delta(H,\tau)=\sum_H\mathsf P^\tau_\delta(H)=1$, so $\sum_H\mathsf P_\delta(H)\langle L_\delta(H)\rangle_\mu=1=\sum_H\mathsf P_\delta(H)$; subtract to get the $\mathrm{kl}$ form.
- **(b) Superposition.** Let $(\sigma,G,U)\sim\mathsf Q_{V,\varrho,\pi}$, and given these let $H\sim\mathsf P^\sigma_\delta$. By Lemma 1.2(b), $(\sigma,G+H,U)\sim\mathsf Q_{V,\varrho+\delta,\pi}$.
- **(b) Factorization.** The formula $L=e^{-\varrho S}w_G$ gives $L_{\varrho+\delta}(G+H,\tau)=L_\varrho(G,\tau)L_\delta(H,\tau)$ pointwise. Hence
$$\tilde F_{\varrho+\delta}(G+H,U,\sigma)=\tilde F_\varrho(G,U,\sigma)\,\langle L_\delta(H,\cdot)\rangle_{\mathrm{post}_{G,U,\sigma}} .$$
- **(b) Expectation.** Take logarithms and expectations; all are integrable by Lemma 4.2. Then apply Lemma 4.4(c) with $\mathcal H=\mathbb N^{V\times V}$, $R^0=\mathsf P_\delta$, $\ell=L_\delta$ and $\varphi=\log\langle L_\delta(h,\cdot)\rangle_{\mathrm{post}}$. ∎

**Lemma 5.2 (convexity in the rate).** For $0\le\varrho_0\le\varrho_1$ and $\delta\ge0$,
$$\mathcal K_V(\varrho_0+\delta,\pi)-\mathcal K_V(\varrho_0,\pi)\le\mathcal K_V(\varrho_1+\delta,\pi)-\mathcal K_V(\varrho_1,\pi).$$

*Proof.*
- **(i) Convexity of $\Xi_\delta$ under countable mixtures.** Let $\mu=\sum_jw_j\mu_j$ be a countable mixture with $w_j\ge0$ and $\sum w_j=1$. For each $H$, $\langle L_\delta(H)\rangle_\mu=\sum_jw_j\langle L_\delta(H)\rangle_{\mu_j}$, and all these values lie in $[m_-^{|H|},e^{\delta n^2}m_+^{|H|}]$. Lemma 1.1(c) gives $\Lambda(\langle L_\delta(H)\rangle_\mu)\le\sum_jw_j\Lambda(\langle L_\delta(H)\rangle_{\mu_j})$. Multiply by $\mathsf P_\delta(H)$ and sum; the double series converges absolutely by the uniform bound of Lemma 5.1(a). Hence $\Xi_\delta(\mu)\le\sum_jw_j\Xi_\delta(\mu_j)$.
- **(ii) Realizing $\mathsf Q_{\varrho_1}$.** Put $\Delta=\varrho_1-\varrho_0$. Realize $\mathsf Q_{V,\varrho_1,\pi}$ as $(\sigma,G_0+G',U)$ with $(\sigma,G_0,U)\sim\mathsf Q_{V,\varrho_0,\pi}$ and, given these, $G'\sim\mathsf P^\sigma_\Delta$. By the factorization of $L$,
$$\mathrm{post}^{\varrho_1}_{G_0+G',U,\sigma}=\mu_{G'},\qquad \mu_{G'}(\tau):=\frac{\mathrm{post}^{\varrho_0}_{G_0,U,\sigma}(\tau)\,L_\Delta(G',\tau)}{\langle L_\Delta(G',\cdot)\rangle_{\mathrm{post}^{\varrho_0}}} .$$
- **(iii) Predictive law.** By Lemma 5.1(b) at $\varrho_1$, and Lemma 4.4(c) with $R^0=\mathsf P_\Delta$, $\ell=L_\Delta$ and the bounded $\varphi=\Xi_\delta(\mu_{G'})$,
$$\mathcal K(\varrho_1+\delta)-\mathcal K(\varrho_1)=\mathbb E_{\mathsf Q_{\varrho_0}}\sum_{G'}\omega(G')\,\Xi_\delta(\mu_{G'}),\qquad \omega(G'):=\mathsf P_\Delta(G')\langle L_\Delta(G',\cdot)\rangle_{\mathrm{post}^{\varrho_0}} .$$
- **(iv) Jensen.** The weights $\omega(G')$ sum to $1$, and $\sum_{G'}\omega(G')\mu_{G'}=\mathrm{post}^{\varrho_0}$ because $\sum_{G'}\mathsf P_\Delta(G')L_\Delta(G',\tau)=1$. By (i), $\sum_{G'}\omega\,\Xi_\delta(\mu_{G'})\ge\Xi_\delta(\mathrm{post}^{\varrho_0})$. Taking $\mathbb E_{\mathsf Q_{\varrho_0}}$ and using Lemma 5.1(b) at $\varrho_0$ gives the claim. ∎

**Lemma 5.3 (edge term by chunking).** Let $\varrho,\beta\ge0$ and put $\kappa_0:=1+\ell_0m_+$. For every integer $J\ge1$, with $c_J:=\beta n^2/J$,
$$\mathcal K_V(\varrho+\beta,\pi)-\mathcal K_V(\varrho,\pi)\ \ge\ \beta\sum_{e\in V\times V}\mathbb E_{\mathsf Q_{V,\varrho,\pi}}\mathrm{kl}\bigl(\langle M_e\rangle_{\mathrm{post}_{G,U,\sigma}}\bigr)-\beta n^2c_J\bigl[(\ell_0+c_J)m_++\kappa_0\bigr].$$
Consequently, letting $J\to\infty$ (only the last, explicit real term depends on $J$),
$$\mathcal K_V(\varrho+\beta,\pi)-\mathcal K_V(\varrho,\pi)\ \ge\ \beta\sum_{e\in V\times V}\mathbb E_{\mathsf Q_{V,\varrho,\pi}}\mathrm{kl}\bigl(\langle M_e\rangle_{\mathrm{post}_{G,U,\sigma}}\bigr).$$

*Proof.*
- **Chunking.** Let $J\ge1$ and $\delta=\beta/J$. Telescoping, then Lemma 5.2 with $\varrho_0=\varrho$ and $\varrho_1=\varrho+j\delta$, then Lemma 5.1(b):
$$\mathcal K(\varrho+\beta)-\mathcal K(\varrho)=\sum_{j<J}\bigl[\mathcal K(\varrho+(j+1)\delta)-\mathcal K(\varrho+j\delta)\bigr]\ge J\,\mathbb E_{\mathsf Q}\Xi_\delta(\mathrm{post}).$$
- **Single edges.** In the $\mathrm{kl}$ form of $\Xi_\delta$, keep only the configurations $H=\mathbf 1_e$ (one edge on the ordered pair $e$); this is legitimate since $\mathrm{kl}\ge0$. Here $\mathsf P_\delta(\mathbf 1_e)=\delta e^{-\delta n^2}$ and $L_\delta(\mathbf 1_e,\tau)=e^{-\delta S(\tau)}M_e(\tau)$. With $c=c_J=\delta n^2$,
$$\mathcal K(\varrho+\beta)-\mathcal K(\varrho)\ge\beta e^{-c}\sum_e\mathbb E_{\mathsf Q}\,\mathrm{kl}(y_e),\qquad y_e:=\langle e^{-\delta S}M_e\rangle_{\mathrm{post}} .$$
- **Removing the tilt (explicit error).** Fix a probability measure $\mu$ and put $y_e=\langle e^{-\delta S}M_e\rangle_\mu$, $y^0_e=\langle M_e\rangle_\mu$. Since $-S\in[0,n^2]$, we have $e^{-\delta S}\in[1,e^c]$, so $y_e\in[m_-,e^cm_+]$, $y^0_e\in[m_-,m_+]$ and $0\le y_e-y^0_e\le m_+(e^c-1)$. On $[m_-,e^cm_+]$, $|\mathrm{kl}'|=|\log|\le\max(\ell_0,c+\log m_+)\le\ell_0+c$ (Lemma 1.1(b), Lemma 1.4(e)). Hence $\mathrm{kl}(y_e)\ge\mathrm{kl}(y^0_e)-(\ell_0+c)m_+(e^c-1)$. Moreover $0\le\mathrm{kl}(y^0_e)\le\kappa_0$, because $\mathrm{kl}$ is convex with $\mathrm{kl}(1)=0$, $\mathrm{kl}(m_-)\le1$ and $\mathrm{kl}(m_+)\le m_+\log m_+\le\ell_0m_+$. Therefore
$$e^{-c}\sum_e\mathrm{kl}(y_e)\ge\sum_e\mathrm{kl}(y^0_e)-(1-e^{-c})\sum_e\mathrm{kl}(y^0_e)-n^2(\ell_0+c)m_+(1-e^{-c})\ge\sum_e\mathrm{kl}(y^0_e)-n^2(1-e^{-c})\bigl[(\ell_0+c)m_++\kappa_0\bigr].$$
  Use $1-e^{-c}\le c$, insert $\mu=\mathrm{post}$, take $\mathbb E_{\mathsf Q}$ and multiply by $\beta$.
- **Limit.** The error is at most $\beta n^2\cdot\frac{\beta n^2}J[(\ell_0+\beta n^2)m_++\kappa_0]\to0$ as $J\to\infty$, while the other two terms do not depend on $J$. No interchange of a limit with an expectation is needed. ∎

**Lemma 5.4 (edge term per posterior).** For every probability measure $\mu$ on $[q]^V$ and every $\beta\ge0$,
$$\beta\sum_{e\in V\times V}\mathrm{kl}(\langle M_e\rangle_\mu)\ \ge\ \beta n^2\Bigl[\mathrm{BE}(\rho_\mu)-2\ell_0m_+\,\iota_2(\mu)-\frac{\ell_0\theta}n\Bigr],\qquad
\iota_2(\mu):=\Bigl(\frac1{n^2}\sum_{v\ne w}I_\mu(\tau_v;\tau_w)\Bigr)^{1/2}.$$

*Proof.*
- **Off-diagonal pairs.** For $v\ne w$, Lemma 1.7(c) gives $|\langle M_{vw}\rangle_\mu-\mu_v^\top M\mu_w|\le2m_+\sqrt{I_\mu(\tau_v;\tau_w)}$. Both values lie in $[m_-,m_+]$, where $\mathrm{kl}$ is $\ell_0$-Lipschitz (Lemma 1.1(b), Lemma 1.4(e)).
- **Diagonal pairs.** For $v=w$, $\langle M_{vv}\rangle=m_-$ and $\mu_v^\top M\mu_v\in[m_-,m_+]$, so the $\mathrm{kl}$ values differ by at most $\ell_0\theta$.
- **Sum.** By Cauchy–Schwarz, $n^{-2}\sum_{v\ne w}\sqrt{I}\le\iota_2(\mu)$. Hence
$$\frac1{n^2}\sum_{(v,w)}\mathrm{kl}(\langle M_{vw}\rangle_\mu)\ge\frac1{n^2}\sum_{(v,w)}\mathrm{kl}(\mu_v^\top M\mu_w)-2\ell_0m_+\iota_2(\mu)-\frac{\ell_0\theta}n .$$
- **Main term.** By Lemma 2.1(b) and bilinearity, $\frac1{n^2}\sum_{(v,w)}\mathrm{kl}(\mu_v^\top M\mu_w)=\mathrm{BE}(\rho_\mu)-\bar m_\mu^\top M\bar m_\mu+1\ge\mathrm{BE}(\rho_\mu)$, because $\bar m^\top M\bar m\le1$ (Lemma 1.4(b); this is where BAL enters). ∎

---

## 6. The pinning lemma for random sets

For a probability measure $\mu$ on $[q]^V$ and sets $W,S\subseteq V$, write
$$\mathcal J_\mu(W\mid S):=\sum_{w\in W}I_\mu(\tau_w;\tau_{W\setminus w}\mid\tau_S),\qquad \mathcal H_\mu(S):=\sum_{w\in V}H_\mu(\tau_w\mid\tau_S)\in[0,n\log q].$$

**Lemma 6.1 (pinning by entropy telescoping).** Let $n=|V|\ge2$, $p\in(0,1)$ and $T\ge1$, and put $\pi_k=1-(1-p)^k$. Let $A_k\sim\mathrm{Bern}(\pi_k)^V$ and $W\sim\mathrm{Bern}(p)^V$ be independent. Then:
- **(a)** $\displaystyle\frac1T\sum_{k=0}^{T-1}\mathbb E\,\mathcal J_\mu(W\mid A_k)\le\frac p{1-p}\cdot\frac{n\log q}T$;
- **(b)** $\displaystyle\frac1T\sum_{k=0}^{T-1}\mathbb E\sum_{u\ne v}I_\mu(\tau_u;\tau_v\mid\tau_{A_k})\le\frac{1+np}{p}\cdot\frac{n\log q}T$.

*Proof.*
- **Step 1 (exact identity for one layer).** For all $S,W\subseteq V$, Lemma 1.5(E6) gives $I(\tau_w;\tau_W\mid\tau_S)=H(\tau_w\mid\tau_S)-H(\tau_w\mid\tau_{S\cup W})$ for every $w$, including $w\in W$. Summing over $w\in V$,
$$\sum_{w\in V}I(\tau_w;\tau_W\mid\tau_S)=\mathcal H(S)-\mathcal H(S\cup W),\qquad\text{each summand }\ge0\ \text{(E3)}.$$
- **Step 2 (layers telescope).** By Lemma 1.3(a), $A_k\cup W\sim\mathrm{Bern}(\pi_{k+1})^V$. Hence, by Step 1,
$$\mathbb E\sum_wI(\tau_w;\tau_W\mid\tau_{A_k})=\mathbb E\mathcal H(A_k)-\mathbb E\mathcal H(A_{k+1}).$$
  Summing over $k<T$ gives at most $\mathcal H(\emptyset)-\mathbb E\mathcal H(A_T)\le n\log q$, by (E1).
- **(a)** Fix $A_k$. Lemma 1.3(b) with $g(w,W')=I(\tau_w;\tau_{W'}\mid\tau_{A_k})$ gives
$$\mathbb E_W\mathcal J(W\mid A_k)=\frac p{1-p}\sum_w\mathbb E_W\bigl[\mathbf 1_{w\notin W}I(\tau_w;\tau_W\mid\tau_{A_k})\bigr]\le\frac p{1-p}\sum_w\mathbb E_WI(\tau_w;\tau_W\mid\tau_{A_k}).$$
  Apply Step 2 and divide by $T$.
- **(b)** Fix $S$ and $u$. For $v\in W\setminus\{u\}$, (E5) gives $I(\tau_u;\tau_W\mid\tau_S)\ge I(\tau_u;\tau_v\mid\tau_S)$. So, whenever $W\setminus\{u\}\ne\emptyset$, $I(\tau_u;\tau_W\mid\tau_S)$ is at least the average of $I(\tau_u;\tau_v\mid\tau_S)$ over $v\in W\setminus\{u\}$. Taking $\mathbb E_W$ and using Lemma 1.3(c),
$$\frac p{1+np}\sum_{v\ne u}I(\tau_u;\tau_v\mid\tau_S)\le\sum_{v\ne u}I(\tau_u;\tau_v\mid\tau_S)\,\mathbb E_W\Bigl[\frac{\mathbf 1_{v\in W}}{|W\setminus\{u\}|}\Bigr]\le\mathbb E_WI(\tau_u;\tau_W\mid\tau_S).$$
  Sum over $u$, put $S=A_k$, and apply Step 2. ∎

**Corollary 6.2 (pinning the posterior to the ground truth).** Fix $V$ with $n\ge2$, $\varrho\ge0$, $p\in(0,1)$ and $T\ge1$. Put $\pi_k=1-(1-p)^k$ and $\mathsf Q_k:=\mathsf Q_{V,\varrho,\pi_k}$. For a probability measure $\mu$ on $[q]^V$ let
$$\bar{\mathcal J}_p(\mu):=\mathbb E_{W\sim\mathrm{Bern}(p)^V}\mathcal J_\mu(W\mid\emptyset),$$
and let $\iota_2(\mu)$ be as in Lemma 5.4. Then
$$\text{(a)}\ \ \frac1T\sum_{k<T}\mathbb E_{\mathsf Q_k}\bar{\mathcal J}_p(\mathrm{post})\le\frac{p}{1-p}\cdot\frac{n\log q}T,\qquad
\text{(b)}\ \ \frac1T\sum_{k<T}\mathbb E_{\mathsf Q_k}\iota_2(\mathrm{post})^2\le\frac{1+np}{np}\cdot\frac{\log q}T .$$

*Proof.*
- **Pin averaging.** Apply Lemma 4.4(a) to $\Upsilon=\bar{\mathcal J}_p$, which is nonnegative and bounded by $n\log q$ (each $I(\tau_w;\tau_{W\setminus w})\le H(\tau_w)\le\log q$, and $|W|\le n$). By (E2), averaging over the pin values $\xi$ turns each mutual information under $\mu_G(\cdot\mid\tau_U=\xi)$ into the conditional mutual information under $\mu_G$ given $\tau_U$. Hence
$$\mathbb E_{\mathsf Q_k}\bar{\mathcal J}_p(\mathrm{post})=\sum_G\bar{\mathsf P}_\varrho(G)\,\mathbb E_{U\sim\mathrm{Bern}(\pi_k)^V}\mathbb E_W\,\mathcal J_{\mu_G}(W\mid U).$$
- **(a)** The law $\bar{\mathsf P}_\varrho$ of $G$ does not depend on $k$. Apply Lemma 6.1(a) to $\mu=\mu_G$ for each $G$, and sum against $\bar{\mathsf P}_\varrho(G)$.
- **(b)** The same argument with Lemma 6.1(b), divided by $n^2$.

Thus pinning to the ground truth is the same as pinning to a posterior sample: in the language of [CKPZ], given the graph, the planted pins $\sigma_U$ are a sample from the posterior (Lemma 4.4(a)). ∎

---

## 7. The Aizenman–Sims–Starr decomposition and the vertex term

**Setting for this section.**
- Let $n\ge2$, $V=[n]$, and $V^+=V\cup\{o\}$, which is relabelled to $[n+1]$ by Lemma 4.7.
- Rates:
$$\varrho''=\frac s{2(n+1)},\qquad\varrho'=\frac s{2n},\qquad\beta=\varrho'-\varrho''=\frac s{2n(n+1)},\qquad r=\frac{sn}{n+1}=2n\varrho''.$$
- Pin probability per layer: $p=1-e^{-s/(n+1)}$, so that $\pi_k(n+1)=1-(1-p)^k$.
- **Cavity objects.** For a probability measure $\mu$ on $[q]^V$, $D\in\mathbb N^V$ and $N_0\in\mathbb N$, put
$$\delta_c(\tau):=-rtq\Bigl(\lambda_\tau(c)-\frac1q\Bigr)=-2\varrho''\sum_{v\in V}(M(\tau_v,c)-1),\qquad \kappa(N_0):=e^{\varrho''(1-m_-)}m_-^{N_0},$$
$$X_\mu(D,N_0):=\kappa(N_0)\,\frac1q\sum_{c\in[q]}\Bigl\langle e^{\delta_c(\tau)}\prod_{v\in V}M(\tau_v,c)^{D_v}\Bigr\rangle_\mu .$$
  The identity in the definition of $\delta_c$ is Lemma 1.4(c).
- **Null cavity law.** $\mathsf P^0:=\bigl(\bigotimes_{v\in V}\mathrm{Pois}(2\varrho'')\bigr)\otimes\mathrm{Pois}(\varrho'')$ for $(D,N_0)$, with expectation $\mathbb E^0$. Note $2\varrho''=s/(n+1)=r/n$.
- **Vertex term.** $\mathrm{Vert}(\mu):=\mathbb E^0\Lambda(X_\mu(D,N_0))$.

**Lemma 7.1 (exact cavity decomposition).** For every $\pi\in[0,1]$, with uniform pins,
$$\mathcal K_{V^+}(\varrho'',\pi)\le\mathcal K_V(\varrho'',\pi)+\mathbb E_{\mathsf Q_{V,\varrho'',\pi}}\mathrm{Vert}(\mathrm{post}_{G,U,\sigma}),$$
with equality if $\pi=0$. All terms are finite.

*Proof.*
- **(i) Splitting the graph.** A multigraph $G^+$ on $V^+$ consists of:
  - $G=G^+|_{V\times V}$;
  - the counts $G^+_{vo}$ and $G^+_{ov}$ for $v\in V$;
  - $N_0=G^+_{oo}$.

  Put $D_v=G^+_{vo}+G^+_{ov}$, and write $\tau^+=(\tau,c)$ with $c=\tau^+_o$. Since $M$ is symmetric, the compensator of the pairs $(v,o),(o,v)$ is $e^{-2\varrho''\sum_v(M(\tau_v,c)-1)}=e^{\delta_c(\tau)}$, and that of $(o,o)$ is $e^{\varrho''(1-m_-)}$. Hence
$$L_{\varrho''}(G^+,\tau^+)=L_{\varrho''}(G,\tau)\,e^{\delta_c(\tau)}\prod_{v\in V}M(\tau_v,c)^{D_v}\,\kappa(N_0).$$
- **(ii) Pointwise bound.** Let $U=U^+\cap V$ and $\sigma=\sigma^+|_V$. Then
$$\tilde F_{\varrho''}(G^+,U^+,\sigma^+)=q^{-(n+1)}\sum_{c\in C}\ \sum_{\tau:\tau_U=\sigma_U}L_{\varrho''}(G,\tau)e^{\delta_c(\tau)}\prod_vM(\tau_v,c)^{D_v}\kappa(N_0),$$
  where $C=[q]$ if $o\notin U^+$ and $C=\{\sigma^+_o\}$ otherwise. All summands are positive, so enlarging $C$ to $[q]$ gives
$$\tilde F_{\varrho''}(G^+,U^+,\sigma^+)\le\tilde F_{\varrho''}(G,U,\sigma)\cdot X_{\mathrm{post}_{G,U,\sigma}}(D,N_0),$$
  with equality if $o\notin U^+$.
- **(iii) Laws.**
  - Under $\mathsf Q_{V^+,\varrho'',\pi}$ we have $(\sigma,G,U)\sim\mathsf Q_{V,\varrho'',\pi}$.
  - $c_0=\sigma^+_o$ is uniform and independent of $(\sigma,G,U)$.
  - Given $(\sigma^+,G,U^+)$, we have $(D,N_0)\sim\mathsf P^{\sigma,c_0}:=\bigotimes_v\mathrm{Pois}(2\varrho''M(\sigma_v,c_0))\otimes\mathrm{Pois}(\varrho''m_-)$, by Lemma 1.2(b) and symmetry of $M$. (The cross and loop counts of $G^+$ are independent of $G=G^+|_{V\times V}$ and of $U^+$ given $\sigma^+$.)

  Taking logarithms and expectations in (ii) gives $\mathcal K_{V^+}(\varrho'',\pi)\le\mathcal K_V(\varrho'',\pi)+\mathbb E\log X_{\mathrm{post}}(D,N_0)$.
- **(iv) Predictive law.** By Lemma 1.2(a), $\mathsf P^{\sigma,c}(D,N_0)/\mathsf P^0(D,N_0)=e^{\delta_c(\sigma)}\prod_vM(\sigma_v,c)^{D_v}\kappa(N_0)$. So, given $(\sigma,G,U)$, the law of $h=(D,N_0)$ is $R^\sigma(h)=\mathsf P^0(h)\ell(h,\sigma)$, where
$$\ell(h,\tau):=\kappa(N_0)\,\frac1q\sum_ce^{\delta_c(\tau)}\prod_vM(\tau_v,c)^{D_v},\qquad \sum_h\mathsf P^0(h)\ell(h,\tau)=1 .$$
  Since $\langle\ell(h,\cdot)\rangle_{\mathrm{post}}=X_{\mathrm{post}}(h)$, Lemma 4.4(c) with $\varphi=\log X_{\mathrm{post}}(h)$ gives
$$\mathbb E\log X_{\mathrm{post}}=\mathbb E_{\mathsf Q}\sum_h\mathsf P^0(h)X_{\mathrm{post}}(h)\log X_{\mathrm{post}}(h)=\mathbb E_{\mathsf Q}\mathrm{Vert}(\mathrm{post}).$$
- **Integrability.** For every $\mu$, $X_\mu(h)\in[e^{-\Gamma(h)},e^{\Gamma(h)}]$, so $|\log X_\mu(h)|\le\Gamma(h)$ and $|\Lambda(X_\mu(h))|\le\Gamma(h)e^{\Gamma(h)}$, with $\Gamma$ as in Lemma 7.3 and $e^{\Gamma}\le e^{c_\delta+\varrho''}m_-^{-(|D|+N_0)}$. By Lemma 1.2(c), $\Gamma$ has finite exponential moments under $\mathsf P^0$ and under every $R^\tau$ (all rates are at most $2\varrho''m_+$). Hence: $\log X_{\mathrm{post}}$ is integrable under the joint law of step (iii), so the expectations there are finite; Lemma 4.4(c) applies with $\Phi=\Gamma$; and $\mathrm{Vert}(\mu)$ converges absolutely, uniformly in $\mu$, because $\mathbb E^0[\Gamma e^\Gamma]<\infty$. ∎

**Lemma 7.2 (the $n$-side).** For every $k\ge0$, with $\mathsf Q_k:=\mathsf Q_{V,\varrho'',\pi_k(n+1)}$,
$$a_n(k)\ge\mathcal K_V(\varrho'',\pi_k(n+1))+\beta\sum_{e\in V\times V}\mathbb E_{\mathsf Q_k}\mathrm{kl}(\langle M_e\rangle_{\mathrm{post}})-\frac{ks\log q}{n+1}.$$
Consequently, by Lemmas 7.1 and 4.7, since $a_{n+1}(k)=\mathcal K_{V^+}(\varrho'',\pi_k(n+1))$,
$$a_{n+1}(k)-a_n(k)\le\mathbb E_{\mathsf Q_k}\Bigl[\mathrm{Vert}(\mathrm{post})-\beta\sum_e\mathrm{kl}(\langle M_e\rangle_{\mathrm{post}})\Bigr]+\frac{ks\log q}{n+1}.\tag{7.1}$$

*Proof.*
- **Pin cost.** $1-\pi_k(n)=e^{-ks/n}=(1-\pi_k(n+1))(1-\pi_x)$ with $\pi_x=1-e^{-ks/(n(n+1))}\le\frac{ks}{n(n+1)}$. By Lemma 4.6,
$$a_n(k)=\mathcal K_V(\varrho',\pi_k(n))\ge\mathcal K_V(\varrho',\pi_k(n+1))-n\pi_x\log q .$$
- **Edge term.** Lemma 5.3 with $\varrho=\varrho''$ and $\varrho+\beta=\varrho'$. ∎

**Lemma 7.3 (the vertex term).** Put $c_\delta:=s\theta$ and $c_2:=1+c_\delta+s+\ell_0$, and
$$C_A:=c_2(1+s)e^{c_\delta+s(2m_+-1)}\,s\,(e^s+1+\theta),\qquad B_2:=c_2^2(1+s)^2e^{s(4m_+^2-1)},\qquad B_3:=c_2^2(1+s)^2e^{s(8m_+^2-1)}.$$
Then for every $n\ge2$ and every probability measure $\mu$ on $[q]^V$,
$$\mathrm{Vert}(\mu)\le\mathrm{BV}_r(\rho_\mu)+C_A\Bigl(\frac1n+\mathrm{dev}(\mu)\Bigr)+\frac{\sqrt{2B_2}\,s}{\sqrt n}+2\sqrt{B_3}\,\sqrt{\bar{\mathcal J}_p(\mu)} .$$

*Proof.*
- **Setup.** Let $(D,N_0)\sim\mathsf P^0$. Then the $D_v$ are i.i.d. $\mathrm{Pois}(r/n)$, $|D|\sim\mathrm{Pois}(r)$ with $r\le s$, $N_0\sim\mathrm{Pois}(\varrho'')$, and $W:=\{v:D_v\ge1\}\sim\mathrm{Bern}(p)^V$, since $1-e^{-r/n}=p$. Let $S_1:=\{D_v\le1\ \forall v\}$. Define
$$X_1(D):=\frac1q\sum_c\Bigl\langle\prod_vM(\tau_v,c)^{D_v}\Bigr\rangle_\mu,\qquad Y(D):=Y_\mu(D)=\frac1q\sum_c\prod_v(M\mu_v)_c^{D_v}.$$
  By Lemma 2.1(a), $\mathbb E^0\Lambda(Y(D))=\mathrm{BV}_r(\rho_\mu)$.
- **Ranges.** Put $\Gamma:=(|D|+N_0)\ell_0+c_\delta+\varrho''$. Then:
  - $|\delta_c|\le r\theta\le c_\delta$;
  - $\kappa\in[m_-^{N_0},e^{\varrho''}]$;
  - the products lie in $[m_-^{|D|},m_+^{|D|}]$, and $m_+\le e^{\ell_0}$.

  So $X_\mu$, $X_1$ and $Y$ all lie in $[e^{-\Gamma},e^{\Gamma}]$. By Lemma 1.1(b),
$$|\Lambda(X_\mu)-\Lambda(Y)|\le(1+\Gamma)\bigl(|X_\mu-X_1|+|X_1-Y|\bigr).$$
- **Exponential moments.** By Lemma 1.2(c) and $1+\Gamma\le c_2(1+|D|)(1+N_0)$:
  - $\mathbb E^0[(1+\Gamma)m_+^{|D|}]\le c_2(1+s)e^{s(2m_+-1)}$;
  - $\mathbb E^0[(1+\Gamma)m_+^{|D|}\mathbf 1_{N_0\ge1}]\le c_2e^{s(2m_+-1)}\cdot2\varrho''\le c_2e^{s(2m_+-1)}s/n$;
  - $\mathbb E^0[(1+\Gamma)^2m_+^{2|D|}]\le B_2$;
  - $\mathbb E^0[(1+\Gamma)^2m_+^{2|D|}|D|]\le B_3$.

  For the last two, use $\mathbb E(1+|D|)^jy^{|D|}\le e^{r(2^jy-1)}$ and $\mathbb E(1+N_0)^2\le(1+s)^2$.
- **Step 1 (compensators).** Write $\Pi_c=\prod_vM(\tau_v,c)^{D_v}\le m_+^{|D|}$. Then
$$X_\mu-X_1=\frac1q\sum_c\bigl[(\kappa-1)\langle e^{\delta_c}\Pi_c\rangle+\langle(e^{\delta_c}-1)\Pi_c\rangle\bigr].$$
  We have:
  - $|\kappa(N_0)-1|\le(e^{\varrho''}-1)+\mathbf 1_{N_0\ge1}$, and $e^{\varrho''}-1\le\frac s{2n}e^s$;
  - $|e^\delta-1|\le|\delta|e^{|\delta|}$;
  - $\frac1q\sum_c|\delta_c(\tau)|\le s\theta\cdot\frac1q\sum_c|\lambda_\tau(c)-\frac1q|\le s\theta\|\lambda_\tau-u\|_2$.

  Hence $|X_\mu-X_1|\le e^{c_\delta}m_+^{|D|}\bigl[(e^{\varrho''}-1)+\mathbf 1_{N_0\ge1}+s\theta\,\mathrm{dev}(\mu)\bigr]$. With the moment bounds, $\mathbb E^0[(1+\Gamma)|X_\mu-X_1|]\le C_A(1/n+\mathrm{dev}(\mu))$.
- **Step 2 (non-simple cavity degrees).** On $S_1^c$, $|X_1-Y|\le2m_+^{|D|}$ (in fact $\le m_+^{|D|}$, since both lie in $[m_-^{|D|},m_+^{|D|}]$; the factor $2$ only enlarges the constant), and $\mathsf P^0(S_1^c)\le n\cdot\frac12(r/n)^2\le\frac{s^2}{2n}$ (Lemma 1.2(c)). By Cauchy–Schwarz, $\mathbb E^0[(1+\Gamma)2m_+^{|D|}\mathbf 1_{S_1^c}]\le2\sqrt{B_2}\,s/\sqrt{2n}$.
- **Step 3 (simple cavity degrees: decorrelation).** On $S_1$ we have $D=\mathbf 1_W$ and $\prod_vM(\tau_v,c)^{D_v}=\prod_{w\in W}M(\tau_w,c)$. Also $(M\mu_w)_c=\langle M(\tau_w,c)\rangle_\mu$, by symmetry of $M$. Lemma 1.7(b) with $f_w=M(\cdot,c)\in[0,m_+]$, followed by Cauchy–Schwarz over $w\in W$, gives
$$|X_1-Y|\le2m_+^{|W|}\sum_{w\in W}\sqrt{I_\mu(\tau_w;\tau_{W\setminus w})}\le2m_+^{|W|}\sqrt{|W|\,\mathcal J_\mu(W\mid\emptyset)}.$$
  Since $|W|\le|D|$, Cauchy–Schwarz under $\mathsf P^0$ gives
$$\mathbb E^0\Bigl[(1+\Gamma)2m_+^{|W|}\sqrt{|W|\mathcal J_\mu(W\mid\emptyset)}\,\mathbf 1_{S_1}\Bigr]\le2\sqrt{B_3}\sqrt{\mathbb E^0\mathcal J_\mu(W\mid\emptyset)}=2\sqrt{B_3}\sqrt{\bar{\mathcal J}_p(\mu)}.$$
- **Conclusion.** Add Steps 1–3: $\mathrm{Vert}(\mu)-\mathrm{BV}_r(\rho_\mu)=\mathbb E^0[\Lambda(X_\mu)-\Lambda(Y)]$, and all expectations are finite. ∎

**Remark 7.4.** The comparison in Lemma 7.3 is with $\mathrm{BV}_r$ at $r=sn/(n+1)$, not at $s$: by Lemma 2.1 the cavity degrees $\mathrm{Pois}(s/(n+1))$ per vertex are *exactly* the Poisson splitting of $\mathrm{Pois}(r)$ over $n$ vertices. The passage from $r$ to $s$ is Lemma 2.2. The edge coefficient matches automatically: $\beta n^2=r/2$.

---

## 8. Assembly: step bound, Cesàro, and the proof of Theorem 0.1

Fix $q\ge2$, $x\in(0,1)$ and $s>0$, and let $\eta$ satisfy $\Psi_s(\nu)\le\eta$ for all $\nu\in\mathcal P_u$. Put
$$C_{\rm step}:=C_{\rm rate}s+qC_{\rm mf}+2C_A+\sqrt{2B_2}\,s+\tfrac12s\ell_0\theta+2\sqrt{B_3\,se^s\log q}+\ell_0m_+\sqrt{2s(1+s)e^s\log q}.$$
It depends only on $(q,x,s)$; the constants come from Lemmas 2.2, 2.3 and 7.3.

**Proposition 8.1 (averaged step bound).** For every $n\ge2$ and every integer $T\ge1$,
$$\frac1T\sum_{k=0}^{T-1}\bigl(a_{n+1}(k)-a_n(k)\bigr)\le\eta+C_{\rm step}\bigl(n^{-1/2}+T^{-1/2}\bigr)+\frac{Ts\log q}{n+1}.$$

*Proof.* Use the notation of §7. Fix $k<T$, write $\mathsf Q_k=\mathsf Q_{V,\varrho'',\pi_k(n+1)}$, and let $\mu$ denote a probability measure on $[q]^V$; it will be $\mathrm{post}_{G,U,\sigma}$.
- **Per-posterior bound.** Lemma 7.3 and Lemma 5.4 (with $\beta n^2=r/2$) give
$$\mathrm{Vert}(\mu)-\beta\sum_e\mathrm{kl}(\langle M_e\rangle_\mu)\le\Psi_r(\rho_\mu)+C_A\Bigl(\frac1n+\mathrm{dev}(\mu)\Bigr)+\frac{\sqrt{2B_2}s}{\sqrt n}+2\sqrt{B_3}\sqrt{\bar{\mathcal J}_p(\mu)}+r\ell_0m_+\iota_2(\mu)+\frac{r\ell_0\theta}{2n}.$$
- **Mean fixing and rate change.** Let $\rho'_\mu$ be the finitely supported law in $\mathcal P_u$ given by Lemma 2.3 applied to $\nu=\rho_\mu$. There, $\alpha(\mu)=\min\{1,q\|\bar m_\mu-u\|_\infty\}\le q\|\bar m_\mu-u\|_2\le q\,\mathrm{dev}(\mu)$. By Lemma 2.3, Lemma 2.2 with $s-r=s/(n+1)$, and the hypothesis on $\eta$,
$$\Psi_r(\rho_\mu)\le\Psi_r(\rho'_\mu)+C_{\rm mf}\,q\,\mathrm{dev}(\mu)\le\Psi_s(\rho'_\mu)+\frac{C_{\rm rate}s}{n+1}+qC_{\rm mf}\mathrm{dev}(\mu)\le\eta+\frac{C_{\rm rate}s}{n+1}+qC_{\rm mf}\mathrm{dev}(\mu).$$
- **Expectation under $\mathsf Q_k$.** Insert $\mu=\mathrm{post}$ into (7.1) and take $\mathbb E_{\mathsf Q_k}$. Use:
  - $\mathbb E\,\mathrm{dev}(\mathrm{post})\le n^{-1/2}$ (Lemma 4.4(b));
  - $\mathbb E\sqrt{\bar{\mathcal J}_p(\mathrm{post})}\le\sqrt{j_k}$ and $\mathbb E\,\iota_2(\mathrm{post})\le\sqrt{i_k}$ (Jensen), where $j_k:=\mathbb E_{\mathsf Q_k}\bar{\mathcal J}_p(\mathrm{post})$ and $i_k:=\mathbb E_{\mathsf Q_k}\iota_2(\mathrm{post})^2$;
  - $r\le s$.

  This gives
$$a_{n+1}(k)-a_n(k)\le\eta+\frac{C_{\rm rate}s}{n+1}+\frac{qC_{\rm mf}+C_A}{\sqrt n}+\frac{C_A}n+\frac{\sqrt{2B_2}s}{\sqrt n}+2\sqrt{B_3}\sqrt{j_k}+s\ell_0m_+\sqrt{i_k}+\frac{s\ell_0\theta}{2n}+\frac{ks\log q}{n+1}.$$
- **Average over $k<T$.** By Jensen, $\frac1T\sum_k\sqrt{j_k}\le\sqrt{\frac1T\sum_kj_k}$, and likewise for $i_k$. Apply Corollary 6.2 with $p=1-e^{-s/(n+1)}$, for which
  - $\frac p{1-p}n=n(e^{s/(n+1)}-1)\le se^s$;
  - $\frac{1+np}{np}\le\frac{2(1+s)e^s}{s}$, because $np\le s$ and $np\ge\frac{sn}{n+1}e^{-s/(n+1)}\ge\frac s2e^{-s}$.

  Hence $\frac1T\sum_k\sqrt{j_k}\le\sqrt{se^s\log q/T}$ and $\frac1T\sum_k\sqrt{i_k}\le\sqrt{2(1+s)e^s\log q/(sT)}$. Finally $\frac1T\sum_{k<T}k\le T$, and $\frac1{n+1}\le\frac1n\le n^{-1/2}$. Collecting terms gives the claim. ∎

**Proposition 8.2 (Cesàro).** For every integer $T\ge1$ and every $N\ge3$,
$$\bar f_N\le N\eta+2|\eta|+C_0+C_{\rm step}\bigl(2\sqrt N+NT^{-1/2}\bigr)+Ts\log q\,(1+\log N),\qquad C_0:=2\log q+s(1+m_+\ell_0).$$

*Proof.*
- **Telescoping.** Put $\bar A_N:=\frac1T\sum_{k<T}a_N(k)$. Summing Proposition 8.1 over $n=2,\dots,N-1$ gives
$$\bar A_N\le\bar A_2+(N-2)\eta+C_{\rm step}\Bigl(\sum_{n=2}^{N-1}n^{-1/2}+NT^{-1/2}\Bigr)+Ts\log q\sum_{n=2}^{N-1}\frac1{n+1}.$$
- **Elementary sums.** $\sum_{n=2}^{N-1}n^{-1/2}\le\int_1^Ny^{-1/2}dy\le2\sqrt N$ and $\sum_{n=2}^{N-1}\frac1{n+1}\le\int_2^N\frac{dy}y\le\log N$.
- **Bounds.** $|\bar A_2|\le C_0$ by Corollary 4.9(b), and $(N-2)\eta\le N\eta+2|\eta|$.
- **Domination.** By Lemma 4.5 and Corollary 4.9(a), $\bar f_N\le a_N(0)\le a_N(k)+Ts\log q$ for every $k<T$. Average over $k$. ∎

**Proof of Theorem 0.1.**
- **Choice of $T$.** Fix $\varepsilon>0$ and put $T:=\lceil(3C_{\rm step}/\varepsilon)^2\rceil$, so that $C_{\rm step}T^{-1/2}\le\varepsilon/3$.
- **Bound for $N\ge3$.** Lemma 3.3 and Proposition 8.2 give
$$f^{\rm lit}_N\le\bar f_N+C_{\rm br}\sqrt N\le\Bigl(\eta+\frac\varepsilon3\Bigr)N+\underbrace{2|\eta|+C_0+(2C_{\rm step}+C_{\rm br})\sqrt N+Ts\log q\,(1+\log N)}_{=:R_N}.$$
- **Choice of $n_\star$.** With $T$ fixed, $R_N=o(N)$. Choose $n_\star\ge3$, depending only on $(q,x,s,\eta,\varepsilon)$, such that $R_N\le\frac{2\varepsilon}3N$ for all $N\ge n_\star$. Then $f^{\rm lit}_N\le(\eta+\varepsilon)N$ for all $N\ge n_\star$.
- **Absolute convergence.** This is Lemma 3.1(a). ∎

**Remarks 8.3.**
1. **A stronger statement.** The hypothesis on $\eta$ was used only at the finitely supported laws $\rho'_{\mathrm{post}}$, which have at most $n+1$ atoms. The proof therefore shows the stronger statement in which $\eta$ need only bound $\Psi_s$ on finitely supported elements of $\mathcal P_u$.
2. **The planted form.** Proposition 8.2 alone gives the planted form of the bound, $\limsup_N\bar f_N/N\le\eta$. Lemma 3.3 transfers it to the literal form.
3. **Hypotheses used.** SYM, BAL and POS are the hypotheses of [CKPZ].
   - BAL ($t\le0$) is used in three places: $L\ge w$ (Lemma 4.2(a)), $\phi\le1$ (Lemma 3.1(d)), and $\bar m^\top M\bar m\le1$ (Lemma 5.4).
   - SYM ($Mu=\mathbf 1$) makes the cavity compensators $\delta_c$ and $S$ vanish at balanced colourings (Lemma 1.4(c)); this is what makes the compensator error $O(\mathrm{dev})$.
   - POS is never used.
   - $q\ge2$ suffices.

---

## 9. Correspondence with the Lean files

The files CKDefs.lean, CKMatrix.lean, CKAnalysis.lean, CKInfo.lean, CKBern.lean, CKBetheFin.lean, CKBethe.lean, CKBridge.lean, CKPlanted.lean, CKEdge.lean, CKPinPost.lean, CKCavity.lean, CKVertex.lean and CKMain.lean formalize §§0–8: CKDefs.lean contains the definitions, and the other thirteen files contain the proofs. The statement `CKPZProp36 q` and the objects it mentions are defined in RSDefs.lean, and a few general facts about Poisson laws are taken from other files of the same library; nothing beyond Mathlib is assumed. The formal proof follows the text, with the differences listed in 9.3.

### 9.1 Objects and conventions

**The statement.** Theorem 0.1 is the proposition `CKPZProp36 q` of RSDefs.lean:
```lean
def CKPZProp36 (q : ℕ) : Prop :=
  ∀ x : ℝ, 0 < x → x < 1 → ∀ s : ℝ, 0 < s → ∀ η : ℝ, (∀ ν ∈ rsPu q, bethePsi q s x ν ≤ η) →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∑' m : ℕ, poisPMF (s * n / 2) m * rsCbar q n m x ≤ (η + ε) * n
```
Here `∑'` is the sum of a series in Mathlib, equal to the true sum whenever the series converges absolutely, and `∀ᶠ n : ℕ in atTop` means "for all $n\ge n_\star$". The absolute convergence asserted in Theorem 0.1 is part of `ck_bridge` (Lemma 3.3), so `ckpz_prop36` proves Theorem 0.1 as stated.

**Objects.** The objects of the statement and of §3 are defined in RSDefs.lean (`poisPMF` and `colorFrac` in Defs.lean, which it imports); those of §§0–7 are defined in CKDefs.lean.

| Text | Lean |
|---|---|
| $t(x)$; $M$ at parameter $t$ | `tRe q x`; `rsM q t` |
| $F_e$, $\bar c_m(n)$ | `rsSeqF q t e`, `rsCbar q n m x` |
| $\mathcal P_u$, $\Psi_r(\nu)$ | `rsPu q`, `bethePsi q r x ν` |
| $\mathrm{Pois}(\lambda)(k)$; product of Poisson laws | `poisPMF λ k`; `poisPi` |
| multigraph $G$, number of edges, $w_G(\tau)$, $F_G$ | `RSGraph n`, `rsEdges G`, `rsW q t G τ`, `rsF q t G` |
| $\lambda_\tau(c)$, $\lVert\lambda_\tau-u\rVert_2^2$ | `colorFrac τ c`, `rsDevSq τ` |
| $\bar f_n$ | `rsFbar q n s t` |
| $m_-$, $m_+$, $\ell_0$; $\Lambda$, $\mathrm{kl}$ | `ckMm q t`, `ckMp t`, `ckEll q t`; `ckLam`, Mathlib's `InformationTheory.klFun` |
| $\mu_v$, $\mathrm{dev}(\mu)$ | `ckMarg μ v`, `ckDev μ` |
| $\tau_S=\sigma_S$; $\mu(\tau'_S=\tau_S)$ | `ckAgree S σ τ`; `ckCyl μ S τ` |
| $h_\mu(S)$, $I_\mu(\tau_A;\tau_B\mid\tau_S)$, $\mu(\cdot\mid\tau_S=\xi_S)$ | `ckH μ S`, `ckMI μ A B S`, `ckCond μ S ξ` |
| $\mathcal J_\mu(W\mid S)$, $\bar{\mathcal J}_p(\mu)$, $\iota_2(\mu)$ | `ckJ μ W S`, `ckJbar p μ`, `ckIota2 μ` |
| $\mathrm B_\pi(U)$ | `ckBern π U` |
| $\nu=\sum_jw_j\delta_{\mu_j}$ finitely supported; $\nu\in\mathcal P_u$ | `ckFinLaw q w μ`; `ckFinPu q w μ` |
| $\mathrm{BV}_r(\nu)$, $\mathrm{BE}(\nu)$, $\Psi_r(\nu)$ at such $\nu$ | `ckBV q t r w μ`, `ckBE q t w μ`, `ckPsi q t r w μ` |
| $\rho_\mu$ | weights `fun _ => (n : ℝ)⁻¹` and atoms `ckMarg μ` |
| $n^2\phi(\sigma)$, $g(\sigma,m)$ | `ckZ1 q t σ`, `ckg q t σ m` |
| $S(\tau)$, $L_\varrho(G,\tau)$; edge rates of $\mathsf P^\sigma_\varrho$ | `ckS q t τ`, `ckL q t ϱ G τ`; `ckPl q t ϱ σ` |
| $\tilde F_\varrho(G,U,\varsigma)$, $\mathrm{post}_{G,U,\varsigma}$ | `ckFt q t ϱ G U ς`, `ckPost q t ϱ G U ς` |
| $\mathbb E_{\mathsf Q_{[n],\varrho,\pi}}$, $\mathcal K_{[n]}(\varrho,\pi)$ | `ckQExp q t ϱ π n`, `ckK q t ϱ π n` |
| $\pi_k(N)$, $a_N(k)$ | `ckPin s k N`, `ckA q t s N k` |
| $\Xi_\delta(\mu)$, $\sum_e\mathrm{kl}(\langle M_e\rangle_\mu)$ | `ckXi q t δ μ`, `ckEdgeKL q t μ` |
| $X_\mu(D,N_0)$, $\mathrm{Vert}(\mu)$ | `ckX q t ϱ μ D N0`, `ckVert q t ϱ μ`, with $\varrho=\varrho''$ |

**Conventions.**
- The Lean statements use the parameter $t$, with the hypothesis `CKPar q t` ($q\ge2$, $t<0$ and $-1<t(q-1)$), in place of $x\in(0,1)$; `ckPar_tRe` shows that $t=t(x)$ satisfies it. In terms of $t$, $m_-=1+t(q-1)$ and $m_+=1-t$. The theorems that involve the objects of Theorem 0.1 (`ck_bethePsi_fin`, `ck_cbar_eq`, `ck_bridge`, `ck_planted_fe` and `ckpz_prop36`) are phrased in terms of $x$.
- Vertex sets are `Fin n`, and a multigraph is a function giving the edge count of each of the $n^2$ ordered pairs.
- Laws are mass functions. A probability measure on $[q]^V$ is a function `μ` with `IsPMF μ`; Poisson laws are explicit mass functions, and random pin sets are weighted by `ckBern`. Every expectation is a finite sum or a series; $\mathbb E_{\mathsf Q}$ (`ckQExp`) is a finite sum over $\sigma$ and $U$ of a series over multigraphs. `CKDom f` states that $\lvert f(\sigma,G,U)\rvert\le A\,c^{\lvert G\rvert}$ for some constants $A$ and $c\ge0$; for such $f$ the series converge.
- All vertices are pinned with the same probability $\pi$, the only case the proof uses.
- Entropy is written in the cylinder form $h_\mu(S)=-\sum_\tau\mu(\tau)\log\mu(\tau'_S=\tau_S)$ (`ckH`), which equals the entropy of the marginal law of $\tau_S$.

### 9.2 Results

For each result, the table lists the results that its proof in §§0–8 uses and the Lean theorems that formalize it. "Internal" means that the result is proved inside the file named in the last column but is not stated there as a separate theorem.

| Result | Proof uses | Lean theorems | File |
|---|---|---|---|
| Theorem 0.1 | 3.1(a), 3.3, 8.2 | `ckpz_prop36` | CKMain.lean |
| §§0.1–0.2: $t(x)$ and the constants | algebra | `ckPar_tRe`, `ck_const_bounds` | CKMatrix.lean |
| Fact 0.2 | product measures of finite sums of point masses; 1.1(d) | `ck_bethePsi_fin` | CKBetheFin.lean |
| Lemma 1.1 | calculus: mean value theorem, convexity | (a), with the bound $\mathrm{kl}\le1+\ell_0m_+$ on $[m_-,m_+]$ from the proof of Lemma 5.3: `ck_klFun_mem`; (b) `ck_lam_lip`, `ck_klFun_lip`; (c) `ck_lam_tsum_le`; (d) `ck_lam_abs_le` | CKAnalysis.lean |
| Lemma 1.2 | Poisson mass functions; binomial and multinomial theorems | (b) `ck_poisPi_superpose`; (c) `ck_pois_tail_two`, `ck_pois_abs_sub_le`, `ck_pois_moment_le`; (d) with uniform weights: `ck_poisson_split_unif`; for (a), (e) and the general case of (d) see 9.3 | CKAnalysis.lean |
| Lemma 1.3 | product structure; Jensen for $1/(1+y)$ | (a) `ck_bern_union`; (b) `ck_bern_insert`; (c) `ck_bern_inv_card`; basic facts `ck_bern_sum`, `ck_bern_nonneg`, `ck_bern_zero`, `ck_bern_card` | CKBern.lean |
| Lemma 1.4 | algebra | (a) `ck_rsM_eq`, `ck_rsM_mem`; (b) `ck_betheMvec_mem`, `ck_betheE_mem`, `ck_betheE_self_le_one`; (c) `ck_S_eq`, `ck_S_mem`, `ck_sum_rsM_sub_one`; (d) `ck_avg_devSq`; (e) `ck_const_bounds`, `ck_abs_log_rsM_le`; (f) internal to CKBridge.lean | CKMatrix.lean |
| Lemma 1.5 | concavity of $-y\log y$; finite Jensen | (E1) `ck_H_nonneg`, `ck_H_empty`, `ck_H_le`; (E2) `ck_H_cond_avg`, `ck_MI_cond_avg`, with `ck_cond_isPMF`; (E3) `ck_H_mono`, `ck_H_submod`, `ck_MI_nonneg`; (E4) internal; (E5) `ck_MI_mono`; (E6) internal to CKBern.lean (Step 1 of Lemma 6.1); also `ck_marg_mem` (marginals are probability vectors) and `ck_MI_single_le` ($I(\tau_w;\tau_B\mid\tau_S)\le\log q$) | CKInfo.lean |
| Lemma 1.6 | $\log y\le y-1$; Cauchy–Schwarz | internal, used by `ck_cov_le` | CKInfo.lean |
| Lemma 1.7 | 1.5(E4, E5), 1.6 | (a) `ck_cov_le`; (b) `ck_prod_decorr`; (c) `ck_pair_decorr` | CKInfo.lean |
| Lemma 2.1 | Fact 0.2, 1.1(d), 1.2(d), 1.4(b) | (a) `ck_BV_emp`; (b) is the definition of `ckBE` at weights $1/n$ | CKBethe.lean |
| Lemma 2.2 | 1.1(d), 1.2(c, e) | `ck_psi_rate` | CKBethe.lean |
| Lemma 2.3 | Fact 0.2, 1.1(d), 1.2(c) | `ck_mean_fix` | CKBethe.lean |
| Lemma 3.1 | 1.2(d), 1.4(d, f); Jensen for $y^m$ | (a) `ck_abs_log_seqF_le`, `ck_abs_g_le`; (b) `ck_cbar_eq`; (c) `ck_fbar_eq`; (d) `ck_nu_le` | CKBridge.lean |
| Lemma 3.2 | 1.4; maximal coupling on a finite set | (a) `ck_g_succ`; (b)–(d) `ck_g_lip` | CKBridge.lean |
| Lemma 3.3 | 3.1, 3.2, 1.2(c), 1.4(d) | `ck_bridge` | CKBridge.lean |
| Definition 4.1 | 1.2(a) | `ck_pl_eq` ($\mathsf P^\sigma_\varrho=\mathsf P_\varrho\,L_\varrho(\cdot,\sigma)$), `ck_L_add` ($L_{\varrho+\delta}(G+H,\tau)=L_\varrho(G,\tau)L_\delta(H,\tau)$), `ck_post_isPMF`, `ck_post_eq_cond` ($\mathrm{post}_{G,U,\varsigma}=\mu_G(\cdot\mid\tau_U=\varsigma_U)$) | CKPlanted.lean |
| Lemma 4.2 | 1.2(a, c), 1.4(c) | (a) `ck_L_mem`; (b) `ck_Ft_pos`, `ck_abs_log_Ft_le`; (c), in the form that functions dominated by $A\,c^{\lvert G\rvert}$ are $\mathsf Q$-integrable, underlies the rules for $\mathbb E_{\mathsf Q}$: `ck_QExp_add`, `ck_QExp_smul`, `ck_QExp_const`, `ck_QExp_mono`, and Jensen's inequality for the square root, `ck_QExp_sqrt_le` | CKPlanted.lean |
| Lemma 4.3 | rearrangement of absolutely convergent sums | `ck_nishimori`; with the unpinned posterior, `ck_nishimori_free` | CKPlanted.lean |
| Lemma 4.4 | 4.3, 1.4(d) | (a) `ck_nishimori_free` with `ck_post_eq_cond` (see 9.3); (b) `ck_magnetization`, `ck_mean_dev_le`; (c) `ck_predictive` | CKPlanted.lean |
| Lemma 4.5 | 4.2(a) | `ck_fbar_le_K` | CKPlanted.lean |
| Lemma 4.6 | 4.3, 1.3(a), 1.5(E1) | `ck_pin_cost` | CKPlanted.lean |
| Lemma 4.7 | — | not needed (see 9.3) | — |
| Definition 4.8 | — | the definitions `ckPin`, `ckA` | CKDefs.lean |
| Corollary 4.9 | 4.2, 4.6 | (a) `ck_A_zero_le`; (b) `ck_abs_A_le` | CKPlanted.lean |
| Remark 4.10 | 4.3, 1.4(c, d); Jensen for $\exp$ | not formalized (not used) | — |
| Lemma 5.1 | 1.2(b), 4.2, 4.4(c) | (a) `ck_xi_bdd`; (b) `ck_superpose` | CKEdge.lean |
| Lemma 5.2 | 5.1, 1.1(c), 4.4(c) | `ck_K_increment_mono` | CKEdge.lean |
| Lemma 5.3 | 5.1, 5.2, 1.1(a, b), 1.4(e) | `ck_edge_lower` (the bound after $J\to\infty$; the bound for each $J$ is internal); `ck_edgeKL_mem` (the bound $0\le\sum_e\mathrm{kl}(\langle M_e\rangle_\mu)\le n^2\kappa_0$ from the proof) | CKEdge.lean |
| Lemma 5.4 | 1.7(c), 1.1(b), 1.4(b, e), 2.1(b) | `ck_edge_pairwise` | CKEdge.lean |
| Lemma 6.1 | 1.5(E3, E5, E6), 1.3 | (a) `ck_pinning_J`; (b) `ck_pinning_pairs` | CKBern.lean |
| Corollary 6.2 | 6.1, 4.4(a), 1.5(E2) | (a) `ck_pin_post_J`; (b) `ck_pin_post_iota` | CKPinPost.lean |
| Lemma 7.1 | 1.2(a, b), 1.4(c), 4.4(c) | `ck_cavity`; the uniform bound on $\mathrm{Vert}$ from its Integrability step: `ck_vert_bdd` (CKVertex.lean) | CKCavity.lean |
| Lemma 7.2 and (7.1) | 4.6, 5.3, 7.1, 4.7 | `ck_step_decomp`, which is (7.1); Lemma 7.2 is internal | CKCavity.lean |
| Lemma 7.3 | 2.1, 1.1(b), 1.2(c), 1.7(b), 1.4 | `ck_vertex`; the law $\mathrm{Bern}(p)^V$ of $W=\{v:D_v\ge1\}$: `ck_poisPi_support` (CKBern.lean) | CKVertex.lean |
| Proposition 8.1 | (7.1), 7.3, 5.4, 2.2, 2.3, 4.4(b), 6.2; the hypothesis on $\eta$ | `ck_step_avg` | CKMain.lean |
| Proposition 8.2 | 8.1, 4.5, 4.9 | `ck_cesaro` | CKMain.lean |
| Remarks 8.3, item 2 | 8.2 | `ck_planted_fe` | CKMain.lean |

### 9.3 Differences from the text

1. **Constants.** Where only the finiteness of a constant matters, the Lean statement asserts that some constant exists. It depends only on $q$, $s$ and $t$ (or $x$), and in `ck_step_avg` and `ck_cesaro` possibly also on $\eta$. This concerns Lemma 2.2 (`ck_psi_rate`), Lemma 2.3 (`ck_mean_fix`), Lemma 3.2(b)–(d) (`ck_g_lip`), Lemma 3.3 (`ck_bridge`), Lemma 7.3 (`ck_vertex`, whose error terms are merged into $C\,(n^{-1/2}+\mathrm{dev}(\mu)+\bar{\mathcal J}_p(\mu)^{1/2})$), Proposition 8.1 (`ck_step_avg`) and Proposition 8.2 (`ck_cesaro`, in the form $\bar f_N\le N\eta+C\,(1+\sqrt N+N/\sqrt T)+Ts\log q\,(1+\log N)$). The other statements carry the constants of the text.
2. **Lemma 2.2.** `ck_psi_rate` compares the Poisson weights $\mathrm{Pois}(s)(d)$ and $\mathrm{Pois}(r)(d)$ term by term instead of using the rate coupling of Lemma 1.2(e), which is not formalized.
3. **Lemma 2.3.** `ck_mean_fix` takes $\alpha=\min\{1,q\lVert\bar m-u\rVert_2\}$, with the Euclidean norm in place of the maximum norm, and bounds the change of $\Psi_r$ by a constant times $\lVert\bar m-u\rVert_2$. The new atom is always added, with weight $0$ when $\alpha=0$. In Proposition 8.1 both versions are bounded through $\lVert\bar m_\mu-u\rVert_2\le\mathrm{dev}(\mu)$.
4. **Lemmas 3.2 and 3.3.** `ck_g_lip` replaces the maximal coupling in the proof of Lemma 3.2(c) by a hybrid argument, which changes the law of one edge at a time, and states (b)–(d) as one Lipschitz bound in $\lVert\lambda_\sigma-\lambda_{\sigma'}\rVert_1$. `ck_bridge` compares both averages with the reference value $q^{-n}\sum_\sigma g(\sigma,\lfloor sn/2\rfloor)$ instead of $g(\sigma_0,\lfloor sn/2\rfloor)$; it also asserts the absolute convergence of the series in Theorem 0.1.
5. **Poisson facts.** Lemma 1.2(a), and the splitting of Lemma 1.2(d) with the non-uniform weights $p_\sigma$ used in Lemma 3.1(c), are taken from other files of the library.
6. **Lemmas 4.3 and 4.4(c).** `ck_nishimori` assumes domination, $\lvert f(\tau,G,U,\varsigma)\rvert\le A\,c^{\lvert G\rvert}$ whenever $\tau_U=\varsigma_U$, instead of integrability; every application satisfies it. `ck_predictive` takes the kernel $R^0(h)\ell(h,\tau)$ as one nonnegative function $R(h,\tau)$, and its domination hypothesis is the summability of $h\mapsto R(h,\tau)\Phi(h)$ for each $\tau$.
7. **Lemma 4.4(a)** has no separate statement. CKPinPost.lean derives the pin averaging used in Corollary 6.2 from `ck_nishimori_free` and `ck_post_eq_cond`.
8. **Pins and relabelling.** Since all vertices are pinned with the same probability, Lemma 4.6 is formalized for constant $\pi$ and $\pi_x$. Lemma 4.7 is not needed: `ck_cavity` compares `Fin (n+1)` with `Fin n` directly, the new vertex being `0`.
9. **Lemma 5.3.** Only the bound after $J\to\infty$ is stated as a theorem (`ck_edge_lower`); the bound for each $J$ is proved inside CKEdge.lean.
10. **Lemmas 7.1 and 7.2.** `ck_cavity` proves the inequality of Lemma 7.1, at every rate $\varrho\ge0$, but not the equality for $\pi=0$, which is not used. Its integrability bound uses $\varrho(2n+1)+(\lvert D\rvert+N_0)\ell_0$ in place of $\Gamma$. Lemma 7.2 is proved inside `ck_step_decomp`, which is (7.1) for every $n\ge1$.
11. **Lemma 7.3.** `ck_vertex` first integrates out the loop count $N_0$, using $\mathbb E\,\kappa(N_0)=1$ and $\log\kappa(N_0)\le\varrho''(1-m_-)$, instead of treating $\kappa(N_0)-1$ in Step 1; it combines Steps 2 and 3 into one application of the Cauchy–Schwarz inequality.
12. **Propositions 8.1 and 8.2.** `ck_step_avg` and `ck_cesaro` assume $\Psi_s(\nu)\le\eta$ only at finitely supported $\nu\in\mathcal P_u$ (`ckFinPu`), as in Remarks 8.3, item 1. `ck_planted_fe` (Remarks 8.3, item 2) derives this hypothesis from the bound on all of $\mathcal P_u$ by Fact 0.2 (`ck_bethePsi_fin`), and `ckpz_prop36` combines `ck_planted_fe` with `ck_bridge`.
13. **Not formalized.** Remark 4.10, which is not used, and Lemmas 1.2(e) and 4.7, which the formal proof avoids (items 2 and 8).
