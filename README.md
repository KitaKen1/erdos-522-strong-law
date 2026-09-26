# A Lean proof of Erdős Problem 522

This repository formalizes solutions to the two **open statements of Erdős Problem 522** registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/522.lean):
`Erdos522.erdos_522` (coefficients `±1`) and `Erdos522.erdos_522.variants.zero_one`
(coefficients `0/1`). Let `ε₀, ε₁, …` be one infinite sequence of independent random
coefficients, uniform on `{−1, 1}` (respectively on `{0, 1}`), and put

```text
f_n(z) = ε₀ + ε₁ z + ⋯ + ε_n zⁿ,
R_n   = number of roots of f_n in { z ∈ ℂ : |z| ≤ 1 }, counted with multiplicity.
```

The theorem is that, for both coefficient distributions,

```text
R_n / (n/2) → 1   almost surely,
```

where "almost surely" refers to the single infinite coefficient sequence, so that the
convergence holds for all degrees `n` simultaneously.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-522-strong-law%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos522StrongLawLean4Web.lean)
(checked with "Latest Mathlib with Lean v4.35.0-rc3"; the file is long, so elaboration takes a few minutes)

For `±1` coefficients the almost-sure statement had already been proved informally by
P. Chojecki and, independently, by Y. Kwon and J. Zou; Yakir had proved the convergence in
probability. For `0/1` coefficients we are not aware of an earlier proof. This repository gives a
kernel-checked proof of both statements.

## Formal Conjectures target

The file in `lean/` imports the Formal Conjectures statement file and proves both statements with
the answer `True`. The definitions `KacCoefficients`, `KacCoefficients.polynomial`,
`KacCoefficients.roots` and `KacCoefficients.numRootsInUnitDisk` are the ones imported from Formal
Conjectures.

```lean
theorem E522.erdos_522_solved :
    answer(True) ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (c : Erdos522.KacCoefficients ({-1, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * c.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1

theorem E522.erdos_522_zero_one_solved :
    answer(True) ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {n : ℕ} (hn : 1 ≤ n) (f : Erdos522.KacCoefficients ({0, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * f.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1
```

Thus the theorems `Erdos522.erdos_522` and `Erdos522.erdos_522.variants.zero_one` can be changed
from `research open` to `research solved` by replacing their answer holes with `True` and using
these proofs.

## Mathematical explanation (AI generated)

The route is chosen to be light for formalization: it uses no Berry–Esseen theorem, no
log-Sobolev or Pisier inequality and no small-ball estimate from the literature. Only the
qualitative limit is proved.

**Notation.** Write $`N=n+1`$ for the number of coefficients, $`x\in\{0,1\}^N`$ for the coefficient
bits, $`\mathrm{sgn}(x_k)=\pm1`$, and $`\mathrm{cav}\,F=\frac1{2\pi}\int_0^{2\pi}F(\theta)\,d\theta`$.
For a radius $`e^s`$ put

```math
\sigma^2(s)=\sum_{k\lt N}e^{2ks},\qquad \rho_k(s)=\frac{e^{ks}}{\sigma(s)},\qquad
W_s(\theta)=\sum_{k\lt N}\mathrm{sgn}(x_k)\,\rho_k(s)\,e^{ik\theta},\qquad
m_s(\theta)=\sum_{k\lt N}\rho_k(s)\,e^{ik\theta}.
```

For $`0/1`$ coefficients, $`2f(e^{s+i\theta})/\sigma(s)=W_s(\theta)+m_s(\theta)`$ (write $`Z_s=W_s+m_s`$);
for $`\pm1`$ coefficients, $`f(e^{s+i\theta})/\sigma(s)=W_s(\theta)`$ (write $`Z_s=W_s`$). Note $`\sum_k\rho_k^2=1`$.

### 0. Reduction to finite cubes

The law of the whole coefficient sequence is the infinite product of the uniform law on
$`\{0,1\}`$ (resp. $`\{\pm1\}`$), and the first $`N`$ bits are uniform on $`\{0,1\}^N`$. By the first
Borel–Cantelli lemma it suffices to prove **complete convergence**: for every $`\varepsilon\gt 0`$,

```math
\sum_n \Pr\Bigl(\Bigl|\tfrac{2R_n}{n}-1\Bigr|\gt \varepsilon\Bigr)\lt \infty .
```

### 1. Jensen's formula at three radii

For a nonzero polynomial with $`|\mathrm{lead}|=1`$, Jensen's formula gives
$`L(s):=\mathrm{cav}\,\log|f(e^{s+i\theta})|=\sum_{\alpha}\log\max(e^s,|\alpha|)`$. Each summand is
convex in $`s`$ with slope $`1`$ exactly when $`|\alpha|\le e^s`$, hence for $`h\gt 0`$

```math
\frac{L(0)-L(-h)}h\ \le\ R_n\ \le\ \frac{L(h)-L(0)}h .
```

With $`A(s)=\tfrac12\log\sigma^2(s)`$, the function $`A(s)-ns/2`$ is even and
$`0\le A(s)-ns/2-A(0)\le n^2s^2/4`$ (pair $`k\leftrightarrow n-k`$ and use $`\cosh u\le e^{u^2/2}`$).
Put $`\Lambda=L-A`$, so $`\Lambda(s)=\mathrm{cav}\,\log|Z_s|`$ up to an additive constant. If
$`\Lambda(\pm h)\le\kappa+E`$ and $`\Lambda(0)\ge\kappa-E`$, then

```math
\Bigl|R_n-\frac n2\Bigr|\le \frac{n^2h}4+\frac{2E}h .
```

With $`h=c/n`$ this reads $`|2R_n/n-1|\le c/2+4E/c`$. It therefore suffices to find, for each
$`n`$, a common constant $`\kappa`$ and an error $`E=E_n\to0`$, with summable failure probability.

### 2. Smoothing, and the lower bound on the unit circle

Let $`\varphi_\delta(z)=\tfrac12\log(|z|^2+\delta^2)\ge\log|z|`$ and $`\psi_\beta(z)=\beta^2/(|z|^2+\beta^2)`$.
The upper bounds use $`\Lambda(s)\le\mathrm{cav}\,\varphi_\delta(Z_s)`$. For the lower bound at
$`s=0`$ we use, for $`z\ne0`$ and $`0\lt \eta\le\delta\le1`$,

```math
\varphi_\delta(z)-\log|z|\ \le\ \frac{\delta^2}{2\beta^2}+2\log\frac{2\delta}\eta\,\psi_\beta(z)
+\mathbf 1_{|z|\lt \eta}\Bigl(1+\log\frac1{|z|}\Bigr).
```

The last term is controlled by two ingredients.

- **A deterministic $`L^2`$ bound.** Every root of a nonzero $`0/1`$ or $`\pm1`$ polynomial has
  $`|\alpha|\lt 2`$ (Cauchy bound), and $`|e^{it}-\rho|\ge|\sin(t/2)|`$ for $`0\le\rho\le2`$; hence
  $`\mathrm{cav}\,(\log|f(e^{i\theta})|)^2\le400N^2`$. By Cauchy–Schwarz, the contribution of a set
  of $`\theta`$ of measure $`\mu`$ is at most $`(1+\log N)\mu+20N\sqrt\mu`$.
- **Super-polynomially small balls by separation.** Let
  $`B=\{\theta:\exists c\in\{-1,0,1\}^K\setminus\{0\},\ |\sum_{j\lt K}c_je^{ij\theta}|\lt 2\varepsilon\}`$. For
  $`\theta\notin B`$ the $`2^K`$ possible values of the first $`K`$ terms of $`f(e^{i\theta})`$ are
  $`2\varepsilon`$-separated, so, after conditioning on the other coefficients,
  $`\Pr(|f(e^{i\theta})|\lt \varepsilon)\le2^{-K}`$. Factoring the nonzero integer polynomials
  $`\sum c_jz^j`$ (their leading coefficients have modulus at least $`1`$) gives
  $`\mathrm{cav}\,\mathbf 1_B\le3^K K(2\varepsilon)^{1/K}`$. With $`K\approx10\log_2N`$ and
  $`\varepsilon\approx N^{-40K}`$, the expected measure of the small-value set is at most $`2N^{-10}`$,
  and Markov's inequality makes the event $`\{\mu\gt N^{-4}\}`$ summable.

### 3. Concentration on the cube

Every $`G:\{0,1\}^N\to\mathbb R`$ satisfies $`G-\mathbb EG=\sum_k\mathrm{sgn}(x_k)\,b_k(x_{\lt k})`$
(Doob decomposition), and if $`\sum_kb_k^2\le v`$ pointwise then

```math
\Pr(|G-\mathbb EG|\ge t)\le 2e^{-t^2/(2v)}
```

(induction on the coordinates, using $`\cosh u\le e^{u^2/2}`$). For
$`G=\mathrm{cav}\,\varphi(W+m)`$ with $`|\nabla\varphi|\le L_1`$ and $`\|\nabla^2\varphi\|\le L_2`$, a
**square-root decomposition** into blocks of length $`L`$ gives

```math
\sum_kb_k^2\le 3L_1^2\rho_{\max}^2\Bigl(\frac NL+1\Bigr)+12L_2^2\rho_{\max}^4LN+L_2^2\rho_{\max}^4N .
```

Indeed, $`b_k`$ is a Fourier coefficient at frequency $`k`$ of an averaged gradient; freezing that
gradient inside each block and applying Bessel's inequality there costs only the in-block drift,
which Parseval bounds. With $`L=\lfloor\sqrt N\rfloor`$, $`\delta=N^{-1/20}`$, $`\beta=N^{-1/40}`$ and
$`t=N^{-1/8}`$ all tails are summable.

### 4. Expectations

- **Lindeberg with Abel summation.** Replace the Rademacher terms one at a time by a
  rotation-invariant complex Gaussian, using a single Gaussian
  $`\tau_j\gamma+\sum_{k\ge j}\mathrm{sgn}(x_k)a_k`$ and the stability
  $`\tau\gamma+\rho\gamma'\sim\sqrt{\tau^2+\rho^2}\,\gamma`$. The second-order mismatch
  $`-\tfrac12\mathrm{Re}(\bar a_j^2\,\mathbb E\,Q(U_j))`$ with $`Q(z)=z^2/(|z|^2+\delta^2)^2`$ is summed
  by parts against the geometric partial sums $`\sum_{j\lt J}\rho_j^2e^{-2ij\theta}=O(1/(N|\sin\theta|))`$.
  The result is $`|\mathbb E\varphi_\delta(W_s(\theta))-\kappa_\delta|\le7\rho_{\max}/\delta^3+P_{\max}(1/(8\delta^2)+2N\rho_{\max}/\delta^3)`$,
  where $`\kappa_\delta=\mathbb E\varphi_\delta(\gamma)`$ is **the same constant at all three radii**.
  Its value is never needed.
- **Littlewood–Offord.** By the Erdős–Sperner argument,
  $`\Pr(|\sum_k\mathrm{sgn}(x_k)e^{ik\theta}+t|\lt r)\le(2r+2)/\sqrt N`$. This bounds the expected
  smoothing error without any Gaussian computation.
- The mean term $`m_s`$ of the $`0/1`$ case costs $`\mathrm{cav}\,|m_s|/(2\delta)`$, and
  $`\mathrm{cav}\,|m_s|\le\sqrt{2\varepsilon_b}+20/(\sqrt N\varepsilon_b)`$.

### 5. Parameters

With $`w=N^{1/80}`$ every parameter is an integer power of $`w`$. The total error satisfies
$`E_n\le10100\,(1+\log N)^2/N^{1/80}\to0`$, and the bad event has probability at most
$`(1/2)^N+C/N^2`$, which is summable. $`\square`$

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `2424bb48...` |
| `lean4web/` | `v4.35.0-rc3` | Standalone mathlib-only proof for Lean4Web (mathlib `5e0c4e52...`) |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both results are kernel checked. The proof files contain no `sorry`, `admit`, custom axiom,
`native_decide`, or `unsafe` theorem. Their final `#print axioms` commands report only Lean's
standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is proved here:

```text
For coefficients uniform on {−1, 1} and on {0, 1}:  R_n / (n/2) → 1 almost surely.
```

What is not claimed:

```text
Rates of convergence, such as R_n = n/2 + O(n^(7/8+δ)) almost surely.
Other coefficient distributions.
```

The two remaining statements in the Formal Conjectures file (`number_real_roots` and
`yakir_solution`) are already marked `research solved` and are not addressed here.

## Sources

- [Erdős Problem 522](https://www.erdosproblems.com/522)
- [Formal Conjectures: `ErdosProblems/522.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/522.lean)
- O. Yakir, *Approximately half of the roots of a random Littlewood polynomial are inside the disk*,
  [arXiv:2011.06234](https://arxiv.org/abs/2011.06234)
- P. Chojecki, [*Erdős Problem 522*](https://www.ulam.ai/research/erdos522-final.pdf)
- Y. Kwon and J. Zou, [*Erdős Problems 521 and 522*](https://github.com/ykwon0407/erdos-521-522)
- I. Ibragimov and D. Zaporozhets, *On distribution of zeros of random polynomials in complex plane*,
  [arXiv:1102.3517](https://arxiv.org/abs/1102.3517)
- P. Erdős, *On a lemma of Littlewood and Offord*, Bull. Amer. Math. Soc. 51 (1945)
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-361-asymptotic)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced by Kenta Kitamura with assistance from ChatGPT and OpenAI Codex using GPT-6 Astra, and Claude Code using Claude Opus 5.5.

## Appendix: Historical background (AI generated)

This appendix explains why Formal Conjectures has two statements for Problem 522, one with
$`\pm1`$ and one with $`\{0,1\}`$ coefficients, and how the problem was solved. It was compiled
on 26 September 2026 from the original paper, the erdosproblems.com pages, their revision history
and forum threads, and the history of `522.lean` in Formal Conjectures.

### A.1 The source and its two readings

The problem comes from §V, "Problems on probability", of P. Erdős,
*Some unsolved problems*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 6 (1961), 221–254
([PDF](https://www.renyi.hu/~p_erdos/1961-22.pdf), pp. 251–253).

Problem 2 there opens with $`\varepsilon_k=\pm1`$ and recalls the Erdős–Offord theorem on real
roots. For the almost-sure questions, however, Erdős writes the binary expansion of $`0\lt t\lt 1`$
as $`t=\sum_{k\ge1}\varepsilon_k(t)/2^k`$ and considers the partial sums of
$`\sum_{k\ge0}\varepsilon_k(t)z^k`$. He conjectures in (V.2.1) that the number of real roots is
asymptotic to $`\frac2\pi\log n`$ for almost all $`t`$; this is now Erdős Problem 521. In (V.2.2)
he asks whether the number $`R'_n(t)`$ of roots in the unit disk satisfies $`R'_n(t)/n\to1/2`$
for almost all $`t`$; this is Problem 522. He adds that he cannot even prove the weaker statement
that all but $`o(2^n)`$ of the polynomials have $`n/2+o(n)`$ roots in $`|z|\lt 1`$.

Binary digits take the values 0 and 1. Read literally, the almost-sure question is therefore about
$`\{0,1\}`$ coefficients, while the surrounding text is about $`\pm1`$ coefficients.

| Passage in Erdős (1961) | What it says | Reading it supports |
|---|---|---|
| p. 251, Problem 1 | Rademacher functions $`r_n(t)=\pm1`$ and the law of the iterated logarithm | $`\pm1`$, explicitly |
| p. 252, Problem 2, first sentence | $`\varepsilon_k=\pm1`$; the Erdős–Offord theorem on real roots | $`\pm1`$, explicitly |
| p. 252, Problem 2, (V.2.1) and (V.2.2) | $`\varepsilon_k(t)`$ are the binary digits of $`t`$ | $`\{0,1\}`$, literally |
| p. 253, Problem 3, (V.3.1) | Salem–Zygmund: $`\max_{\vert z\vert=1}\vert\sum_{k\le n}\varepsilon_k(t)z^k\vert\asymp\sqrt{n\log n}`$, with the same $`\varepsilon_k(t)`$ | $`\pm1`$, implicitly: for $`\{0,1\}`$ the value at $`z=1`$ is about $`n/2`$ |

The last row is our own observation. Note also that the binary expansion starts at $`k=1`$ while
the power series starts at $`k=0`$, so $`\varepsilon_0(t)`$ is not defined: the definition is
written informally.

### A.2 How the two readings became two statements

- **Problem 521 forum, September 2025.** M. Sawhney noted that for $`\{0,1\}`$ coefficients the
  constant $`2/\pi`$ in (V.2.1) should be $`1/\pi`$, since a $`0/1`$ polynomial has no positive
  real roots. T. Tao argued for the literal $`\{0,1\}`$ reading. T. Bloom argued for $`\pm1`$:
  that reading needs only one slip (an uncentred binary expansion), whereas $`\{0,1\}`$ breaks the
  convention of the section and also the constant in (V.2.1). Both readings were judged natural,
  and the site now mentions both.
- **Problem 522 forum, September–November 2025.** V. Kovač pointed out the same ambiguity, and
  also that the site's statement did not distinguish almost-sure convergence from convergence in
  probability.
- **erdosproblems.com.** The page for 522 had described the problem as solved by Yakir. On
  6 December 2025 it was reopened with the almost-sure formulation, $`\pm1`$ coefficients and a
  note on $`\{0,1\}`$.
- **Formal Conjectures.** The first formalization
  ([#351](https://github.com/google-deepmind/formal-conjectures/pull/351), merged August 2025) was
  an in-probability statement marked `research solved`. It was reopened in February 2026 and
  rewritten as the almost-sure statement in
  [#3896](https://github.com/google-deepmind/formal-conjectures/pull/3896) (28 April 2026), which
  also added `erdos_522.variants.zero_one` for the $`\{0,1\}`$ reading. In
  [#5793](https://github.com/google-deepmind/formal-conjectures/pull/5793) (12 September 2026) the
  reference measure of `KacCoefficients` was changed to the counting measure; before that change,
  uniform coefficients on a two-point set could not be expressed by measurable functions.

For Problem 522 the two readings have the same answer. With $`\xi_k=(1+\varepsilon_k)/2`$,

```math
f_n^{0/1}(z)=\tfrac12\,g_n(z)+\tfrac12\,(1+z+\dots+z^n),
```

where $`g_n`$ has $`\pm1`$ coefficients. On the unit circle the random part has size about
$`\sqrt n`$, and the deterministic part exceeds it only on an arc of length about $`1/\sqrt n`$
around $`z=1`$, which carries about $`\sqrt n`$ of the $`n`$ roots. For Problem 521, in contrast,
the reading changes the constant from $`2/\pi`$ to $`1/\pi`$.

The proofs do differ. The informal $`\pm1`$ proofs listed below use the log-integrability theorem
of Nazarov, Nishry and Sodin for Rademacher Fourier series, which does not apply directly when the
mean term is present. The route of this repository does not use that theorem (Section 2 above).

### A.3 Other possible readings

| Question | Erdős (1961) | Current statements | Effect on the answer | This repository |
|---|---|---|---|---|
| Coefficients | Stated as $`\pm1`$, defined as binary digits $`\{0,1\}`$ | Site: $`\pm1`$, with $`\{0,1\}`$ in a note. FC: both, as separate statements | None: both answers are yes | Both proved |
| Mode of convergence | Almost sure ("for almost all $`t`$"). Convergence in probability is the weaker question he also could not prove | Almost sure. Until December 2025 (site) and April 2026 (FC), Yakir's in-probability theorem was treated as a solution | Different questions. Convergence in probability was proved by Yakir (2021) for $`\pm1`$ | Almost sure, which implies convergence in probability |
| One sequence, or a new one for each $`n`$ | One $`t`$, hence one sequence for all $`n`$ | FC: one `KacCoefficients` sequence | None | The proof gives complete convergence, so the conclusion holds for any coupling across $`n`$ (not stated as a separate theorem) |
| Boundary | "In the unit circle"; the weaker form uses the open disk | Closed disk | None expected: only roots on the circle differ | Jensen's secant bounds control both the open-disk and the closed-disk counts. The Lean statement uses the closed disk |
| Multiplicity | Not specified | FC counts with multiplicity | For $`\pm1`$, none: a double root has probability $`O(n^{-2})`$ (Peled–Sen–Zeitouni), so eventually there are none. For $`\{0,1\}`$ the multiplicity of the root $`0`$ is eventually constant; other repeated roots were not examined | With multiplicity |

### A.4 Timeline

| Date | Event |
|---|---|
| 1956 | Erdős and Offord: all but $`o(2^n/\sqrt{\log\log n})`$ of the $`\pm1`$ polynomials of degree $`n`$ have $`\frac2\pi\log n+o((\log n)^{2/3}\log\log n)`$ real roots. |
| 1961 | Erdős asks the almost-sure questions (V.2.1) and (V.2.2), and the weaker in-probability question for the unit disk. |
| 1967 | The in-probability question appears in W. K. Hayman, *Research Problems in Function Theory*. |
| 2011 | Ibragimov and Zaporozhets: for i.i.d. coefficients the arguments of the roots are asymptotically uniform, and $`\mathbb E\log(1+\vert\xi_0\vert)\lt\infty`$ is necessary and sufficient for the roots to concentrate near the unit circle. This does not decide the fraction inside the disk. |
| 2020 (arXiv), 2021 | O. Yakir: all but $`o(2^n)`$ of the $`\pm1`$ polynomials have $`n/2+o(n)`$ roots in the unit disk, answering the in-probability question. |
| August 2025 | Formal Conjectures formalizes 522 as an in-probability statement, marked `research solved`. |
| September–November 2025 | Forum discussions of Problems 521 and 522 identify the $`\pm1`$ versus $`\{0,1\}`$ ambiguity and the almost-sure versus in-probability distinction. |
| 6 December 2025 | erdosproblems.com reopens 522 with the almost-sure formulation. |
| February 2026 | Formal Conjectures changes the status of `erdos_522` to `research open`. |
| 15 April 2026 | B. Letwin outlines an approach through the Nazarov–Nishry–Sodin theorem and an almost-sure central limit theorem in the spirit of Angst and Poly. |
| 20 April 2026 | P. Chojecki posts an informal proof of the $`\pm1`$ statement, written with GPT-5.4 Pro. |
| 21 April 2026 | B. Letwin reports that M. Michelen and O. Yakir can prove a stronger result that would imply the $`\pm1`$ statement. We could not locate it as of 26 September 2026. |
| 27 April 2026 | P. Chojecki posts a revised proof, written with GPT-5.5 Pro: $`R_n=n/2+O(n^{399/400})`$ almost surely. |
| 28 April 2026 | Y. Kwon and J. Zou post an independent informal proof through a fourth-moment estimate, with rate $`n^{7/8+\delta}`$. |
| 28 April 2026 | Formal Conjectures rewrites 522 as the almost-sure statement and adds `erdos_522.variants.zero_one`. |
| 12 September 2026 | Formal Conjectures corrects the reference measure of `KacCoefficients`. |
| 26 September 2026 | This repository: Lean proofs of `erdos_522` and `erdos_522.variants.zero_one`. |

### A.5 Status on 26 September 2026

| Statement | Coefficients, convergence | Informal proof | Formal proof | Status (site / FC) |
|---|---|---|---|---|
| `erdos_522` | $`\pm1`$, almost sure | P. Chojecki; Y. Kwon and J. Zou (April 2026, not peer reviewed) | This repository | open / `research open` |
| `erdos_522.variants.zero_one` | $`\{0,1\}`$, almost sure | None known to us | This repository | mentioned in a note / `research open` |
| `erdos_522.variants.yakir_solution` | $`\pm1`$, in probability | O. Yakir (2021) | — | — / `research solved` |
| `erdos_522.variants.number_real_roots` | $`\pm1`$, real roots, in probability | Erdős and Offord (1956) | — | — / `research solved` |

We are not aware of an earlier proof of the $`\{0,1\}`$ statement, but a literature search cannot
exclude unpublished work.

Further sources for this appendix:
[erdosproblems.com revision history of 522](https://www.erdosproblems.com/history/522),
[forum of Problem 522](https://www.erdosproblems.com/forum/discuss/522),
[Problem 521](https://www.erdosproblems.com/521) and
[its forum](https://www.erdosproblems.com/forum/discuss/521),
[P. Chojecki, first version](https://www.ulam.ai/research/erdos522.pdf),
[F. Nazarov, A. Nishry and M. Sodin](https://arxiv.org/abs/1301.0529),
[J. Angst and G. Poly](https://arxiv.org/abs/1912.09928),
[R. Peled, A. Sen and O. Zeitouni](https://arxiv.org/abs/1409.2034).
