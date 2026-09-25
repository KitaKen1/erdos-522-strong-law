import Mathlib

#eval Lean.versionString

/-!
# Erdős Problem 522: standalone Lean4Web proof

This file reproduces the Formal Conjectures definitions `KacCoefficients`,
`KacCoefficients.polynomial`, `KacCoefficients.roots` and `KacCoefficients.numRootsInUnitDisk`
(`FormalConjectures/ErdosProblems/522.lean`) and proves the statements `erdos_522`
(coefficients `±1`) and `erdos_522.variants.zero_one` (coefficients `0/1`) with the answer
`True`: for one infinite sequence of independent uniform coefficients, the number `R_n` of roots
of `∑_{k ≤ n} ε_k z^k` in the closed unit disc satisfies `2 R_n / n → 1` almost surely.
It uses mathlib only.
-/

/- ## Section: `FormalConjectures definitions` -/

/-
The definitions below are copied from `FormalConjectures/ErdosProblems/522.lean` at Formal
Conjectures commit `2424bb480c590237ffbb2cc831ae4cb8977e045a` (Copyright 2025 The Formal Conjectures Authors, Apache License
2.0), with the same `open` declarations. Only the `module`/`public` wrappers and the two
statements with an open answer are dropped (they are proved at the end of this file).
-/

section

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real

namespace Erdos522

/--
A sequence of *Kac coefficients* over a subset `S` of a field `k` is a countably infinite sequence
of independent random variables, each uniformly distributed over `S` with respect to the reference
measure `μ`. The default reference measure is the counting measure, so that for a finite set `S`
each coefficient takes every value of `S` with probability `1 / |S|`.

Such a sequence determines a *Kac polynomial* of degree `n` for each `n`, which is the random
polynomial given by `KacCoefficients.polynomial`.
-/
@[ext]
structure KacCoefficients
    {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count) where
  toFun : ℕ → Ω → k
  h_indep : ProbabilityTheory.iIndepFun toFun ℙ
  h_unif : ∀ i, MeasureTheory.pdf.IsUniform (toFun i) S ℙ μ

variable {k : Type*} [Field k] [MeasurableSpace k] (S : Set k)
    (Ω : Type*) [MeasureSpace Ω] (μ : Measure k := Measure.count)

/--
We can always view a Kac polynomial as a random variable on `ℕ`.
-/
instance : FunLike (KacCoefficients S Ω μ) ℕ (Ω → k) where
  coe P := P.toFun
  coe_injective P Q h := by aesop

namespace KacCoefficients

open scoped Polynomial

variable {S Ω} {μ : Measure k}

/--
The random polynomial associated to a sequence `c : KacCoefficients S Ω μ` of Kac coefficients
given by `∑ i ∈ Finset.range (n + 1), c i z^i`.
-/
noncomputable def polynomial (c : KacCoefficients S Ω μ) (n : ℕ) :
    Ω → k[X] := fun ω => ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (c i ω)

/--
The random multiset of roots associated to a Kac polynomial
-/
noncomputable def roots (c : KacCoefficients S Ω μ) (n : ℕ) : Ω → Multiset k :=
    fun ω => (c.polynomial n ω).roots

/-- Counts the number of roots of a Kac polynomial in the unit disk with multiplicity. -/
noncomputable def numRootsInUnitDisk [PseudoMetricSpace k] (c : KacCoefficients S Ω μ) (n : ℕ)
    (ω : Ω) : ℕ :=
  open scoped Classical in
  (c.roots n ω).countP (· ∈ Metric.closedBall 0 1)

end KacCoefficients

end Erdos522

end

/- ## Section: `Defs` -/

section

/-
# Erdős 522 (0/1 variant): core definitions

Everything below is elementary: the random `0/1` polynomial with coefficient vector
`x : Fin N → Bool`, finite cube averages, normalised averages over `[0, 2π]`, the radial
profile `ρ_k(s) = e^{ks}/σ_N(s)`, the smoothed logarithm `φ_δ`, the test function `ψ_β`,
and the standard complex Gaussian `cgauss` (with `E|z|² = 1`).
-/

open Real Complex MeasureTheory Filter Topology

namespace E522

noncomputable section

/-- `±1` value of a bit. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- `0/1` value of a bit. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

lemma sgn_add_one (b : Bool) : sgn b + 1 = 2 * bit b := by
  cases b <;> norm_num [sgn, bit]

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by
  cases b <;> norm_num [sgn]

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> norm_num [sgn]

/-- The `0/1` polynomial `∑_{k<N} x_k z^k`. -/
def poly {N : ℕ} (x : Fin N → Bool) : Polynomial ℂ :=
  ∑ k : Fin N, Polynomial.monomial (k : ℕ) ((bit (x k) : ℝ) : ℂ)

open scoped Classical in
/-- Number of roots (with multiplicity) of `poly x` in the closed unit disc. -/
def rootCount {N : ℕ} (x : Fin N → Bool) : ℕ :=
  (poly x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1)

/-- Normalised average over `[0, 2π]`. -/
def cav (F : ℝ → ℝ) : ℝ := (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), F θ

/-- Normalised average over `[0, 2π]` of a complex valued function. -/
def cavC (F : ℝ → ℂ) : ℂ := (((2 * π)⁻¹ : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), F θ

/-- Uniform average over the cube `Bool^N`. -/
def cubeAvg (N : ℕ) (F : (Fin N → Bool) → ℝ) : ℝ := (∑ x, F x) / 2 ^ N

open scoped Classical in
/-- Uniform probability of an event on the cube `Bool^N`. -/
def cubeProb (N : ℕ) (P : (Fin N → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / 2 ^ N

/-- `σ_N(s)^2 = ∑_{k<N} e^{2ks}`. -/
def sig2 (N : ℕ) (s : ℝ) : ℝ := ∑ k ∈ Finset.range N, Real.exp (2 * k * s)

/-- Normalised radial profile `ρ_k(s) = e^{ks}/σ_N(s)`. -/
def rho (N : ℕ) (s : ℝ) (k : ℕ) : ℝ := Real.exp (k * s) / Real.sqrt (sig2 N s)

/-- `e^{ikθ}`. -/
def ex (k : ℕ) (θ : ℝ) : ℂ := Complex.exp (((k : ℝ) * θ : ℝ) * I)

/-- The random `±1` part `W(θ) = ∑_k sgn(x_k) ρ_k e^{ikθ}`. -/
def Wfun {N : ℕ} (ρ : ℕ → ℝ) (x : Fin N → Bool) (θ : ℝ) : ℂ :=
  ∑ k : Fin N, ((sgn (x k) * ρ k : ℝ) : ℂ) * ex k θ

/-- The deterministic mean part `m(θ) = ∑_{k<N} ρ_k e^{ikθ}`. -/
def mfun (N : ℕ) (ρ : ℕ → ℝ) (θ : ℝ) : ℂ :=
  ∑ k : Fin N, ((ρ k : ℝ) : ℂ) * ex k θ

/-- Smoothed logarithm `φ_δ(z) = ½ log(|z|² + δ²)`. -/
def phiD (δ : ℝ) (z : ℂ) : ℝ := Real.log (‖z‖ ^ 2 + δ ^ 2) / 2

/-- Gradient of `φ_δ` (as a complex number): `z / (|z|² + δ²)`. -/
def gphiD (δ : ℝ) (z : ℂ) : ℂ := z / (((‖z‖ ^ 2 + δ ^ 2 : ℝ)) : ℂ)

/-- Test function `ψ_β(z) = β²/(|z|² + β²)`. -/
def psiB (β : ℝ) (z : ℂ) : ℝ := β ^ 2 / (‖z‖ ^ 2 + β ^ 2)

/-- Gradient of `ψ_β` (as a complex number): `-2β² z/(|z|²+β²)²`. -/
def gpsiB (β : ℝ) (z : ℂ) : ℂ := -((2 * β ^ 2 / (‖z‖ ^ 2 + β ^ 2) ^ 2 : ℝ) : ℂ) * z

/-- Standard complex Gaussian (with `E|z|² = 1`). -/
def cgauss : Measure ℂ :=
  (ProbabilityTheory.stdGaussian ℂ).map (fun z : ℂ => ((Real.sqrt 2)⁻¹ : ℝ) • z)

/-- `κ_δ = E φ_δ(γ)` for a standard complex Gaussian `γ`. -/
def kappa (δ : ℝ) : ℝ := ∫ z, phiD δ z ∂cgauss

/-- Average of `G` over the coordinates `≥ k`, keeping `x j` for `j < k`. -/
def condPrefix {N : ℕ} (G : (Fin N → Bool) → ℝ) (k : ℕ) (x : Fin N → Bool) : ℝ :=
  cubeAvg N (fun y => G (fun j => if (j : ℕ) < k then x j else y j))

/-- Martingale difference coefficient `b_k(x)` (depends only on `x_{<k}`). -/
def mgDiff {N : ℕ} (G : (Fin N → Bool) → ℝ) (k : Fin N) (x : Fin N → Bool) : ℝ :=
  (condPrefix G (k + 1) (Function.update x k true) -
    condPrefix G (k + 1) (Function.update x k false)) / 2

/-- `b k x` depends only on `x j` for `j < k`. -/
def Predictable {N : ℕ} (b : Fin N → (Fin N → Bool) → ℝ) : Prop :=
  ∀ (k : Fin N) (x y : Fin N → Bool), (∀ j : Fin N, j < k → x j = y j) → b k x = b k y

/-- Normalised log-average on the circle of radius `e^s`:
`Λ_x(s) = (1/2π)∫ log|f_x(e^{s+iθ})| dθ − ½ log σ_N(s)²`. -/
def Lam {N : ℕ} (x : Fin N → Bool) (s : ℝ) : ℝ :=
  Real.circleAverage (fun z => Real.log ‖(poly x).eval z‖) 0 (Real.exp s) -
    Real.log (sig2 N s) / 2

/-- The normalised random polynomial on the circle of radius `e^s`:
`Z_x(s,θ) = 2 f_x(e^{s+iθ}) / σ_N(s) = W(θ) + m(θ)` with `ρ = rho N s`. -/
def Zfun {N : ℕ} (x : Fin N → Bool) (s θ : ℝ) : ℂ :=
  Wfun (rho N s) x θ + mfun N (rho N s) θ

end

end E522

end

/- ## Section: `Cube` -/

section

/-
# Finite cube: averages, probabilities, martingale decomposition, Chernoff bound

`G x - E G = ∑_k sgn(x_k) b_k(x)` with predictable `b_k = mgDiff G k`, and
if `∑_k b_k(x)^2 ≤ v` for every `x` then `P(|G - EG| ≥ t) ≤ 2 exp(-t²/(2v))`.
Proof of the MGF bound: induction on the last coordinate using
`(e^{λb} + e^{-λb})/2 = cosh(λ b) ≤ exp(λ²b²/2)` (`Real.cosh_le_exp_half_sq`).
-/

open Real

namespace E522

/- ### Helpers -/

lemma cube_aux_card (N : ℕ) : (Fintype.card (Fin N → Bool) : ℝ) = 2 ^ N := by
  simp

lemma cube_aux_prob_eq (N : ℕ) (P : (Fin N → Bool) → Prop) [DecidablePred P] :
    cubeProb N P = ((Finset.univ.filter P).card : ℝ) / 2 ^ N := by
  unfold cubeProb
  congr

/- ### Basic facts on `cubeAvg` / `cubeProb` -/

theorem cubeAvg_const (N : ℕ) (c : ℝ) : cubeAvg N (fun _ => c) = c := by
  unfold cubeAvg
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cube_aux_card]
  field_simp

theorem cubeAvg_mono {N : ℕ} {F G : (Fin N → Bool) → ℝ} (h : ∀ x, F x ≤ G x) :
    cubeAvg N F ≤ cubeAvg N G := by
  unfold cubeAvg
  gcongr with x
  exact h x

theorem cubeAvg_add {N : ℕ} (F G : (Fin N → Bool) → ℝ) :
    cubeAvg N (fun x => F x + G x) = cubeAvg N F + cubeAvg N G := by
  unfold cubeAvg
  rw [Finset.sum_add_distrib, add_div]

theorem cubeAvg_sub {N : ℕ} (F G : (Fin N → Bool) → ℝ) :
    cubeAvg N (fun x => F x - G x) = cubeAvg N F - cubeAvg N G := by
  unfold cubeAvg
  rw [Finset.sum_sub_distrib, sub_div]

theorem cubeAvg_smul {N : ℕ} (c : ℝ) (F : (Fin N → Bool) → ℝ) :
    cubeAvg N (fun x => c * F x) = c * cubeAvg N F := by
  unfold cubeAvg
  rw [← Finset.mul_sum, mul_div_assoc]

theorem abs_cubeAvg_le {N : ℕ} (F : (Fin N → Bool) → ℝ) :
    |cubeAvg N F| ≤ cubeAvg N (fun x => |F x|) := by
  unfold cubeAvg
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ N)]
  gcongr
  exact Finset.abs_sum_le_sum_abs _ _

theorem cubeProb_nonneg (N : ℕ) (P : (Fin N → Bool) → Prop) : 0 ≤ cubeProb N P := by
  unfold cubeProb
  positivity

theorem cubeProb_le_one (N : ℕ) (P : (Fin N → Bool) → Prop) : cubeProb N P ≤ 1 := by
  classical
  rw [cube_aux_prob_eq, div_le_one (by positivity), ← cube_aux_card]
  exact_mod_cast Finset.card_filter_le _ _

theorem cubeProb_mono {N : ℕ} {P Q : (Fin N → Bool) → Prop} (h : ∀ x, P x → Q x) :
    cubeProb N P ≤ cubeProb N Q := by
  classical
  rw [cube_aux_prob_eq, cube_aux_prob_eq]
  gcongr
  exact h _

theorem cubeProb_or_le {N : ℕ} (P Q : (Fin N → Bool) → Prop) :
    cubeProb N (fun x => P x ∨ Q x) ≤ cubeProb N P + cubeProb N Q := by
  classical
  rw [cube_aux_prob_eq, cube_aux_prob_eq, cube_aux_prob_eq, ← add_div, Finset.filter_or]
  gcongr
  exact_mod_cast Finset.card_union_le _ _

open scoped Classical in
theorem cubeProb_eq_cubeAvg {N : ℕ} (P : (Fin N → Bool) → Prop) :
    cubeProb N P = cubeAvg N (fun x => if P x then 1 else 0) := by
  unfold cubeProb cubeAvg
  rw [Finset.sum_boole]

/-- Markov's inequality on the cube. -/
theorem cube_markov {N : ℕ} (F : (Fin N → Bool) → ℝ) (hF : ∀ x, 0 ≤ F x) (a : ℝ) (ha : 0 < a) :
    cubeProb N (fun x => a < F x) ≤ cubeAvg N F / a := by
  classical
  rw [cubeProb_eq_cubeAvg, div_eq_inv_mul, ← cubeAvg_smul]
  apply cubeAvg_mono
  intro x
  split_ifs with h
  · rw [inv_mul_eq_div, le_div_iff₀ ha]
    linarith
  · have := hF x
    positivity

/-- The polynomial with no nonzero coefficient is only the all-`false` vector. -/
theorem cubeProb_all_false (N : ℕ) :
    cubeProb N (fun x => ∀ k, x k = false) = (1 / 2) ^ N := by
  classical
  rw [cube_aux_prob_eq]
  have h1 : (Finset.univ.filter (fun x : Fin N → Bool => ∀ k, x k = false)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨fun _ => false, ?_⟩
    ext x
    simp [funext_iff]
  rw [h1]
  simp

/- ### Martingale decomposition -/

lemma cube_aux_flip_invol {N : ℕ} (k : Fin N) :
    Function.Involutive (fun x : Fin N → Bool => Function.update x k (!x k)) := by
  intro x
  simp

lemma cube_aux_sum_flip {N : ℕ} (k : Fin N) (f : (Fin N → Bool) → ℝ) :
    ∑ x, f (Function.update x k (!x k)) = ∑ x, f x :=
  Equiv.sum_comp ((cube_aux_flip_invol k).toPerm _) f

lemma cube_aux_sum_split {N : ℕ} (k : Fin N) (f : (Fin N → Bool) → ℝ) :
    ∑ y, f (Function.update y k true) + ∑ y, f (Function.update y k false) = 2 * ∑ y, f y := by
  have hpt : ∀ y, f (Function.update y k true) + f (Function.update y k false) =
      f y + f (Function.update y k (!y k)) := by
    intro y
    cases h : y k
    · have : Function.update y k false = y := by rw [← h, Function.update_eq_self]
      rw [this]
      simp [add_comm]
    · have : Function.update y k true = y := by rw [← h, Function.update_eq_self]
      rw [this]
      simp
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun y _ => hpt y), Finset.sum_add_distrib,
    cube_aux_sum_flip k f]
  ring

lemma cube_aux_condPrefix_zero {N : ℕ} (G : (Fin N → Bool) → ℝ) (x : Fin N → Bool) :
    condPrefix G 0 x = cubeAvg N G := by
  simp [condPrefix]

lemma cube_aux_condPrefix_top {N : ℕ} (G : (Fin N → Bool) → ℝ) (x : Fin N → Bool) :
    condPrefix G N x = G x := by
  simp [condPrefix, cubeAvg_const]

lemma cube_aux_condPrefix_update {N : ℕ} (G : (Fin N → Bool) → ℝ) (k : Fin N)
    (x : Fin N → Bool) (c : Bool) :
    condPrefix G (k + 1) (Function.update x k c) =
      (∑ y, G (fun j => if (j : ℕ) < k then x j else Function.update y k c j)) / 2 ^ N := by
  unfold condPrefix cubeAvg
  congr 1
  refine Finset.sum_congr rfl (fun y _ => ?_)
  beta_reduce
  congr 1
  funext j
  by_cases hjk : j = k
  · subst hjk
    simp
  · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
    have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
    by_cases hj : (j : ℕ) < k
    · simp [hj, show (j : ℕ) < k + 1 by omega]
    · simp [hj, show ¬ (j : ℕ) < k + 1 by omega]

lemma cube_aux_condPrefix_split {N : ℕ} (G : (Fin N → Bool) → ℝ) (k : Fin N)
    (x : Fin N → Bool) :
    2 * condPrefix G k x = condPrefix G (k + 1) (Function.update x k true) +
      condPrefix G (k + 1) (Function.update x k false) := by
  have h := cube_aux_sum_split k (fun y => G (fun j => if (j : ℕ) < k then x j else y j))
  rw [cube_aux_condPrefix_update, cube_aux_condPrefix_update, ← add_div, h]
  unfold condPrefix cubeAvg
  ring

lemma cube_aux_condPrefix_step {N : ℕ} (G : (Fin N → Bool) → ℝ) (k : Fin N)
    (x : Fin N → Bool) :
    condPrefix G (k + 1) x - condPrefix G k x = sgn (x k) * mgDiff G k x := by
  have h2 := cube_aux_condPrefix_split G k x
  have hx : condPrefix G (k + 1) x = condPrefix G (k + 1) (Function.update x k (x k)) := by
    rw [Function.update_eq_self]
  unfold mgDiff
  cases hxk : x k
  · rw [hxk] at hx
    rw [hx]
    simp only [sgn]
    norm_num
    linarith
  · rw [hxk] at hx
    rw [hx]
    simp only [sgn]
    norm_num
    linarith

theorem mgDiff_predictable {N : ℕ} (G : (Fin N → Bool) → ℝ) : Predictable (mgDiff G) := by
  intro k x y hxy
  have key : ∀ (c : Bool) (z : Fin N → Bool),
      (fun j : Fin N => if (j : ℕ) < k + 1 then Function.update x k c j else z j) =
        (fun j : Fin N => if (j : ℕ) < k + 1 then Function.update y k c j else z j) := by
    intro c z
    funext j
    split_ifs with hj
    · by_cases hjk : j = k
      · subst hjk
        simp
      · rw [Function.update_of_ne hjk, Function.update_of_ne hjk]
        apply hxy
        have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
        rw [Fin.lt_def]
        omega
    · rfl
  simp only [mgDiff, condPrefix, key]

theorem sub_avg_eq_sum_mgDiff {N : ℕ} (G : (Fin N → Bool) → ℝ) (x : Fin N → Bool) :
    G x - cubeAvg N G = ∑ k, sgn (x k) * mgDiff G k x := by
  calc G x - cubeAvg N G = condPrefix G N x - condPrefix G 0 x := by
        rw [cube_aux_condPrefix_top, cube_aux_condPrefix_zero]
    _ = ∑ i ∈ Finset.range N, (condPrefix G (i + 1) x - condPrefix G i x) :=
        (Finset.sum_range_sub (fun i => condPrefix G i x) N).symm
    _ = ∑ k : Fin N, (condPrefix G (k + 1) x - condPrefix G k x) :=
        (Fin.sum_univ_eq_sum_range (fun i => condPrefix G (i + 1) x - condPrefix G i x) N).symm
    _ = ∑ k, sgn (x k) * mgDiff G k x :=
        Finset.sum_congr rfl (fun k _ => cube_aux_condPrefix_step G k x)

/- ### Exponential martingale and Chernoff -/

lemma cube_aux_sgn_not (c : Bool) : sgn (!c) = - sgn c := by
  cases c <;> simp [sgn]

/-- Pointwise step of the exponential supermartingale. -/
lemma cube_aux_exp_pair (a c S : ℝ) (hc : a ^ 2 / 2 = c) :
    Real.exp (a - c + S) + Real.exp (-a - c + S) ≤ 2 * Real.exp S := by
  have h1 : Real.exp (a - c + S) = Real.exp a * Real.exp (S - c) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-a - c + S) = Real.exp (-a) * Real.exp (S - c) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (a ^ 2 / 2) * Real.exp (S - c) = Real.exp S := by
    rw [← Real.exp_add, hc]; ring_nf
  have hcosh := Real.cosh_le_exp_half_sq a
  rw [Real.cosh_eq] at hcosh
  have hpos : 0 < Real.exp (S - c) := Real.exp_pos _
  rw [h1, h2, ← h3]
  nlinarith

lemma cube_aux_mgf_partial {N : ℕ} (b : Fin N → (Fin N → Bool) → ℝ) (hb : Predictable b)
    (l : ℝ) (m : ℕ) (hm : m ≤ N) :
    ∑ x, Real.exp (∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
      (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)) ≤ 2 ^ N := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have hmN : m < N := hm
    set km : Fin N := ⟨m, hmN⟩ with hkm
    have hfil : Finset.univ.filter (fun k : Fin N => (k : ℕ) < m + 1) =
        insert km (Finset.univ.filter (fun k : Fin N => (k : ℕ) < m)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, km,
        Fin.ext_iff]
      omega
    have hnot : km ∉ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m) := by
      simp [km]
    -- the partial sum does not see coordinate `km`
    have hSflip : ∀ x : Fin N → Bool,
        ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
          (l * sgn (Function.update x km (!x km) k) * b k (Function.update x km (!x km)) -
            l ^ 2 / 2 * b k (Function.update x km (!x km)) ^ 2) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
          (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2) := by
      intro x
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      have hne : k ≠ km := by
        intro h
        rw [h] at hk
        simp [km] at hk
      have hb' : b k (Function.update x km (!x km)) = b k x := by
        apply hb
        intro j hj
        have : j ≠ km := by
          intro h
          rw [h, Fin.lt_def] at hj
          simp only [km] at hj
          omega
        exact Function.update_of_ne this _ _
      rw [hb', Function.update_of_ne hne]
    have hbflip : ∀ x : Fin N → Bool, b km (Function.update x km (!x km)) = b km x := by
      intro x
      apply hb
      intro j hj
      exact Function.update_of_ne (ne_of_lt hj) _ _
    have hpt : ∀ x : Fin N → Bool,
        Real.exp ((l * sgn (x km) * b km x - l ^ 2 / 2 * b km x ^ 2) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)) +
          Real.exp ((l * sgn (Function.update x km (!x km) km) *
              b km (Function.update x km (!x km)) -
              l ^ 2 / 2 * b km (Function.update x km (!x km)) ^ 2) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (Function.update x km (!x km) k) * b k (Function.update x km (!x km)) -
                l ^ 2 / 2 * b k (Function.update x km (!x km)) ^ 2)) ≤
        2 * Real.exp (∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)) := by
      intro x
      rw [hSflip, hbflip, Function.update_self, cube_aux_sgn_not]
      have := cube_aux_exp_pair (l * sgn (x km) * b km x) (l ^ 2 / 2 * b km x ^ 2)
        (∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
          (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2))
        (by rw [mul_pow, mul_pow, sgn_sq]; ring)
      convert this using 3
      ring
    calc ∑ x, Real.exp (∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m + 1),
          (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2))
        = ∑ x, Real.exp ((l * sgn (x km) * b km x - l ^ 2 / 2 * b km x ^ 2) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hfil, Finset.sum_insert hnot]
      _ = (∑ x, Real.exp ((l * sgn (x km) * b km x - l ^ 2 / 2 * b km x ^ 2) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)) +
          ∑ x, Real.exp ((l * sgn (Function.update x km (!x km) km) *
              b km (Function.update x km (!x km)) -
              l ^ 2 / 2 * b km (Function.update x km (!x km)) ^ 2) +
            ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (Function.update x km (!x km) k) * b k (Function.update x km (!x km)) -
                l ^ 2 / 2 * b k (Function.update x km (!x km)) ^ 2))) / 2 := by
          rw [cube_aux_sum_flip km (fun x => Real.exp ((l * sgn (x km) * b km x -
            l ^ 2 / 2 * b km x ^ 2) + ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)))]
          ring
      _ ≤ (∑ x, 2 * Real.exp (∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2))) / 2 := by
          rw [← Finset.sum_add_distrib]
          gcongr with x
          exact hpt x
      _ = ∑ x, Real.exp (∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) < m),
              (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2)) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ 2 ^ N := ih (by omega)

theorem cube_mgf_le_one {N : ℕ} (b : Fin N → (Fin N → Bool) → ℝ) (hb : Predictable b) (l : ℝ) :
    cubeAvg N (fun x => Real.exp (∑ k, (l * sgn (x k) * b k x - l ^ 2 / 2 * b k x ^ 2))) ≤ 1 := by
  have h := cube_aux_mgf_partial b hb l N le_rfl
  rw [Finset.filter_true_of_mem (fun k _ => k.isLt)] at h
  unfold cubeAvg
  rw [div_le_one (by positivity)]
  exact h


theorem cube_tail_upper {N : ℕ} (G : (Fin N → Bool) → ℝ) (v t : ℝ) (hv : 0 < v) (ht : 0 ≤ t)
    (hsum : ∀ x, ∑ k, mgDiff G k x ^ 2 ≤ v) :
    cubeProb N (fun x => t ≤ G x - cubeAvg N G) ≤ Real.exp (-t ^ 2 / (2 * v)) := by
  classical
  set l := t / v with hl
  have hl0 : 0 ≤ l := div_nonneg ht hv.le
  rw [cubeProb_eq_cubeAvg]
  refine le_trans (cubeAvg_mono (G := fun x => Real.exp (-t ^ 2 / (2 * v)) *
    Real.exp (∑ k, (l * sgn (x k) * mgDiff G k x - l ^ 2 / 2 * mgDiff G k x ^ 2))) ?_) ?_
  · intro x
    split_ifs with h
    · rw [← Real.exp_add]
      apply Real.one_le_exp
      have h1 : ∑ k, (l * sgn (x k) * mgDiff G k x - l ^ 2 / 2 * mgDiff G k x ^ 2) =
          l * (G x - cubeAvg N G) - l ^ 2 / 2 * ∑ k, mgDiff G k x ^ 2 := by
        rw [sub_avg_eq_sum_mgDiff, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [h1]
      have h2 := hsum x
      have h3 : l * t ≤ l * (G x - cubeAvg N G) := mul_le_mul_of_nonneg_left h hl0
      have h4 : l ^ 2 / 2 * ∑ k, mgDiff G k x ^ 2 ≤ l ^ 2 / 2 * v := by gcongr
      have h5 : -t ^ 2 / (2 * v) + l * t - l ^ 2 / 2 * v = 0 := by
        rw [hl]
        field_simp
        ring
      linarith
    · positivity
  · rw [cubeAvg_smul]
    calc Real.exp (-t ^ 2 / (2 * v)) *
          cubeAvg N (fun x => Real.exp (∑ k, (l * sgn (x k) * mgDiff G k x -
            l ^ 2 / 2 * mgDiff G k x ^ 2)))
        ≤ Real.exp (-t ^ 2 / (2 * v)) * 1 := by
          gcongr
          exact cube_mgf_le_one _ (mgDiff_predictable G) l
      _ = Real.exp (-t ^ 2 / (2 * v)) := mul_one _

theorem cube_tail {N : ℕ} (G : (Fin N → Bool) → ℝ) (v t : ℝ) (hv : 0 < v) (ht : 0 ≤ t)
    (hsum : ∀ x, ∑ k, mgDiff G k x ^ 2 ≤ v) :
    cubeProb N (fun x => t ≤ |G x - cubeAvg N G|) ≤ 2 * Real.exp (-t ^ 2 / (2 * v)) := by
  have hneg_avg : cubeAvg N (fun x => -G x) = -cubeAvg N G := by
    unfold cubeAvg
    rw [Finset.sum_neg_distrib, neg_div]
  have hneg_cond : ∀ k x, condPrefix (fun x => -G x) k x = -condPrefix G k x := by
    intro k x
    unfold condPrefix cubeAvg
    rw [Finset.sum_neg_distrib, neg_div]
  have hneg_mg : ∀ k x, mgDiff (fun x => -G x) k x = -mgDiff G k x := by
    intro k x
    unfold mgDiff
    rw [hneg_cond, hneg_cond]
    ring
  have h1 := cube_tail_upper G v t hv ht hsum
  have h2 := cube_tail_upper (fun x => -G x) v t hv ht (by
    intro x
    simp only [hneg_mg, neg_sq]
    exact hsum x)
  calc cubeProb N (fun x => t ≤ |G x - cubeAvg N G|)
      ≤ cubeProb N (fun x => t ≤ G x - cubeAvg N G ∨
          t ≤ (fun x => -G x) x - cubeAvg N (fun x => -G x)) := by
        apply cubeProb_mono
        intro x hx
        rw [hneg_avg]
        rcases le_abs.mp hx with h | h
        · left
          exact h
        · right
          linarith
    _ ≤ cubeProb N (fun x => t ≤ G x - cubeAvg N G) +
          cubeProb N (fun x => t ≤ (fun x => -G x) x - cubeAvg N (fun x => -G x)) :=
        cubeProb_or_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * v)) + Real.exp (-t ^ 2 / (2 * v)) := add_le_add h1 h2
    _ = 2 * Real.exp (-t ^ 2 / (2 * v)) := by ring

end E522

end

/- ## Section: `Smooth` -/

section

/-
# Calculus of the smooth test functions `φ_δ(z) = ½log(|z|²+δ²)` and `ψ_β(z) = β²/(|z|²+β²)`

All bounds are proved along lines: for fixed `z, w` put `q(t) = |z + t w|² + δ²`
(a real quadratic in `t`, `q ≥ δ²`, `|q'| ≤ 2√q |w|`, `q'' = 2|w|²`), and use 1D Taylor
(`taylor_mean_remainder_lagrange` or explicit integral forms) / mean value inequalities.

Useful derivative formulas for `u(t) = ½ log q(t)`:
`u' = q'/(2q)`, `u'' = |w|²/q − q'²/(2q²)`, `u''' = −(3/2) q' q''/q² + q'³/q³`,
so `|u''| ≤ 3|w|²/δ²`, `|u'''| ≤ 14 |w|³/δ³`.
For `v(t) = β²/q(t)`: `v' = −β² q'/q²`, `|v''| ≤ 10 |w|²/β²`.
-/

open Real Complex

namespace E522

/- ### Auxiliary one-variable calculus -/

/-- Fencing lemma on `[0,1]` with a differentiable bound. -/
lemma smooth_aux_step {g g' B B' : ℝ → ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hB : ∀ t, HasDerivAt B (B' t) t)
    (h0 : |g 0| ≤ B 0) (hb : ∀ t ∈ Set.Icc (0:ℝ) 1, |g' t| ≤ B' t) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, |g t| ≤ B t := by
  intro t ht
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g) (f' := g') (a := 0) (b := 1)
    (B := B) (B' := B')
    (fun x _ => (hg x).continuousAt.continuousWithinAt) (fun x _ => (hg x).hasDerivWithinAt)
    (by simpa [Real.norm_eq_abs] using h0) hB
    (fun x hx => by simpa [Real.norm_eq_abs] using hb x (Set.Ico_subset_Icc_self hx)) ht
  simpa [Real.norm_eq_abs] using this

lemma smooth_aux_hasDerivAt_lin (M : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => M * t) M t := by
  simpa using (hasDerivAt_id t).const_mul M

lemma smooth_aux_hasDerivAt_sq (M : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => M * t ^ 2 / 2) (M * t) t := by
  have := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
  exact this.congr_deriv (by norm_num; ring)

lemma smooth_aux_hasDerivAt_cube (M : ℝ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => M * t ^ 3 / 6) (M * t ^ 2 / 2) t := by
  have := ((hasDerivAt_pow 3 t).const_mul M).div_const 6
  exact this.congr_deriv (by norm_num; ring)

/-- Second order Taylor bound on `[0,1]`. -/
lemma smooth_aux_taylor2 {f f1 f2 : ℝ → ℝ} {M : ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hM : ∀ t ∈ Set.Icc (0:ℝ) 1, |f2 t| ≤ M) :
    |f 1 - f 0 - f1 0| ≤ M / 2 := by
  have s1 : ∀ t ∈ Set.Icc (0:ℝ) 1, |f1 t - f1 0| ≤ M * t := by
    apply smooth_aux_step (g' := f2) (B' := fun _ => M)
    · intro t; exact (hf1 t).sub_const (f1 0)
    · intro t; exact smooth_aux_hasDerivAt_lin M t
    · simp
    · exact hM
  have s2 : ∀ t ∈ Set.Icc (0:ℝ) 1, |f t - f 0 - t * f1 0| ≤ M * t ^ 2 / 2 := by
    apply smooth_aux_step (g' := fun t => f1 t - f1 0) (B' := fun t => M * t)
    · intro t
      have := ((hf t).sub_const (f 0)).sub ((hasDerivAt_id t).mul_const (f1 0))
      exact this.congr_deriv (by simp)
    · intro t; exact smooth_aux_hasDerivAt_sq M t
    · simp
    · exact s1
  have h := s2 1 (by norm_num)
  have e : f 1 - f 0 - 1 * f1 0 = f 1 - f 0 - f1 0 := by ring
  have e2 : M * 1 ^ 2 / 2 = M / 2 := by ring
  rw [e, e2] at h
  exact h

/-- Third order Taylor bound on `[0,1]`. -/
lemma smooth_aux_taylor3 {f f1 f2 f3 : ℝ → ℝ} {M : ℝ}
    (hf : ∀ t, HasDerivAt f (f1 t) t) (hf1 : ∀ t, HasDerivAt f1 (f2 t) t)
    (hf2 : ∀ t, HasDerivAt f2 (f3 t) t)
    (hM : ∀ t ∈ Set.Icc (0:ℝ) 1, |f3 t| ≤ M) :
    |f 1 - f 0 - f1 0 - f2 0 / 2| ≤ M / 6 := by
  have s1 : ∀ t ∈ Set.Icc (0:ℝ) 1, |f2 t - f2 0| ≤ M * t := by
    apply smooth_aux_step (g' := f3) (B' := fun _ => M)
    · intro t; exact (hf2 t).sub_const (f2 0)
    · intro t; exact smooth_aux_hasDerivAt_lin M t
    · simp
    · exact hM
  have s2 : ∀ t ∈ Set.Icc (0:ℝ) 1, |f1 t - f1 0 - t * f2 0| ≤ M * t ^ 2 / 2 := by
    apply smooth_aux_step (g' := fun t => f2 t - f2 0) (B' := fun t => M * t)
    · intro t
      have := ((hf1 t).sub_const (f1 0)).sub ((hasDerivAt_id t).mul_const (f2 0))
      exact this.congr_deriv (by simp)
    · intro t; exact smooth_aux_hasDerivAt_sq M t
    · simp
    · exact s1
  have s3 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |f t - f 0 - t * f1 0 - t ^ 2 / 2 * f2 0| ≤ M * t ^ 3 / 6 := by
    apply smooth_aux_step (g' := fun t => f1 t - f1 0 - t * f2 0) (B' := fun t => M * t ^ 2 / 2)
    · intro t
      have := (((hf t).sub_const (f 0)).sub ((hasDerivAt_id t).mul_const (f1 0))).sub
        (((hasDerivAt_pow 2 t).div_const 2).mul_const (f2 0))
      exact this.congr_deriv (by norm_num)
    · intro t; exact smooth_aux_hasDerivAt_cube M t
    · simp
    · exact s2
  have h := s3 1 (by norm_num)
  have e : f 1 - f 0 - 1 * f1 0 - 1 ^ 2 / 2 * f2 0 = f 1 - f 0 - f1 0 - f2 0 / 2 := by ring
  have e2 : M * 1 ^ 3 / 6 = M / 6 := by ring
  rw [e, e2] at h
  exact h

/- ### The quadratic `q(t) = A t² + B t + C` and derivatives along it -/

lemma smooth_aux_quad_hasDerivAt (A B C t : ℝ) :
    HasDerivAt (fun t => A * t ^ 2 + B * t + C) (2 * A * t + B) t := by
  have := (((hasDerivAt_pow 2 t).const_mul A).add ((hasDerivAt_id' t).const_mul B)).add_const C
  exact this.congr_deriv (by norm_num; ring)

lemma smooth_aux_lin_hasDerivAt (A B t : ℝ) :
    HasDerivAt (fun t => 2 * A * t + B) (2 * A) t := by
  have := ((hasDerivAt_id' t).const_mul (2 * A)).add_const B
  exact this.congr_deriv (by ring)

lemma smooth_aux_u_hasDerivAt (A B C : ℝ) (hq : ∀ t, 0 < A * t ^ 2 + B * t + C) (t : ℝ) :
    HasDerivAt (fun t => Real.log (A * t ^ 2 + B * t + C) / 2)
      ((2 * A * t + B) / (2 * (A * t ^ 2 + B * t + C))) t := by
  have h := ((smooth_aux_quad_hasDerivAt A B C t).log (hq t).ne').div_const 2
  have hq0 := (hq t).ne'
  refine h.congr_deriv ?_
  generalize A * t ^ 2 + B * t + C = Q at hq0 ⊢
  field_simp

lemma smooth_aux_u1_hasDerivAt (A B C : ℝ) (hq : ∀ t, 0 < A * t ^ 2 + B * t + C) (t : ℝ) :
    HasDerivAt (fun t => (2 * A * t + B) / (2 * (A * t ^ 2 + B * t + C)))
      (A / (A * t ^ 2 + B * t + C) - (2 * A * t + B) ^ 2 / (2 * (A * t ^ 2 + B * t + C) ^ 2)) t := by
  have hN := smooth_aux_lin_hasDerivAt A B t
  have hD := (smooth_aux_quad_hasDerivAt A B C t).const_mul 2
  have hq0 := (hq t).ne'
  have h := hN.fun_div hD (mul_ne_zero two_ne_zero hq0)
  refine h.congr_deriv ?_
  generalize A * t ^ 2 + B * t + C = Q at hq0 ⊢
  generalize 2 * A * t + B = N
  field_simp

lemma smooth_aux_u2_hasDerivAt (A B C : ℝ) (hq : ∀ t, 0 < A * t ^ 2 + B * t + C) (t : ℝ) :
    HasDerivAt
      (fun t => A / (A * t ^ 2 + B * t + C) - (2 * A * t + B) ^ 2 / (2 * (A * t ^ 2 + B * t + C) ^ 2))
      (-3 * A * (2 * A * t + B) / (A * t ^ 2 + B * t + C) ^ 2
        + (2 * A * t + B) ^ 3 / (A * t ^ 2 + B * t + C) ^ 3) t := by
  have hN := smooth_aux_lin_hasDerivAt A B t
  have hQ := smooth_aux_quad_hasDerivAt A B C t
  have hq0 := (hq t).ne'
  have h1 := (hasDerivAt_const t A).fun_div hQ hq0
  have h2 := (hN.fun_pow 2).fun_div ((hQ.fun_pow 2).const_mul 2)
    (mul_ne_zero two_ne_zero (pow_ne_zero 2 hq0))
  refine (h1.fun_sub h2).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  generalize A * t ^ 2 + B * t + C = Q at hq0 ⊢
  generalize 2 * A * t + B = N
  field_simp
  ring

lemma smooth_aux_v_hasDerivAt (A B C β : ℝ) (hq : ∀ t, 0 < A * t ^ 2 + B * t + C) (t : ℝ) :
    HasDerivAt (fun t => β ^ 2 / (A * t ^ 2 + B * t + C))
      (-β ^ 2 * (2 * A * t + B) / (A * t ^ 2 + B * t + C) ^ 2) t := by
  have hQ := smooth_aux_quad_hasDerivAt A B C t
  have hq0 := (hq t).ne'
  have h1 := (hasDerivAt_const t (β ^ 2)).fun_div hQ hq0
  refine h1.congr_deriv ?_
  generalize A * t ^ 2 + B * t + C = Q at hq0 ⊢
  generalize 2 * A * t + B = N
  field_simp
  ring

lemma smooth_aux_v1_hasDerivAt (A B C β : ℝ) (hq : ∀ t, 0 < A * t ^ 2 + B * t + C) (t : ℝ) :
    HasDerivAt (fun t => -β ^ 2 * (2 * A * t + B) / (A * t ^ 2 + B * t + C) ^ 2)
      (-2 * β ^ 2 * A / (A * t ^ 2 + B * t + C) ^ 2
        + 2 * β ^ 2 * (2 * A * t + B) ^ 2 / (A * t ^ 2 + B * t + C) ^ 3) t := by
  have hN : HasDerivAt (fun t => -β ^ 2 * (2 * A * t + B)) (-β ^ 2 * (2 * A)) t :=
    (smooth_aux_lin_hasDerivAt A B t).const_mul (-β ^ 2)
  have hQ := smooth_aux_quad_hasDerivAt A B C t
  have hq0 := (hq t).ne'
  have h := hN.fun_div (hQ.fun_pow 2) (pow_ne_zero 2 hq0)
  refine h.congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  generalize A * t ^ 2 + B * t + C = Q at hq0 ⊢
  generalize 2 * A * t + B = N
  field_simp
  ring

/- ### Pointwise bounds on the derivatives -/

lemma smooth_aux_u2_bound {A N Q δ : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hQ : δ ^ 2 ≤ Q)
    (hN : N ^ 2 ≤ 4 * A * Q) :
    |A / Q - N ^ 2 / (2 * Q ^ 2)| ≤ 3 / δ ^ 2 * A := by
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hQ0 : Q ≠ 0 := hQpos.ne'
  have h1 : 0 ≤ A / Q := div_nonneg hA hQpos.le
  have h2 : A / Q ≤ A / δ ^ 2 := div_le_div_of_nonneg_left hA (by positivity) hQ
  have h3 : 0 ≤ N ^ 2 / (2 * Q ^ 2) := by positivity
  have h4 : N ^ 2 / (2 * Q ^ 2) ≤ 2 * (A / Q) := by
    calc N ^ 2 / (2 * Q ^ 2) ≤ (4 * A * Q) / (2 * Q ^ 2) :=
          div_le_div_of_nonneg_right hN (by positivity)
      _ = 2 * (A / Q) := by field_simp; ring
  have h5 : 3 / δ ^ 2 * A = 3 * (A / δ ^ 2) := by ring
  have h6 : 0 ≤ A / δ ^ 2 := by positivity
  rw [h5, abs_le]
  constructor <;> linarith

lemma smooth_aux_u3_bound {A N Q δ m : ℝ} (hδ : 0 < δ) (hm : 0 ≤ m) (hA : A = m ^ 2)
    (hQ : δ ^ 2 ≤ Q) (hN : N ^ 2 ≤ 4 * A * Q) :
    |-3 * A * N / Q ^ 2 + N ^ 3 / Q ^ 3| ≤ 14 * m ^ 3 / δ ^ 3 := by
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hQ0 : Q ≠ 0 := hQpos.ne'
  have e : -3 * A * N / Q ^ 2 + N ^ 3 / Q ^ 3 = (N / Q) * ((N / Q) ^ 2 - 3 * (A / Q)) := by
    field_simp
    ring
  have hX2 : (N / Q) ^ 2 ≤ 4 * (A / Q) := by
    calc (N / Q) ^ 2 = N ^ 2 / Q ^ 2 := by rw [div_pow]
      _ ≤ (4 * A * Q) / Q ^ 2 := div_le_div_of_nonneg_right hN (by positivity)
      _ = 4 * (A / Q) := by field_simp
  have hAQ0 : 0 ≤ A / Q := div_nonneg (by rw [hA]; positivity) hQpos.le
  have hAQ : A / Q ≤ m ^ 2 / δ ^ 2 := by
    rw [hA]; exact div_le_div_of_nonneg_left (sq_nonneg m) (by positivity) hQ
  have hX : |N / Q| ≤ 2 * m / δ := by
    apply abs_le_of_sq_le_sq _ (by positivity)
    have : (2 * m / δ) ^ 2 = 4 * (m ^ 2 / δ ^ 2) := by ring
    rw [this]; linarith
  have hY : |(N / Q) ^ 2 - 3 * (A / Q)| ≤ 3 * (m ^ 2 / δ ^ 2) := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (N / Q)]
  rw [e, abs_mul]
  calc |N / Q| * |(N / Q) ^ 2 - 3 * (A / Q)| ≤ (2 * m / δ) * (3 * (m ^ 2 / δ ^ 2)) :=
        mul_le_mul hX hY (abs_nonneg _) (by positivity)
    _ = 6 * m ^ 3 / δ ^ 3 := by ring
    _ ≤ 14 * m ^ 3 / δ ^ 3 := by gcongr; norm_num

lemma smooth_aux_v2_bound {A N Q β : ℝ} (hβ : 0 < β) (hA : 0 ≤ A) (hQ : β ^ 2 ≤ Q)
    (hN : N ^ 2 ≤ 4 * A * Q) :
    |-2 * β ^ 2 * A / Q ^ 2 + 2 * β ^ 2 * N ^ 2 / Q ^ 3| ≤ 10 / β ^ 2 * A := by
  have hQpos : 0 < Q := lt_of_lt_of_le (by positivity) hQ
  have hQ0 : Q ≠ 0 := hQpos.ne'
  have e : -2 * β ^ 2 * A / Q ^ 2 + 2 * β ^ 2 * N ^ 2 / Q ^ 3
      = (2 * β ^ 2 / Q ^ 2) * (N ^ 2 / Q - A) := by
    field_simp
    ring
  have hNQ : N ^ 2 / Q ≤ 4 * A := by rw [div_le_iff₀ hQpos]; linarith
  have hNQ0 : 0 ≤ N ^ 2 / Q := by positivity
  have hY : |N ^ 2 / Q - A| ≤ 3 * A := by rw [abs_le]; constructor <;> linarith
  have hK : 2 * β ^ 2 / Q ^ 2 ≤ 2 / β ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (β ^ 2) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (by positivity) hQ 2
    nlinarith
  rw [e, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * β ^ 2 / Q ^ 2)]
  calc (2 * β ^ 2 / Q ^ 2) * |N ^ 2 / Q - A| ≤ (2 / β ^ 2) * (3 * A) :=
        mul_le_mul hK hY (abs_nonneg _) (by positivity)
    _ = 6 / β ^ 2 * A := by ring
    _ ≤ 10 / β ^ 2 * A := by gcongr; norm_num

/- ### Taylor bounds for the explicit one-variable functions -/

lemma smooth_aux_phi_taylor2_abc {δ A B C : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A)
    (hqge : ∀ t, δ ^ 2 ≤ A * t ^ 2 + B * t + C)
    (hdisc : ∀ t, (2 * A * t + B) ^ 2 ≤ 4 * A * (A * t ^ 2 + B * t + C)) :
    |Real.log (A + B + C) / 2 - Real.log C / 2 - B / (2 * C)| ≤ 3 / δ ^ 2 * A / 2 := by
  have hq : ∀ t, 0 < A * t ^ 2 + B * t + C := fun t => lt_of_lt_of_le (by positivity) (hqge t)
  have key := smooth_aux_taylor2 (f := fun t => Real.log (A * t ^ 2 + B * t + C) / 2)
    (f1 := fun t => (2 * A * t + B) / (2 * (A * t ^ 2 + B * t + C)))
    (f2 := fun t => A / (A * t ^ 2 + B * t + C)
      - (2 * A * t + B) ^ 2 / (2 * (A * t ^ 2 + B * t + C) ^ 2))
    (M := 3 / δ ^ 2 * A)
    (smooth_aux_u_hasDerivAt A B C hq) (smooth_aux_u1_hasDerivAt A B C hq)
    (fun t _ => smooth_aux_u2_bound hδ hA (hqge t) (hdisc t))
  have key' : |Real.log (A * 1 ^ 2 + B * 1 + C) / 2 - Real.log (A * 0 ^ 2 + B * 0 + C) / 2
      - (2 * A * 0 + B) / (2 * (A * 0 ^ 2 + B * 0 + C))| ≤ 3 / δ ^ 2 * A / 2 := key
  have e1 : A * 1 ^ 2 + B * 1 + C = A + B + C := by ring
  have e0 : A * 0 ^ 2 + B * 0 + C = C := by ring
  have e2 : 2 * A * 0 + B = B := by ring
  rw [e1, e0, e2] at key'
  exact key'

lemma smooth_aux_phi_taylor3_abc {δ A B C m : ℝ} (hδ : 0 < δ) (hm : 0 ≤ m) (hA : A = m ^ 2)
    (hqge : ∀ t, δ ^ 2 ≤ A * t ^ 2 + B * t + C)
    (hdisc : ∀ t, (2 * A * t + B) ^ 2 ≤ 4 * A * (A * t ^ 2 + B * t + C)) :
    |Real.log (A + B + C) / 2 - Real.log C / 2 - B / (2 * C)
        - (A / C - B ^ 2 / (2 * C ^ 2)) / 2| ≤ 14 * m ^ 3 / δ ^ 3 / 6 := by
  have hq : ∀ t, 0 < A * t ^ 2 + B * t + C := fun t => lt_of_lt_of_le (by positivity) (hqge t)
  have key := smooth_aux_taylor3 (f := fun t => Real.log (A * t ^ 2 + B * t + C) / 2)
    (f1 := fun t => (2 * A * t + B) / (2 * (A * t ^ 2 + B * t + C)))
    (f2 := fun t => A / (A * t ^ 2 + B * t + C)
      - (2 * A * t + B) ^ 2 / (2 * (A * t ^ 2 + B * t + C) ^ 2))
    (f3 := fun t => -3 * A * (2 * A * t + B) / (A * t ^ 2 + B * t + C) ^ 2
        + (2 * A * t + B) ^ 3 / (A * t ^ 2 + B * t + C) ^ 3)
    (M := 14 * m ^ 3 / δ ^ 3)
    (smooth_aux_u_hasDerivAt A B C hq) (smooth_aux_u1_hasDerivAt A B C hq)
    (smooth_aux_u2_hasDerivAt A B C hq)
    (fun t _ => smooth_aux_u3_bound hδ hm hA (hqge t) (hdisc t))
  have key' : |Real.log (A * 1 ^ 2 + B * 1 + C) / 2 - Real.log (A * 0 ^ 2 + B * 0 + C) / 2
      - (2 * A * 0 + B) / (2 * (A * 0 ^ 2 + B * 0 + C))
      - (A / (A * 0 ^ 2 + B * 0 + C)
          - (2 * A * 0 + B) ^ 2 / (2 * (A * 0 ^ 2 + B * 0 + C) ^ 2)) / 2|
      ≤ 14 * m ^ 3 / δ ^ 3 / 6 := key
  have e1 : A * 1 ^ 2 + B * 1 + C = A + B + C := by ring
  have e0 : A * 0 ^ 2 + B * 0 + C = C := by ring
  have e2 : 2 * A * 0 + B = B := by ring
  rw [e1, e0, e2] at key'
  exact key'

lemma smooth_aux_psi_taylor2_abc {β A B C : ℝ} (hβ : 0 < β) (hA : 0 ≤ A)
    (hqge : ∀ t, β ^ 2 ≤ A * t ^ 2 + B * t + C)
    (hdisc : ∀ t, (2 * A * t + B) ^ 2 ≤ 4 * A * (A * t ^ 2 + B * t + C)) :
    |β ^ 2 / (A + B + C) - β ^ 2 / C - (-β ^ 2 * B / C ^ 2)| ≤ 10 / β ^ 2 * A / 2 := by
  have hq : ∀ t, 0 < A * t ^ 2 + B * t + C := fun t => lt_of_lt_of_le (by positivity) (hqge t)
  have key := smooth_aux_taylor2 (f := fun t => β ^ 2 / (A * t ^ 2 + B * t + C))
    (f1 := fun t => -β ^ 2 * (2 * A * t + B) / (A * t ^ 2 + B * t + C) ^ 2)
    (f2 := fun t => -2 * β ^ 2 * A / (A * t ^ 2 + B * t + C) ^ 2
        + 2 * β ^ 2 * (2 * A * t + B) ^ 2 / (A * t ^ 2 + B * t + C) ^ 3)
    (M := 10 / β ^ 2 * A)
    (smooth_aux_v_hasDerivAt A B C β hq) (smooth_aux_v1_hasDerivAt A B C β hq)
    (fun t _ => smooth_aux_v2_bound hβ hA (hqge t) (hdisc t))
  have key' : |β ^ 2 / (A * 1 ^ 2 + B * 1 + C) - β ^ 2 / (A * 0 ^ 2 + B * 0 + C)
      - (-β ^ 2 * (2 * A * 0 + B) / (A * 0 ^ 2 + B * 0 + C) ^ 2)| ≤ 10 / β ^ 2 * A / 2 := key
  have e1 : A * 1 ^ 2 + B * 1 + C = A + B + C := by ring
  have e0 : A * 0 ^ 2 + B * 0 + C = C := by ring
  have e2 : 2 * A * 0 + B = B := by ring
  rw [e1, e0, e2] at key'
  exact key'

/- ### Complex line geometry -/

lemma smooth_aux_norm_sq_line (z w : ℂ) (t : ℝ) :
    ‖z + (t : ℂ) * w‖ ^ 2 = ‖w‖ ^ 2 * t ^ 2 + 2 * (z * starRingEnd ℂ w).re * t + ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma smooth_aux_norm_sq_add (z w : ℂ) :
    ‖z + w‖ ^ 2 = ‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re + ‖z‖ ^ 2 := by
  have h := smooth_aux_norm_sq_line z w 1
  simp only [Complex.ofReal_one, one_mul, one_pow, mul_one] at h
  exact h

lemma smooth_aux_re_sq_le (z w : ℂ) :
    (z * starRingEnd ℂ w).re ^ 2 ≤ ‖z‖ ^ 2 * ‖w‖ ^ 2 := by
  have h := Complex.abs_re_le_norm (z * starRingEnd ℂ w)
  rw [norm_mul, Complex.norm_conj] at h
  have h2 : (z * starRingEnd ℂ w).re ^ 2 ≤ (‖z‖ * ‖w‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  linarith [h2, show (‖z‖ * ‖w‖) ^ 2 = ‖z‖ ^ 2 * ‖w‖ ^ 2 by ring]

lemma smooth_aux_q_ge (z w : ℂ) (δ t : ℝ) :
    δ ^ 2 ≤ ‖w‖ ^ 2 * t ^ 2 + 2 * (z * starRingEnd ℂ w).re * t + (‖z‖ ^ 2 + δ ^ 2) := by
  have h := smooth_aux_norm_sq_line z w t
  nlinarith [sq_nonneg ‖z + (t : ℂ) * w‖]

lemma smooth_aux_disc (z w : ℂ) (δ t : ℝ) :
    (2 * ‖w‖ ^ 2 * t + 2 * (z * starRingEnd ℂ w).re) ^ 2 ≤
      4 * ‖w‖ ^ 2 * (‖w‖ ^ 2 * t ^ 2 + 2 * (z * starRingEnd ℂ w).re * t + (‖z‖ ^ 2 + δ ^ 2)) := by
  have h := smooth_aux_re_sq_le z w
  have hw : 0 ≤ ‖w‖ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hw (sq_nonneg δ)]

lemma smooth_aux_phiD_add (δ : ℝ) (z w : ℂ) :
    phiD δ (z + w) =
      Real.log (‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re + (‖z‖ ^ 2 + δ ^ 2)) / 2 := by
  unfold phiD
  rw [smooth_aux_norm_sq_add]
  congr 2
  ring

lemma smooth_aux_psiB_add (β : ℝ) (z w : ℂ) :
    psiB β (z + w) = β ^ 2 / (‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re + (‖z‖ ^ 2 + β ^ 2)) := by
  unfold psiB
  rw [smooth_aux_norm_sq_add]
  congr 1
  ring

lemma smooth_aux_gphiD_re (δ : ℝ) (z w : ℂ) :
    (starRingEnd ℂ w * gphiD δ z).re = (z * starRingEnd ℂ w).re / (‖z‖ ^ 2 + δ ^ 2) := by
  rw [gphiD, ← mul_div_assoc, Complex.div_ofReal_re, mul_comm (starRingEnd ℂ w) z]

lemma smooth_aux_gpsiB_re (β : ℝ) (z w : ℂ) :
    (starRingEnd ℂ w * gpsiB β z).re
      = -(2 * β ^ 2 / (‖z‖ ^ 2 + β ^ 2) ^ 2) * (z * starRingEnd ℂ w).re := by
  rw [gpsiB]
  have : starRingEnd ℂ w * (-((2 * β ^ 2 / (‖z‖ ^ 2 + β ^ 2) ^ 2 : ℝ) : ℂ) * z)
      = ((-(2 * β ^ 2 / (‖z‖ ^ 2 + β ^ 2) ^ 2) : ℝ) : ℂ) * (z * starRingEnd ℂ w) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]

/- ### Algebraic Lipschitz bound for `gphiD` -/

lemma smooth_aux_gphiD_norm_eq (δ : ℝ) (z : ℂ) :
    ‖gphiD δ z‖ = ‖z‖ / (‖z‖ ^ 2 + δ ^ 2) := by
  rw [gphiD, norm_div, Complex.norm_of_nonneg (by positivity)]

lemma smooth_aux_gphiD_lip1 {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    ‖gphiD δ z - gphiD δ w‖ ≤ ‖z - w‖ / δ ^ 2 := by
  have hp : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have hq : 0 < ‖w‖ ^ 2 + δ ^ 2 := by positivity
  have hp' : ((‖z‖ ^ 2 + δ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : ((‖w‖ ^ 2 + δ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : gphiD δ z - gphiD δ w =
      (((δ ^ 2 : ℝ) : ℂ) * (z - w) + z * w * (starRingEnd ℂ w - starRingEnd ℂ z)) /
        (((‖z‖ ^ 2 + δ ^ 2 : ℝ) : ℂ) * ((‖w‖ ^ 2 + δ ^ 2 : ℝ) : ℂ)) := by
    rw [gphiD, gphiD, div_sub_div _ _ hp' hq']
    congr 1
    push_cast
    rw [← Complex.mul_conj', ← Complex.mul_conj']
    ring
  have hnum : ‖((δ ^ 2 : ℝ) : ℂ) * (z - w) + z * w * (starRingEnd ℂ w - starRingEnd ℂ z)‖ ≤
      (δ ^ 2 + ‖z‖ * ‖w‖) * ‖z - w‖ := by
    calc _ ≤ ‖((δ ^ 2 : ℝ) : ℂ) * (z - w)‖ + ‖z * w * (starRingEnd ℂ w - starRingEnd ℂ z)‖ :=
          norm_add_le _ _
      _ = δ ^ 2 * ‖z - w‖ + ‖z‖ * ‖w‖ * ‖z - w‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_of_nonneg (sq_nonneg δ), ← map_sub,
          Complex.norm_conj, norm_sub_rev w z]
      _ = (δ ^ 2 + ‖z‖ * ‖w‖) * ‖z - w‖ := by ring
  have hpq : δ ^ 2 * (δ ^ 2 + ‖z‖ * ‖w‖) ≤ (‖z‖ ^ 2 + δ ^ 2) * (‖w‖ ^ 2 + δ ^ 2) := by
    have h1 : 0 ≤ ‖z‖ * ‖w‖ := mul_nonneg (norm_nonneg z) (norm_nonneg w)
    nlinarith [sq_nonneg (‖z‖ - ‖w‖), mul_nonneg h1 h1, mul_nonneg h1 (sq_nonneg δ),
      mul_nonneg (sq_nonneg δ) (sq_nonneg (‖z‖ - ‖w‖))]
  rw [key, norm_div, norm_mul, Complex.norm_of_nonneg hp.le, Complex.norm_of_nonneg hq.le,
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc _ ≤ (δ ^ 2 + ‖z‖ * ‖w‖) * ‖z - w‖ * δ ^ 2 := by gcongr
    _ = ‖z - w‖ * (δ ^ 2 * (δ ^ 2 + ‖z‖ * ‖w‖)) := by ring
    _ ≤ ‖z - w‖ * ((‖z‖ ^ 2 + δ ^ 2) * (‖w‖ ^ 2 + δ ^ 2)) := by gcongr

/- ### Main statements -/

theorem phiD_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (phiD δ) := by
  unfold phiD
  have h : ∀ z : ℂ, ‖z‖ ^ 2 + δ ^ 2 ≠ 0 := fun z => by positivity
  exact (((continuous_norm.pow 2).add continuous_const).log h).div_const 2

theorem gphiD_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (gphiD δ) := by
  unfold gphiD
  have h : ∀ z : ℂ, (((‖z‖ ^ 2 + δ ^ 2 : ℝ)) : ℂ) ≠ 0 := fun z => by
    rw [Complex.ofReal_ne_zero]; positivity
  exact continuous_id.div
    (Complex.continuous_ofReal.comp ((continuous_norm.pow 2).add continuous_const)) h

theorem psiB_continuous {β : ℝ} (hβ : 0 < β) : Continuous (psiB β) := by
  unfold psiB
  have h : ∀ z : ℂ, ‖z‖ ^ 2 + β ^ 2 ≠ 0 := fun z => by positivity
  exact continuous_const.div ((continuous_norm.pow 2).add continuous_const) h

theorem gpsiB_continuous {β : ℝ} (hβ : 0 < β) : Continuous (gpsiB β) := by
  unfold gpsiB
  have h : ∀ z : ℂ, (‖z‖ ^ 2 + β ^ 2) ^ 2 ≠ 0 := fun z => by positivity
  exact (Complex.continuous_ofReal.comp (continuous_const.div
    (((continuous_norm.pow 2).add continuous_const).pow 2) h)).neg.mul continuous_id

theorem phiD_lipschitz {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    |phiD δ z - phiD δ w| ≤ ‖z - w‖ / (2 * δ) := by
  have hF : ∀ r : ℝ, HasDerivAt (fun r : ℝ => Real.log (r ^ 2 + δ ^ 2) / 2)
      (r / (r ^ 2 + δ ^ 2)) r := by
    intro r
    have hr : r ^ 2 + δ ^ 2 ≠ 0 := by positivity
    have := (((hasDerivAt_pow 2 r).add_const (δ ^ 2)).log hr).div_const 2
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp
  have hb : ∀ r : ℝ, ‖r / (r ^ 2 + δ ^ 2)‖ ≤ 1 / (2 * δ) := by
    intro r
    have hr : 0 < r ^ 2 + δ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr, div_le_div_iff₀ hr (by positivity)]
    nlinarith [sq_nonneg (|r| - δ), sq_abs r, abs_nonneg r]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun r : ℝ => Real.log (r ^ 2 + δ ^ 2) / 2)
    (fun x _ => (hF x).hasDerivWithinAt) (fun x _ => hb x) convex_univ
    (Set.mem_univ ‖w‖) (Set.mem_univ ‖z‖)
  simp only [Real.norm_eq_abs] at key
  have h2 := abs_norm_sub_norm_le z w
  calc |phiD δ z - phiD δ w|
      = |Real.log (‖z‖ ^ 2 + δ ^ 2) / 2 - Real.log (‖w‖ ^ 2 + δ ^ 2) / 2| := rfl
    _ ≤ 1 / (2 * δ) * |‖z‖ - ‖w‖| := key
    _ ≤ 1 / (2 * δ) * ‖z - w‖ := by gcongr
    _ = ‖z - w‖ / (2 * δ) := by ring

theorem gphiD_norm_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) : ‖gphiD δ z‖ ≤ 1 / (2 * δ) := by
  have hq : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  rw [smooth_aux_gphiD_norm_eq, div_le_div_iff₀ hq (by positivity)]
  nlinarith [sq_nonneg (‖z‖ - δ)]

theorem gphiD_lip {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    ‖gphiD δ z - gphiD δ w‖ ≤ 3 / δ ^ 2 * ‖z - w‖ := by
  calc ‖gphiD δ z - gphiD δ w‖ ≤ ‖z - w‖ / δ ^ 2 := smooth_aux_gphiD_lip1 hδ z w
    _ = 1 / δ ^ 2 * ‖z - w‖ := by ring
    _ ≤ 3 / δ ^ 2 * ‖z - w‖ := by gcongr; norm_num

/-- Second order Taylor bound for `φ_δ` with gradient `gphiD`. -/
theorem phiD_taylor2 {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    |phiD δ (z + w) - phiD δ z - (starRingEnd ℂ w * gphiD δ z).re| ≤ 3 / δ ^ 2 / 2 * ‖w‖ ^ 2 := by
  have h := smooth_aux_phi_taylor2_abc (δ := δ) (A := ‖w‖ ^ 2)
    (B := 2 * (z * starRingEnd ℂ w).re) (C := ‖z‖ ^ 2 + δ ^ 2) hδ (sq_nonneg _)
    (smooth_aux_q_ge z w δ) (smooth_aux_disc z w δ)
  have e : phiD δ (z + w) - phiD δ z - (starRingEnd ℂ w * gphiD δ z).re
      = Real.log (‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re + (‖z‖ ^ 2 + δ ^ 2)) / 2
        - Real.log (‖z‖ ^ 2 + δ ^ 2) / 2
        - 2 * (z * starRingEnd ℂ w).re / (2 * (‖z‖ ^ 2 + δ ^ 2)) := by
    rw [smooth_aux_phiD_add, smooth_aux_gphiD_re]
    unfold phiD
    generalize ‖z‖ ^ 2 + δ ^ 2 = C
    ring
  rw [e]
  calc _ ≤ 3 / δ ^ 2 * ‖w‖ ^ 2 / 2 := h
    _ = 3 / δ ^ 2 / 2 * ‖w‖ ^ 2 := by ring

/-- Third order Taylor bound for `φ_δ`; the quadratic term is `u''(0)/2` with
`u''(0) = |w|²/q − 2 Re(z w̄)²/q²`, `q = |z|²+δ²`. -/
theorem phiD_taylor3 {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    |phiD δ (z + w) - phiD δ z - (starRingEnd ℂ w * gphiD δ z).re
      - (‖w‖ ^ 2 / (‖z‖ ^ 2 + δ ^ 2)
          - 2 * (z * starRingEnd ℂ w).re ^ 2 / (‖z‖ ^ 2 + δ ^ 2) ^ 2) / 2|
      ≤ 7 / 3 * ‖w‖ ^ 3 / δ ^ 3 := by
  have h := smooth_aux_phi_taylor3_abc (δ := δ) (A := ‖w‖ ^ 2)
    (B := 2 * (z * starRingEnd ℂ w).re) (C := ‖z‖ ^ 2 + δ ^ 2) (m := ‖w‖) hδ (norm_nonneg w)
    rfl (smooth_aux_q_ge z w δ) (smooth_aux_disc z w δ)
  have e : phiD δ (z + w) - phiD δ z - (starRingEnd ℂ w * gphiD δ z).re
      - (‖w‖ ^ 2 / (‖z‖ ^ 2 + δ ^ 2)
          - 2 * (z * starRingEnd ℂ w).re ^ 2 / (‖z‖ ^ 2 + δ ^ 2) ^ 2) / 2
      = Real.log (‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re + (‖z‖ ^ 2 + δ ^ 2)) / 2
        - Real.log (‖z‖ ^ 2 + δ ^ 2) / 2
        - 2 * (z * starRingEnd ℂ w).re / (2 * (‖z‖ ^ 2 + δ ^ 2))
        - (‖w‖ ^ 2 / (‖z‖ ^ 2 + δ ^ 2)
          - (2 * (z * starRingEnd ℂ w).re) ^ 2 / (2 * (‖z‖ ^ 2 + δ ^ 2) ^ 2)) / 2 := by
    rw [smooth_aux_phiD_add, smooth_aux_gphiD_re]
    unfold phiD
    generalize ‖z‖ ^ 2 + δ ^ 2 = C
    ring
  rw [e]
  calc _ ≤ 14 * ‖w‖ ^ 3 / δ ^ 3 / 6 := h
    _ = 7 / 3 * ‖w‖ ^ 3 / δ ^ 3 := by ring

theorem gpsiB_norm_le {β : ℝ} (hβ : 0 < β) (z : ℂ) : ‖gpsiB β z‖ ≤ 1 / β := by
  have hq : 0 < ‖z‖ ^ 2 + β ^ 2 := by positivity
  rw [gpsiB, norm_mul, norm_neg, Complex.norm_of_nonneg (by positivity), div_mul_eq_mul_div,
    div_le_div_iff₀ (by positivity) hβ]
  have h1 : 2 * ‖z‖ * β ≤ ‖z‖ ^ 2 + β ^ 2 := by nlinarith [sq_nonneg (‖z‖ - β)]
  have h2 : β ^ 2 ≤ ‖z‖ ^ 2 + β ^ 2 := by nlinarith [sq_nonneg ‖z‖]
  have h3 : (2 * ‖z‖ * β) * β ^ 2 ≤ (‖z‖ ^ 2 + β ^ 2) * (‖z‖ ^ 2 + β ^ 2) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  nlinarith [h3]

theorem gpsiB_lip {β : ℝ} (hβ : 0 < β) (z w : ℂ) :
    ‖gpsiB β z - gpsiB β w‖ ≤ 10 / β ^ 2 * ‖z - w‖ := by
  have hp : 0 < ‖z‖ ^ 2 + β ^ 2 := by positivity
  have hq : 0 < ‖w‖ ^ 2 + β ^ 2 := by positivity
  have e : ∀ ζ : ℂ, gpsiB β ζ = ((-2 * β ^ 2 / (‖ζ‖ ^ 2 + β ^ 2) : ℝ) : ℂ) * gphiD β ζ := by
    intro ζ
    have hζ : (‖ζ‖ : ℂ) ^ 2 + (β : ℂ) ^ 2 ≠ 0 := by
      have : (0:ℝ) < ‖ζ‖ ^ 2 + β ^ 2 := by positivity
      exact_mod_cast this.ne'
    rw [gpsiB, gphiD]
    push_cast
    field_simp
  set a := -2 * β ^ 2 / (‖z‖ ^ 2 + β ^ 2) with ha
  set b := -2 * β ^ 2 / (‖w‖ ^ 2 + β ^ 2) with hb
  have e2 : gpsiB β z - gpsiB β w
      = (a : ℂ) * (gphiD β z - gphiD β w) + ((a - b : ℝ) : ℂ) * gphiD β w := by
    rw [e z, e w, ← ha, ← hb]; push_cast; ring
  have ha_le : |a| ≤ 2 := by
    rw [ha, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    rw [abs_of_nonpos (by nlinarith [sq_nonneg β])]
    nlinarith [sq_nonneg ‖z‖]
  have hk : |1 / (‖z‖ ^ 2 + β ^ 2) - 1 / (‖w‖ ^ 2 + β ^ 2)| ≤ ‖z - w‖ / β ^ 3 := by
    rw [div_sub_div _ _ hp.ne' hq.ne', abs_div, abs_of_pos (mul_pos hp hq),
      div_le_div_iff₀ (mul_pos hp hq) (by positivity)]
    have e3 : 1 * (‖w‖ ^ 2 + β ^ 2) - (‖z‖ ^ 2 + β ^ 2) * 1 = (‖w‖ - ‖z‖) * (‖w‖ + ‖z‖) := by
      ring
    rw [e3, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖w‖ + ‖z‖)]
    have h1 : |‖w‖ - ‖z‖| ≤ ‖z - w‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le z w
    have h2 : (‖w‖ + ‖z‖) * β ^ 3 ≤ (‖z‖ ^ 2 + β ^ 2) * (‖w‖ ^ 2 + β ^ 2) := by
      have i1 : 2 * ‖z‖ * β ≤ ‖z‖ ^ 2 + β ^ 2 := by nlinarith [sq_nonneg (‖z‖ - β)]
      have i2 : 2 * ‖w‖ * β ≤ ‖w‖ ^ 2 + β ^ 2 := by nlinarith [sq_nonneg (‖w‖ - β)]
      have i3 : β ^ 2 ≤ ‖z‖ ^ 2 + β ^ 2 := by nlinarith [sq_nonneg ‖z‖]
      have i4 : β ^ 2 ≤ ‖w‖ ^ 2 + β ^ 2 := by nlinarith [sq_nonneg ‖w‖]
      have j1 : (2 * ‖z‖ * β) * β ^ 2 ≤ (‖z‖ ^ 2 + β ^ 2) * (‖w‖ ^ 2 + β ^ 2) :=
        mul_le_mul i1 i4 (by positivity) (by positivity)
      have j2 : β ^ 2 * (2 * ‖w‖ * β) ≤ (‖z‖ ^ 2 + β ^ 2) * (‖w‖ ^ 2 + β ^ 2) :=
        mul_le_mul i3 i2 (by positivity) (by positivity)
      nlinarith [j1, j2]
    calc |‖w‖ - ‖z‖| * (‖w‖ + ‖z‖) * β ^ 3 ≤ ‖z - w‖ * ((‖w‖ + ‖z‖) * β ^ 3) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ‖z - w‖ * ((‖z‖ ^ 2 + β ^ 2) * (‖w‖ ^ 2 + β ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
  have hab : |a - b| ≤ 2 * ‖z - w‖ / β := by
    have e4 : a - b = -2 * β ^ 2 * (1 / (‖z‖ ^ 2 + β ^ 2) - 1 / (‖w‖ ^ 2 + β ^ 2)) := by
      rw [ha, hb]; ring
    rw [e4, abs_mul, abs_of_nonpos (by nlinarith [sq_nonneg β] : -2 * β ^ 2 ≤ 0)]
    calc -(-2 * β ^ 2) * |1 / (‖z‖ ^ 2 + β ^ 2) - 1 / (‖w‖ ^ 2 + β ^ 2)|
        ≤ -(-2 * β ^ 2) * (‖z - w‖ / β ^ 3) := by gcongr; nlinarith [sq_nonneg β]
      _ = 2 * ‖z - w‖ / β := by field_simp
  have hg := smooth_aux_gphiD_lip1 hβ z w
  have hgw := gphiD_norm_le hβ w
  rw [e2]
  calc ‖(a : ℂ) * (gphiD β z - gphiD β w) + ((a - b : ℝ) : ℂ) * gphiD β w‖
      ≤ ‖(a : ℂ) * (gphiD β z - gphiD β w)‖ + ‖((a - b : ℝ) : ℂ) * gphiD β w‖ := norm_add_le _ _
    _ = |a| * ‖gphiD β z - gphiD β w‖ + |a - b| * ‖gphiD β w‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs]
    _ ≤ 2 * (‖z - w‖ / β ^ 2) + (2 * ‖z - w‖ / β) * (1 / (2 * β)) := by
        gcongr
    _ = 3 / β ^ 2 * ‖z - w‖ := by field_simp; ring
    _ ≤ 10 / β ^ 2 * ‖z - w‖ := by gcongr; norm_num

/-- Second order Taylor bound for `ψ_β` with gradient `gpsiB`. -/
theorem psiB_taylor2 {β : ℝ} (hβ : 0 < β) (z w : ℂ) :
    |psiB β (z + w) - psiB β z - (starRingEnd ℂ w * gpsiB β z).re| ≤ 10 / β ^ 2 / 2 * ‖w‖ ^ 2 := by
  have h := smooth_aux_psi_taylor2_abc (β := β) (A := ‖w‖ ^ 2)
    (B := 2 * (z * starRingEnd ℂ w).re) (C := ‖z‖ ^ 2 + β ^ 2) hβ (sq_nonneg _)
    (smooth_aux_q_ge z w β) (smooth_aux_disc z w β)
  have e : psiB β (z + w) - psiB β z - (starRingEnd ℂ w * gpsiB β z).re
      = β ^ 2 / (‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re + (‖z‖ ^ 2 + β ^ 2))
        - β ^ 2 / (‖z‖ ^ 2 + β ^ 2)
        - (-β ^ 2 * (2 * (z * starRingEnd ℂ w).re) / (‖z‖ ^ 2 + β ^ 2) ^ 2) := by
    rw [smooth_aux_psiB_add, smooth_aux_gpsiB_re]
    unfold psiB
    generalize ‖z‖ ^ 2 + β ^ 2 = C
    ring
  rw [e]
  calc _ ≤ 10 / β ^ 2 * ‖w‖ ^ 2 / 2 := h
    _ = 10 / β ^ 2 / 2 * ‖w‖ ^ 2 := by ring

/-- The complex quantity `z²/(|z|²+δ²)²` appearing in the Lindeberg–Abel step. -/
noncomputable def Qfun (δ : ℝ) (z : ℂ) : ℂ := z ^ 2 / (((‖z‖ ^ 2 + δ ^ 2) ^ 2 : ℝ) : ℂ)

lemma smooth_aux_Qfun_eq (δ : ℝ) (z : ℂ) : Qfun δ z = gphiD δ z ^ 2 := by
  rw [Qfun, gphiD, div_pow, Complex.ofReal_pow]

theorem Qfun_continuous {δ : ℝ} (hδ : 0 < δ) : Continuous (Qfun δ) := by
  unfold Qfun
  have h : ∀ z : ℂ, (((‖z‖ ^ 2 + δ ^ 2) ^ 2 : ℝ) : ℂ) ≠ 0 := fun z => by
    rw [Complex.ofReal_ne_zero]; positivity
  exact (continuous_id.pow 2).div
    (Complex.continuous_ofReal.comp (((continuous_norm.pow 2).add continuous_const).pow 2)) h

theorem Qfun_norm_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) : ‖Qfun δ z‖ ≤ 1 / (4 * δ ^ 2) := by
  rw [smooth_aux_Qfun_eq, norm_pow]
  calc ‖gphiD δ z‖ ^ 2 ≤ (1 / (2 * δ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (gphiD_norm_le hδ z) 2
    _ = 1 / (4 * δ ^ 2) := by ring

theorem Qfun_lip {δ : ℝ} (hδ : 0 < δ) (z w : ℂ) :
    ‖Qfun δ z - Qfun δ w‖ ≤ 2 / δ ^ 3 * ‖z - w‖ := by
  rw [smooth_aux_Qfun_eq, smooth_aux_Qfun_eq]
  have e : gphiD δ z ^ 2 - gphiD δ w ^ 2
      = (gphiD δ z - gphiD δ w) * (gphiD δ z + gphiD δ w) := by ring
  rw [e, norm_mul]
  have h1 := smooth_aux_gphiD_lip1 hδ z w
  have h2 : ‖gphiD δ z + gphiD δ w‖ ≤ 1 / δ := by
    calc _ ≤ ‖gphiD δ z‖ + ‖gphiD δ w‖ := norm_add_le _ _
      _ ≤ 1 / (2 * δ) + 1 / (2 * δ) := add_le_add (gphiD_norm_le hδ z) (gphiD_norm_le hδ w)
      _ = 1 / δ := by field_simp; ring
  calc ‖gphiD δ z - gphiD δ w‖ * ‖gphiD δ z + gphiD δ w‖ ≤ (‖z - w‖ / δ ^ 2) * (1 / δ) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = 1 / δ ^ 3 * ‖z - w‖ := by field_simp
    _ ≤ 2 / δ ^ 3 * ‖z - w‖ := by gcongr; norm_num

/-- The algebraic identity behind the second order mismatch between a Rademacher
step `± a` and a complex Gaussian step `γ a`. -/
theorem second_order_mismatch (δ : ℝ) (z a : ℂ) :
    (‖a‖ ^ 2 / (‖z‖ ^ 2 + δ ^ 2) - 2 * (z * starRingEnd ℂ a).re ^ 2 / (‖z‖ ^ 2 + δ ^ 2) ^ 2)
      - (‖a‖ ^ 2 / (‖z‖ ^ 2 + δ ^ 2) - ‖z‖ ^ 2 * ‖a‖ ^ 2 / (‖z‖ ^ 2 + δ ^ 2) ^ 2)
      = -(starRingEnd ℂ a ^ 2 * Qfun δ z).re := by
  rw [Qfun, ← mul_div_assoc, Complex.div_ofReal_re]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/- ### Pointwise inequalities used for smoothing -/

theorem log_norm_le_phiD {δ : ℝ} (hδ : 0 < δ) {z : ℂ} (hz : z ≠ 0) :
    Real.log ‖z‖ ≤ phiD δ z := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.log (‖z‖ ^ 2) = 2 * Real.log ‖z‖ := by rw [Real.log_pow]; norm_num
  have h2 : Real.log (‖z‖ ^ 2) ≤ Real.log (‖z‖ ^ 2 + δ ^ 2) :=
    Real.log_le_log (by positivity) (by linarith [pow_pos hδ 2])
  rw [phiD]; linarith

theorem phiD_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (z : ℂ) :
    Real.log δ ≤ phiD δ z ∧ phiD δ z ≤ ‖z‖ ^ 2 / 2 := by
  have hq : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  constructor
  · have h1 : Real.log (δ ^ 2) = 2 * Real.log δ := by rw [Real.log_pow]; norm_num
    have h2 : Real.log (δ ^ 2) ≤ Real.log (‖z‖ ^ 2 + δ ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ‖z‖])
    rw [phiD]; linarith
  · have h1 := Real.log_le_sub_one_of_pos hq
    have h2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
    rw [phiD]; linarith

/-- Decomposition of the smoothing error `½ log(1 + δ²/|z|²)`. -/
theorem phiD_sub_log_le {η δ β : ℝ} (hη : 0 < η) (hηδ : η ≤ δ) (hδ1 : δ ≤ 1) (hβ : 0 < β)
    {z : ℂ} (hz : z ≠ 0) :
    phiD δ z - Real.log ‖z‖ ≤ δ ^ 2 / (2 * β ^ 2) + 2 * Real.log (2 * δ / η) * psiB β z
      + (if ‖z‖ < η then 1 + Real.log (1 / ‖z‖) else 0) := by
  have hδ : 0 < δ := lt_of_lt_of_le hη hηδ
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hq : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have hlogr : Real.log (‖z‖ ^ 2) = 2 * Real.log ‖z‖ := by rw [Real.log_pow]; norm_num
  have hT1 : 0 ≤ δ ^ 2 / (2 * β ^ 2) := by positivity
  have hL : 0 ≤ Real.log (2 * δ / η) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hη]; linarith
  have hψ : 0 ≤ psiB β z := div_nonneg (sq_nonneg β) (by positivity)
  have hT2 : 0 ≤ 2 * Real.log (2 * δ / η) * psiB β z :=
    mul_nonneg (mul_nonneg zero_le_two hL) hψ
  have hT3 : 0 ≤ (if ‖z‖ < η then 1 + Real.log (1 / ‖z‖) else 0) := by
    split_ifs with h
    · have h1 : 1 ≤ 1 / ‖z‖ := by rw [le_div_iff₀ hr]; linarith
      have := Real.log_nonneg h1
      linarith
    · exact le_refl 0
  have hD : phiD δ z - Real.log ‖z‖ = Real.log (‖z‖ ^ 2 + δ ^ 2) / 2 - Real.log ‖z‖ := rfl
  rcases le_or_gt β ‖z‖ with hβr | hrβ
  · -- `|z| ≥ β`
    have h1 : Real.log (‖z‖ ^ 2 + δ ^ 2) - Real.log (‖z‖ ^ 2) ≤ δ ^ 2 / ‖z‖ ^ 2 := by
      rw [← Real.log_div hq.ne' (by positivity)]
      have := Real.log_le_sub_one_of_pos (div_pos hq (by positivity : (0:ℝ) < ‖z‖ ^ 2))
      have e : (‖z‖ ^ 2 + δ ^ 2) / ‖z‖ ^ 2 - 1 = δ ^ 2 / ‖z‖ ^ 2 := by field_simp; ring
      linarith
    have h2 : δ ^ 2 / ‖z‖ ^ 2 ≤ δ ^ 2 / β ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg δ) (by positivity)
        (pow_le_pow_left₀ hβ.le hβr 2)
    have e : δ ^ 2 / (2 * β ^ 2) = (δ ^ 2 / β ^ 2) / 2 := by field_simp
    rw [hD]
    linarith
  · rcases le_or_gt η ‖z‖ with hηr | hrη
    · -- `η ≤ |z| < β`
      have h1 : ‖z‖ ^ 2 + δ ^ 2 ≤ (2 * δ / η) ^ 2 * ‖z‖ ^ 2 := by
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have e1 : η ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hη.le hηδ 2
        have e2 : η ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hη.le hηr 2
        nlinarith [mul_le_mul_of_nonneg_left e1 (sq_nonneg ‖z‖),
          mul_le_mul_of_nonneg_left e2 (sq_nonneg δ), mul_nonneg (sq_nonneg δ) (sq_nonneg ‖z‖)]
      have h2 : Real.log (‖z‖ ^ 2 + δ ^ 2) ≤ 2 * Real.log (2 * δ / η) + 2 * Real.log ‖z‖ := by
        calc Real.log (‖z‖ ^ 2 + δ ^ 2) ≤ Real.log ((2 * δ / η) ^ 2 * ‖z‖ ^ 2) :=
              Real.log_le_log hq h1
          _ = Real.log ((2 * δ / η) ^ 2) + Real.log (‖z‖ ^ 2) :=
              Real.log_mul (by positivity) (by positivity)
          _ = 2 * Real.log (2 * δ / η) + 2 * Real.log ‖z‖ := by
              rw [Real.log_pow, Real.log_pow]; norm_num
      have h3 : 1 / 2 ≤ psiB β z := by
        rw [psiB, le_div_iff₀ (by positivity)]
        nlinarith [pow_lt_pow_left₀ hrβ hr.le two_ne_zero]
      have h4 : Real.log (2 * δ / η) ≤ 2 * Real.log (2 * δ / η) * psiB β z := by nlinarith
      rw [hD]
      linarith
    · -- `|z| < η`
      have h1 : Real.log (‖z‖ ^ 2 + δ ^ 2) ≤ 2 := by
        have := Real.log_le_sub_one_of_pos hq
        have h5 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ hr.le (by linarith)
        have h6 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1
        linarith
      have h2 : Real.log (1 / ‖z‖) = - Real.log ‖z‖ := by rw [one_div, Real.log_inv]
      rw [if_pos hrη, hD]
      linarith

theorem psiB_nonneg (β : ℝ) (z : ℂ) : 0 ≤ psiB β z := by
  unfold psiB
  exact div_nonneg (sq_nonneg β) (by positivity)

theorem psiB_le_indicator {β β₂ : ℝ} (hβ : 0 < β) (hβ₂ : 0 < β₂) (z : ℂ) :
    psiB β z ≤ (if ‖z‖ < β₂ then 1 else 0) + β ^ 2 / β₂ ^ 2 := by
  have hq : 0 < ‖z‖ ^ 2 + β ^ 2 := by positivity
  split_ifs with h
  · have h1 : psiB β z ≤ 1 := by
      rw [psiB, div_le_one hq]; nlinarith [sq_nonneg ‖z‖]
    have h2 : 0 ≤ β ^ 2 / β₂ ^ 2 := by positivity
    linarith
  · have h' : β₂ ≤ ‖z‖ := not_lt.mp h
    rw [zero_add, psiB]
    apply div_le_div_of_nonneg_left (sq_nonneg β) (by positivity)
    nlinarith [pow_le_pow_left₀ hβ₂.le h' 2, sq_nonneg β]

end E522

end

/- ## Section: `Sensitivity` -/

section

/-
# Sensitivity bound for smoothed circle averages ("square-root decomposition")

Let `a_k(θ) = ρ_k e^{ikθ}` and `G(x) = cav(θ ↦ φ(∑_k sgn(x_k) a_k(θ) + m(θ)))`.
We bound `∑_k b_k(x)²` for the martingale coefficients `b_k = mgDiff G k`.

Proof sketch (all steps pointwise in `x`):
* `b_k = ½ avg_{y}[G(x_{<k}, +, y_{>k}) − G(x_{<k}, −, y_{>k})]`.
  With `S_k(θ) = ∑_{j<k} sgn(x_j) a_j + ∑_{j>k} sgn(y_j) a_j + m`,
  `φ(S+a) − φ(S−a) = 2 Re(conj(a) g(S)) + e`, `|e| ≤ L₂|a|²` (from `hT` twice), so
  `|b_k − Re(ρ_k ψ̂_k(k))| ≤ L₂ ρ_k²/2` where `ψ_k(θ) = avg_y g(S_k(θ))` and
  `ψ̂(k) = cavC(θ ↦ e^{-ikθ} ψ(θ))`.
* Blocks of length `L`: `k₀ = L * (k / L)`. `|ψ̂_k(k)| ≤ |ψ̂_{k₀}(k)| + (cav|ψ_k − ψ_{k₀}|²)^{1/2}`
  and `|ψ_k − ψ_{k₀}| ≤ avg_y L₂ |S_k − S_{k₀}|`, where `S_k − S_{k₀} = ∑_{j=k₀}^{k} c_j a_j`
  with `|c_j| ≤ 2` (same `y`!). Parseval: `cav|∑ c_j ρ_j e^{ijθ}|² = ∑ |c_j|² ρ_j² ≤ 4 L ρmax²`.
* Bessel inside each block (distinct frequencies): `∑_{k ∈ block} |ψ̂_{k₀}(k)|² ≤ cav|ψ_{k₀}|² ≤ L₁²`.
  Number of blocks `≤ N/L + 1`.
* `(a+b+c)² ≤ 3(a²+b²+c²)` gives the stated bound.

## Structure of the formal proof

All helper declarations carry the prefix `sens_aux_`.
* Fourier analysis on `[0, 2π]`: `sens_aux_orth` (orthogonality of `ex j`), `sens_aux_gram`,
  `sens_aux_parseval`, `sens_aux_bessel` (for any finite set of frequencies `s ⊆ Fin N`).
* Elementary facts about `cav`, `cavC` (linearity for continuous integrands, monotonicity,
  `(cav f)² ≤ cav f²`, `Re ∘ cavC = cav ∘ Re`) and about cube averages
  (`sens_aux_avg_sq_le`, ...).
* `sens_aux_coef`, `sens_aux_S`: the function `S_k^y`; `sens_aux_mgDiff_eq` rewrites `b_k`
  as a cube average of `cav φ(S + a_k) − cav φ(S − a_k)`.
* `sens_aux_step2`: `|b_k − M_k| ≤ L₂ ρ_k² / 2`, with
  `M_k = avg_y cav Re(conj(a_k) g(S_k^y))`.
* `sens_aux_step4`: `(M_k − M'_k)² ≤ ρ_k² L₂² · 4 (k + 1 − k₀) ρmax²`, where `M'_k` uses
  `S_{k₀}^y` (Lipschitz bound, two Cauchy–Schwarz steps and Parseval).
* `sens_aux_main_term`: `|M'_k| ≤ ρ_k ‖Ψ̂_{k₀}(k)‖ / 2^N` with `Ψ_{k₀} = ∑_y g(S_{k₀}^y)`.
* `sens_aux_block_sum`: Bessel inside each block, summed over the `N / L + 1` blocks.
* `sens_aux_bk_sq` combines the three bounds for one `k`; `sum_mgDiff_sq_le` sums over `k`.
-/

open Real Complex
open scoped ComplexConjugate

namespace E522

/- ### Exponentials: orthogonality, Parseval, Bessel -/

@[fun_prop]
lemma sens_aux_ex_cont (k : ℕ) : Continuous (fun θ => ex k θ) := by
  unfold ex; fun_prop

lemma sens_aux_norm_ex (k : ℕ) (θ : ℝ) : ‖ex k θ‖ = 1 := by
  unfold ex; exact Complex.norm_exp_ofReal_mul_I _

lemma sens_aux_ex_mul_conj (j k : ℕ) (θ : ℝ) :
    ex j θ * conj (ex k θ) = Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * I * (θ : ℂ)) := by
  unfold ex
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma sens_aux_orth (j k : ℕ) :
    ∫ θ in (0 : ℝ)..(2 * π), ex j θ * conj (ex k θ) =
      if j = k then ((2 * π : ℝ) : ℂ) else 0 := by
  simp_rw [sens_aux_ex_mul_conj]
  split_ifs with h
  · subst h; simp
  · have hc : (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * I ≠ 0 := by
      apply mul_ne_zero _ I_ne_zero
      have : (j : ℤ) - (k : ℤ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
      exact_mod_cast this
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [show (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * I * ((2 * π : ℝ) : ℂ) =
          (((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [h2]; simp

lemma sens_aux_sq_norm_ofReal (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma sens_aux_gram {N : ℕ} (s : Finset (Fin N)) (c : Fin N → ℂ) :
    ∫ θ in (0 : ℝ)..(2 * π), (∑ j ∈ s, c j * ex j θ) * conj (∑ l ∈ s, c l * ex l θ) =
      ((2 * π : ℝ) : ℂ) * ∑ j ∈ s, c j * conj (c j) := by
  have hexp : ∀ θ, (∑ j ∈ s, c j * ex j θ) * conj (∑ l ∈ s, c l * ex l θ) =
      ∑ j ∈ s, ∑ l ∈ s, (c j * conj (c l)) * (ex j θ * conj (ex l θ)) := by
    intro θ
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    rw [map_mul]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum (fun j _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  have : ∀ j ∈ s, ∫ θ in (0:ℝ)..(2*π), ∑ l ∈ s, (c j * conj (c l)) * (ex j θ * conj (ex l θ)) =
      ((2 * π : ℝ) : ℂ) * (c j * conj (c j)) := by
    intro j hj
    rw [intervalIntegral.integral_finsetSum (fun l _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    simp_rw [intervalIntegral.integral_const_mul, sens_aux_orth, Fin.val_inj, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq, if_pos hj]; ring
  rw [Finset.sum_congr rfl this, Finset.mul_sum]

lemma sens_aux_parseval {N : ℕ} (c : Fin N → ℂ) :
    cav (fun θ => ‖∑ j, c j * ex j θ‖ ^ 2) = ∑ j, ‖c j‖ ^ 2 := by
  unfold cav
  have h2 : ∫ θ in (0:ℝ)..(2*π), ‖∑ j, c j * ex j θ‖ ^ 2 = 2 * π * ∑ j, ‖c j‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [sens_aux_sq_norm_ofReal]
    rw [sens_aux_gram, show ((2 * π * ∑ j, ‖c j‖ ^ 2 : ℝ) : ℂ) =
        ((2 * π : ℝ) : ℂ) * ∑ j, ((‖c j‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
    simp_rw [sens_aux_sq_norm_ofReal]
  rw [h2]; field_simp

lemma sens_aux_bessel {N : ℕ} (ψ : ℝ → ℂ) (hψ : Continuous ψ) (s : Finset (Fin N)) :
    ∑ k ∈ s, ‖cavC (fun θ => conj (ex k θ) * ψ θ)‖ ^ 2 ≤ cav (fun θ => ‖ψ θ‖ ^ 2) := by
  set c : Fin N → ℂ := fun k => cavC (fun θ => conj (ex k θ) * ψ θ) with hc_def
  set P : ℝ → ℂ := fun θ => ∑ k ∈ s, c k * ex k θ with hP_def
  have hPc : Continuous P := by rw [hP_def]; fun_prop
  have h2pi : (2 * π : ℝ) ≠ 0 := by positivity
  have hck : ∀ k : Fin N, ∫ θ in (0:ℝ)..(2*π), conj (ex k θ) * ψ θ = ((2*π : ℝ) : ℂ) * c k := by
    intro k
    simp only [hc_def, cavC]
    rw [← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ h2pi]; simp
  have h1 : ∫ θ in (0:ℝ)..(2*π), ψ θ * conj (P θ) =
      ((2*π:ℝ):ℂ) * ∑ k ∈ s, c k * conj (c k) := by
    simp only [hP_def, map_sum, map_mul, Finset.mul_sum]
    rw [intervalIntegral.integral_finsetSum (fun k _ => by
      apply Continuous.intervalIntegrable; fun_prop)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e : ∀ θ, ψ θ * (conj (c k) * conj (ex k θ)) = conj (c k) * (conj (ex k θ) * ψ θ) :=
      fun θ => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, hck]; ring
  have h2 : ∫ θ in (0:ℝ)..(2*π), P θ * conj (ψ θ) =
      ((2*π:ℝ):ℂ) * ∑ k ∈ s, c k * conj (c k) := by
    have : ∀ θ, P θ * conj (ψ θ) = conj (ψ θ * conj (P θ)) := fun θ => by
      simp [mul_comm]
    simp_rw [this]
    rw [intervalIntegral.intervalIntegral_conj, h1]
    simp only [map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have h3 : ∫ θ in (0:ℝ)..(2*π), P θ * conj (P θ) =
      ((2*π:ℝ):ℂ) * ∑ k ∈ s, c k * conj (c k) := sens_aux_gram s c
  have key : ∫ θ in (0:ℝ)..(2*π), ‖ψ θ - P θ‖ ^ 2 =
      (∫ θ in (0:ℝ)..(2*π), ‖ψ θ‖ ^ 2) - 2 * π * ∑ k ∈ s, ‖c k‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_sum,
      ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_ofReal]
    simp_rw [sens_aux_sq_norm_ofReal]
    have e : ∀ θ, (ψ θ - P θ) * conj (ψ θ - P θ) =
        ψ θ * conj (ψ θ) - ψ θ * conj (P θ) - P θ * conj (ψ θ) + P θ * conj (P θ) :=
      fun θ => by rw [map_sub]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_sub, h1, h2, h3]
    · ring
    all_goals (apply Continuous.intervalIntegrable; fun_prop)
  have nonneg : 0 ≤ ∫ θ in (0:ℝ)..(2*π), ‖ψ θ - P θ‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by positivity) (fun θ _ => by positivity)
  rw [key] at nonneg
  unfold cav
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

/- ### Basic facts about `cav` / `cavC` -/

lemma sens_aux_cav_const (c : ℝ) : cav (fun _ => c) = c := by
  unfold cav
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma sens_aux_cav_nonneg {f : ℝ → ℝ} (hf : ∀ θ, 0 ≤ f θ) : 0 ≤ cav f := by
  unfold cav
  exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by positivity)
    (fun θ _ => hf θ))

lemma sens_aux_cav_add {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) :
    cav (fun θ => f θ + h θ) = cav f + cav h := by
  unfold cav
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  ring

lemma sens_aux_cav_sub {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h) :
    cav (fun θ => f θ - h θ) = cav f - cav h := by
  unfold cav
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _)]
  ring

lemma sens_aux_cav_const_mul (c : ℝ) (f : ℝ → ℝ) : cav (fun θ => c * f θ) = c * cav f := by
  unfold cav
  rw [intervalIntegral.integral_const_mul]
  ring

lemma sens_aux_cav_mono {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hfh : ∀ θ, f θ ≤ h θ) : cav f ≤ cav h := by
  unfold cav
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono_on (by positivity) (hf.intervalIntegrable _ _)
    (hh.intervalIntegrable _ _) (fun θ _ => hfh θ)

lemma sens_aux_abs_cav_le {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hfh : ∀ θ, |f θ| ≤ h θ) : |cav f| ≤ cav h := by
  have h1 : cav f ≤ cav h := sens_aux_cav_mono hf hh (fun θ => (abs_le.mp (hfh θ)).2)
  have h2 : cav (fun θ => (-1) * h θ) ≤ cav f :=
    sens_aux_cav_mono (by fun_prop) hf (fun θ => by linarith [(abs_le.mp (hfh θ)).1])
  rw [sens_aux_cav_const_mul] at h2
  rw [abs_le]
  constructor <;> linarith

lemma sens_aux_cav_re {f : ℝ → ℂ} (hf : Continuous f) :
    cav (fun θ => (f θ).re) = (cavC f).re := by
  unfold cav cavC
  rw [Complex.re_ofReal_mul]
  congr 1
  exact intervalIntegral.intervalIntegral_re (hf.intervalIntegrable _ _)

lemma sens_aux_cavC_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i, Continuous (f i)) :
    cavC (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, cavC (f i) := by
  unfold cavC
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hf i).intervalIntegrable _ _),
    Finset.mul_sum]

lemma sens_aux_cavC_const_mul (c : ℂ) (f : ℝ → ℂ) : cavC (fun θ => c * f θ) = c * cavC f := by
  unfold cavC
  rw [intervalIntegral.integral_const_mul]
  ring

lemma sens_aux_cav_sq_le {f : ℝ → ℝ} (hf : Continuous f) :
    cav f ^ 2 ≤ cav (fun θ => f θ ^ 2) := by
  set c := cav f with hc
  have h0 : 0 ≤ cav (fun θ => (f θ - c) ^ 2) := sens_aux_cav_nonneg (fun θ => sq_nonneg _)
  have e : (fun θ => (f θ - c) ^ 2) = fun θ => (f θ ^ 2 + (-2 * c) * f θ) + c ^ 2 := by
    ext θ; ring
  rw [e, sens_aux_cav_add (by fun_prop) (by fun_prop), sens_aux_cav_add (by fun_prop)
    (by fun_prop), sens_aux_cav_const_mul, sens_aux_cav_const] at h0
  nlinarith

/- ### The decomposition of `b_k` -/

noncomputable section

/-- Coefficient vector: `x` below `k`, `0` at `k`, `y` above `k`. -/
def sens_aux_coef {N : ℕ} (x y : Fin N → Bool) (k : ℕ) (j : Fin N) : ℝ :=
  if (j : ℕ) < k then sgn (x j) else if (j : ℕ) = k then 0 else sgn (y j)

/-- `S_k^y(θ) = ∑_{j<k} sgn(x_j) a_j + ∑_{j>k} sgn(y_j) a_j + m`. -/
def sens_aux_S {N : ℕ} (ρ : ℕ → ℝ) (m : ℝ → ℂ) (x y : Fin N → Bool) (k : ℕ) (θ : ℝ) : ℂ :=
  ∑ j : Fin N, ((sens_aux_coef x y k j * ρ j : ℝ) : ℂ) * ex j θ + m θ

@[fun_prop]
lemma sens_aux_S_cont {N : ℕ} (ρ : ℕ → ℝ) {m : ℝ → ℂ} (hm : Continuous m)
    (x y : Fin N → Bool) (k : ℕ) : Continuous (fun θ => sens_aux_S ρ m x y k θ) := by
  unfold sens_aux_S; fun_prop

lemma sens_aux_W_split {N : ℕ} (ρ : ℕ → ℝ) (m : ℝ → ℂ) (x y : Fin N → Bool) (k : Fin N)
    (b : Bool) (θ : ℝ) :
    Wfun ρ (fun j => if (j : ℕ) < (k : ℕ) + 1 then Function.update x k b j else y j) θ + m θ =
      sens_aux_S ρ m x y k θ + ((sgn b * ρ k : ℝ) : ℂ) * ex k θ := by
  unfold Wfun sens_aux_S
  have hj : ∀ j : Fin N,
      ((sgn ((fun j : Fin N => if (j : ℕ) < (k : ℕ) + 1 then Function.update x k b j else y j) j)
        * ρ j : ℝ) : ℂ) * ex j θ =
      ((sens_aux_coef x y k j * ρ j : ℝ) : ℂ) * ex j θ +
        if j = k then ((sgn b * ρ k : ℝ) : ℂ) * ex k θ else 0 := by
    intro j
    by_cases hjk : j = k
    · subst hjk; simp [sens_aux_coef]
    · have hjk' : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
      rcases lt_or_gt_of_ne hjk' with h | h
      · have h1 : (j : ℕ) < (k : ℕ) + 1 := by omega
        simp [sens_aux_coef, h, h1, hjk]
      · have h1 : ¬ (j : ℕ) < (k : ℕ) + 1 := by omega
        have h2 : ¬ (j : ℕ) < (k : ℕ) := by omega
        simp [sens_aux_coef, h1, h2, hjk, hjk']
  rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

lemma sens_aux_mgDiff_eq {N : ℕ} (ρ : ℕ → ℝ) (m : ℝ → ℂ) (φ : ℂ → ℝ) (x : Fin N → Bool)
    (k : Fin N) :
    mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x =
      (∑ y : Fin N → Bool,
        (cav (fun θ => φ (sens_aux_S ρ m x y k θ + ((ρ k : ℝ) : ℂ) * ex k θ)) -
          cav (fun θ => φ (sens_aux_S ρ m x y k θ - ((ρ k : ℝ) : ℂ) * ex k θ)))) / 2 ^ N / 2 := by
  unfold mgDiff condPrefix cubeAvg
  simp_rw [sens_aux_W_split]
  rw [Finset.sum_sub_distrib]
  simp only [sgn, if_true, one_mul, Bool.false_eq_true, if_false, ofReal_neg,
    neg_mul, ← sub_eq_add_neg]
  ring

/- ### Averages over the cube -/

lemma sens_aux_card_cube (N : ℕ) : (Finset.univ : Finset (Fin N → Bool)).card = 2 ^ N := by
  simp [Finset.card_univ]

lemma sens_aux_sum_const_cube (N : ℕ) (C : ℝ) :
    ∑ _y : Fin N → Bool, C = 2 ^ N * C := by
  rw [Finset.sum_const, sens_aux_card_cube, nsmul_eq_mul]
  push_cast; ring

lemma sens_aux_avg_le {N : ℕ} (u : (Fin N → Bool) → ℝ) (C : ℝ) (h : ∀ y, u y ≤ C) :
    (∑ y, u y) / 2 ^ N ≤ C := by
  rw [div_le_iff₀ (by positivity)]
  calc ∑ y, u y ≤ ∑ _y : Fin N → Bool, C := Finset.sum_le_sum (fun y _ => h y)
    _ = C * 2 ^ N := by rw [sens_aux_sum_const_cube]; ring

lemma sens_aux_avg_abs_le {N : ℕ} (u : (Fin N → Bool) → ℝ) (C : ℝ) (h : ∀ y, |u y| ≤ C) :
    |(∑ y, u y) / 2 ^ N| ≤ C := by
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ N), div_le_iff₀ (by positivity)]
  calc |∑ y, u y| ≤ ∑ y, |u y| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : Fin N → Bool, C := Finset.sum_le_sum (fun y _ => h y)
    _ = C * 2 ^ N := by rw [sens_aux_sum_const_cube]; ring

lemma sens_aux_avg_sq_le {N : ℕ} (u : (Fin N → Bool) → ℝ) :
    ((∑ y, u y) / 2 ^ N) ^ 2 ≤ (∑ y, u y ^ 2) / 2 ^ N := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin N → Bool))) (f := u)
  rw [sens_aux_card_cube] at h
  push_cast at h
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∑ y, u y) ^ 2 * 2 ^ N ≤ (2 ^ N * ∑ y, u y ^ 2) * 2 ^ N := by gcongr
    _ = (∑ y, u y ^ 2) * (2 ^ N) ^ 2 := by ring

/- ### Step 2: Taylor expansion in the `k`-th coordinate -/

lemma sens_aux_pair_bound (φ : ℂ → ℝ) (g : ℂ → ℂ) (L₂ : ℝ)
    (hT : ∀ z w : ℂ, |φ (z + w) - φ z - (starRingEnd ℂ w * g z).re| ≤ L₂ / 2 * ‖w‖ ^ 2)
    (S a : ℂ) :
    |φ (S + a) - φ (S - a) - 2 * (conj a * g S).re| ≤ L₂ * ‖a‖ ^ 2 := by
  have h1 := hT S a
  have h2 := hT S (-a)
  rw [← sub_eq_add_neg, map_neg, neg_mul, Complex.neg_re, norm_neg] at h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma sens_aux_norm_a (r : ℝ) (hr : 0 ≤ r) (k : ℕ) (θ : ℝ) :
    ‖((r : ℝ) : ℂ) * ex k θ‖ = r := by
  rw [norm_mul, sens_aux_norm_ex, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

lemma sens_aux_step2_y (φ : ℂ → ℝ) (g : ℂ → ℂ) (L₂ : ℝ) (hφ : Continuous φ)
    (hgc : Continuous g)
    (hT : ∀ z w : ℂ, |φ (z + w) - φ z - (starRingEnd ℂ w * g z).re| ≤ L₂ / 2 * ‖w‖ ^ 2)
    {S a : ℝ → ℂ} (hS : Continuous S) (ha : Continuous a) (r : ℝ) (hna : ∀ θ, ‖a θ‖ = r) :
    |cav (fun θ => φ (S θ + a θ)) - cav (fun θ => φ (S θ - a θ)) -
      2 * cav (fun θ => (conj (a θ) * g (S θ)).re)| ≤ L₂ * r ^ 2 := by
  rw [← sens_aux_cav_const_mul, ← sens_aux_cav_sub (by fun_prop) (by fun_prop),
    ← sens_aux_cav_sub (by fun_prop) (by fun_prop)]
  calc _ ≤ cav (fun _ => L₂ * r ^ 2) :=
        sens_aux_abs_cav_le (by fun_prop) (by fun_prop) (fun θ => by
          have := sens_aux_pair_bound φ g L₂ hT (S θ) (a θ)
          rwa [hna θ] at this)
    _ = L₂ * r ^ 2 := sens_aux_cav_const _

lemma sens_aux_step2 {N : ℕ} (ρ : ℕ → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k) (m : ℝ → ℂ) (hm : Continuous m)
    (φ : ℂ → ℝ) (g : ℂ → ℂ) (L₂ : ℝ) (hφ : Continuous φ) (hgc : Continuous g)
    (hT : ∀ z w : ℂ, |φ (z + w) - φ z - (starRingEnd ℂ w * g z).re| ≤ L₂ / 2 * ‖w‖ ^ 2)
    (x : Fin N → Bool) (k : Fin N) :
    |mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x -
      (∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re)) / 2 ^ N|
      ≤ L₂ * ρ k ^ 2 / 2 := by
  rw [sens_aux_mgDiff_eq]
  set P : (Fin N → Bool) → ℝ := fun y =>
    cav (fun θ => φ (sens_aux_S ρ m x y k θ + ((ρ k : ℝ) : ℂ) * ex k θ)) with hP
  set Q : (Fin N → Bool) → ℝ := fun y =>
    cav (fun θ => φ (sens_aux_S ρ m x y k θ - ((ρ k : ℝ) : ℂ) * ex k θ)) with hQ
  set R : (Fin N → Bool) → ℝ := fun y => cav (fun θ =>
    (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re) with hR
  have e : (∑ y, (P y - Q y)) / 2 ^ N / 2 - (∑ y, R y) / 2 ^ N =
      ((∑ y, (P y - Q y - 2 * R y)) / 2 ^ N) / 2 := by
    rw [Finset.sum_sub_distrib (f := fun y => P y - Q y), ← Finset.mul_sum]
    ring
  rw [e, abs_div, abs_two, div_le_div_iff_of_pos_right (by norm_num)]
  apply sens_aux_avg_abs_le
  intro y
  exact sens_aux_step2_y φ g L₂ hφ hgc hT (sens_aux_S_cont ρ hm x y k) (by fun_prop) (ρ k)
    (fun θ => sens_aux_norm_a (ρ k) (hρ0 k) k θ)

/- ### Step 4: comparison with the start of the block -/

lemma sens_aux_S_sub {N : ℕ} (ρ : ℕ → ℝ) (m : ℝ → ℂ) (x y : Fin N → Bool) (k k₀ : ℕ)
    (θ : ℝ) :
    sens_aux_S ρ m x y k θ - sens_aux_S ρ m x y k₀ θ =
      ∑ j : Fin N, ((((sens_aux_coef x y k j - sens_aux_coef x y k₀ j) * ρ j : ℝ) : ℂ)) *
        ex j θ := by
  unfold sens_aux_S
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  push_cast; ring

lemma sens_aux_abs_coef_le {N : ℕ} (x y : Fin N → Bool) (k : ℕ) (j : Fin N) :
    |sens_aux_coef x y k j| ≤ 1 := by
  unfold sens_aux_coef
  split_ifs <;> simp [abs_sgn]

lemma sens_aux_coef_diff_sq {N : ℕ} (x y : Fin N → Bool) {k₀ k : ℕ} (hk : k₀ ≤ k)
    (j : Fin N) :
    (sens_aux_coef x y k j - sens_aux_coef x y k₀ j) ^ 2 ≤
      if k₀ ≤ (j : ℕ) ∧ (j : ℕ) ≤ k then 4 else 0 := by
  split_ifs with h
  · have h1 := abs_le.mp (sens_aux_abs_coef_le x y k j)
    have h2 := abs_le.mp (sens_aux_abs_coef_le x y k₀ j)
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  · have : sens_aux_coef x y k j = sens_aux_coef x y k₀ j := by
      unfold sens_aux_coef
      rcases not_and_or.mp h with h' | h'
      · have a1 : (j : ℕ) < k₀ := by omega
        have a2 : (j : ℕ) < k := by omega
        simp [a1, a2]
      · have a1 : ¬ (j : ℕ) < k₀ := by omega
        have a2 : ¬ (j : ℕ) < k := by omega
        have a3 : (j : ℕ) ≠ k₀ := by omega
        have a4 : (j : ℕ) ≠ k := by omega
        simp [a1, a2, a3, a4]
    rw [this]; simp

lemma sens_aux_card_window (N k₀ k : ℕ) :
    ((Finset.univ : Finset (Fin N)).filter (fun j : Fin N => k₀ ≤ (j : ℕ) ∧ (j : ℕ) ≤ k)).card ≤
      k + 1 - k₀ := by
  calc _ ≤ (Finset.Icc k₀ k).card := by
        apply Finset.card_le_card_of_injOn (fun j : Fin N => (j : ℕ))
        · intro j hj
          simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hj
          simp only [Finset.coe_Icc, Set.mem_Icc]
          exact hj
        · intro a _ b _ h; exact Fin.ext h
    _ = k + 1 - k₀ := Nat.card_Icc _ _

lemma sens_aux_cav_D_sq {N : ℕ} (ρ : ℕ → ℝ) (ρmax : ℝ) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hρ : ∀ k < N, ρ k ≤ ρmax) (m : ℝ → ℂ) (x y : Fin N → Bool) {k₀ k : ℕ} (hk : k₀ ≤ k) :
    cav (fun θ => ‖sens_aux_S ρ m x y k θ - sens_aux_S ρ m x y k₀ θ‖ ^ 2) ≤
      4 * ((k + 1 - k₀ : ℕ) : ℝ) * ρmax ^ 2 := by
  simp_rw [sens_aux_S_sub]
  rw [sens_aux_parseval]
  have hcard := sens_aux_card_window N k₀ k
  calc ∑ j : Fin N, ‖((((sens_aux_coef x y k j - sens_aux_coef x y k₀ j) * ρ j : ℝ) : ℂ))‖ ^ 2
      = ∑ j : Fin N, (sens_aux_coef x y k j - sens_aux_coef x y k₀ j) ^ 2 * ρ j ^ 2 := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]; ring
    _ ≤ ∑ j : Fin N, (if k₀ ≤ (j : ℕ) ∧ (j : ℕ) ≤ k then (4 : ℝ) else 0) * ρmax ^ 2 := by
        refine Finset.sum_le_sum (fun j _ => ?_)
        apply mul_le_mul (sens_aux_coef_diff_sq x y hk j) _ (sq_nonneg _)
          (by split_ifs <;> norm_num)
        exact pow_le_pow_left₀ (hρ0 j) (hρ j j.isLt) 2
    _ = 4 * (((Finset.univ : Finset (Fin N)).filter
          (fun j : Fin N => k₀ ≤ (j : ℕ) ∧ (j : ℕ) ≤ k)).card : ℝ) * ρmax ^ 2 := by
        rw [← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
          nsmul_eq_mul]
        ring
    _ ≤ 4 * ((k + 1 - k₀ : ℕ) : ℝ) * ρmax ^ 2 := by
        gcongr

lemma sens_aux_step4 {N : ℕ} (ρ : ℕ → ℝ) (ρmax : ℝ) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hρ : ∀ k < N, ρ k ≤ ρmax) (m : ℝ → ℂ) (hm : Continuous m) (g : ℂ → ℂ) (L₂ : ℝ)
    (hgc : Continuous g) (hgL : ∀ z w, ‖g z - g w‖ ≤ L₂ * ‖z - w‖)
    (x : Fin N → Bool) (k : Fin N) {k₀ : ℕ} (hk : k₀ ≤ k) :
    ((∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re)) / 2 ^ N -
     (∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)).re)) / 2 ^ N) ^ 2
      ≤ ρ k ^ 2 * L₂ ^ 2 * (4 * ((k + 1 - k₀ : ℕ) : ℝ) * ρmax ^ 2) := by
  set V : (Fin N → Bool) → ℝ := fun y => ρ k * L₂ *
    cav (fun θ => ‖sens_aux_S ρ m x y k θ - sens_aux_S ρ m x y k₀ θ‖) with hV
  have hdiff : ∀ y : Fin N → Bool,
      |cav (fun θ => (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re) -
        cav (fun θ => (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)).re)|
        ≤ V y := by
    intro y
    have hc1 : Continuous (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re) := by fun_prop
    have hc2 : Continuous (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)).re) := by fun_prop
    rw [← sens_aux_cav_sub hc1 hc2]
    simp only [hV]
    rw [← sens_aux_cav_const_mul]
    apply sens_aux_abs_cav_le (by fun_prop) (by fun_prop)
    intro θ
    rw [← Complex.sub_re, ← mul_sub]
    calc |(conj (((ρ k : ℝ) : ℂ) * ex k θ) *
          (g (sens_aux_S ρ m x y k θ) - g (sens_aux_S ρ m x y k₀ θ))).re|
        ≤ ‖conj (((ρ k : ℝ) : ℂ) * ex k θ) *
          (g (sens_aux_S ρ m x y k θ) - g (sens_aux_S ρ m x y k₀ θ))‖ :=
          Complex.abs_re_le_norm _
      _ = ρ k * ‖g (sens_aux_S ρ m x y k θ) - g (sens_aux_S ρ m x y k₀ θ)‖ := by
          rw [norm_mul, Complex.norm_conj, sens_aux_norm_a (ρ k) (hρ0 k)]
      _ ≤ ρ k * (L₂ * ‖sens_aux_S ρ m x y k θ - sens_aux_S ρ m x y k₀ θ‖) :=
          mul_le_mul_of_nonneg_left (hgL _ _) (hρ0 k)
      _ = ρ k * L₂ * ‖sens_aux_S ρ m x y k θ - sens_aux_S ρ m x y k₀ θ‖ := by ring
  have h1 : |(∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re)) / 2 ^ N -
     (∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)).re)) / 2 ^ N|
      ≤ (∑ y, V y) / 2 ^ N := by
    rw [← sub_div, ← Finset.sum_sub_distrib, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < 2 ^ N)]
    gcongr
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun y _ => hdiff y))
  have h3 : ∀ y, V y ^ 2 ≤ ρ k ^ 2 * L₂ ^ 2 * (4 * ((k + 1 - k₀ : ℕ) : ℝ) * ρmax ^ 2) := by
    intro y
    simp only [hV]
    rw [mul_pow, mul_pow]
    gcongr
    calc _ ≤ cav (fun θ => ‖sens_aux_S ρ m x y k θ - sens_aux_S ρ m x y k₀ θ‖ ^ 2) :=
          sens_aux_cav_sq_le (by fun_prop)
      _ ≤ _ := sens_aux_cav_D_sq ρ ρmax hρ0 hρ m x y hk
  rw [← sq_abs]
  calc _ ≤ ((∑ y, V y) / 2 ^ N) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ (∑ y, V y ^ 2) / 2 ^ N := sens_aux_avg_sq_le V
    _ ≤ _ := sens_aux_avg_le _ _ h3

/- ### Step 3: the main term is a Fourier coefficient -/

lemma sens_aux_main_term {N : ℕ} (ρ : ℕ → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k) (m : ℝ → ℂ)
    (hm : Continuous m) (g : ℂ → ℂ) (hgc : Continuous g) (x : Fin N → Bool) (k : Fin N)
    (k₀ : ℕ) :
    |(∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)).re)) / 2 ^ N|
      ≤ ρ k * ‖cavC (fun θ => conj (ex k θ) *
          ∑ y : Fin N → Bool, g (sens_aux_S ρ m x y k₀ θ))‖ / 2 ^ N := by
  have e1 : ∀ y : Fin N → Bool, cav (fun θ =>
      (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)).re) =
      (cavC (fun θ => conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ))).re :=
    fun y => sens_aux_cav_re (by fun_prop)
  have e3 : ∑ y : Fin N → Bool,
      cavC (fun θ => conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)) =
      cavC (fun θ => ∑ y : Fin N → Bool,
        conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)) :=
    (sens_aux_cavC_sum Finset.univ (f := fun y θ =>
      conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ))
      (fun y => by fun_prop)).symm
  rw [Finset.sum_congr rfl (fun y _ => e1 y), ← Complex.re_sum, e3]
  have e2 : (fun θ => ∑ y : Fin N → Bool,
      conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k₀ θ)) =
      fun θ => ((ρ k : ℝ) : ℂ) *
        (conj (ex k θ) * ∑ y : Fin N → Bool, g (sens_aux_S ρ m x y k₀ θ)) := by
    ext θ
    rw [← Finset.mul_sum, map_mul, Complex.conj_ofReal]; ring
  rw [e2, sens_aux_cavC_const_mul, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ N)]
  gcongr
  calc _ ≤ ‖((ρ k : ℝ) : ℂ) * cavC (fun θ => conj (ex k θ) *
          ∑ y : Fin N → Bool, g (sens_aux_S ρ m x y k₀ θ))‖ := Complex.abs_re_le_norm _
    _ = _ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 k)]

/- ### Step 5: summing over blocks (Bessel inside each block) -/

lemma sens_aux_block_sum {N L : ℕ} (ρ : ℕ → ℝ) (ρmax : ℝ) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hρ : ∀ k < N, ρ k ≤ ρmax) (Ψ : ℕ → ℝ → ℂ) (hΨc : ∀ k₀, Continuous (Ψ k₀)) (B : ℝ)
    (hΨ : ∀ k₀ θ, ‖Ψ k₀ θ‖ ≤ B) :
    ∑ k : Fin N, (ρ k * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * ((k : ℕ) / L)) θ)‖) ^ 2 ≤
      ρmax ^ 2 * B ^ 2 * (((N / L : ℕ) : ℝ) + 1) := by
  have hmaps : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      (k : ℕ) / L ∈ Finset.range (N / L + 1) := by
    intro k _
    rw [Finset.mem_range]
    have : (k : ℕ) / L ≤ N / L := Nat.div_le_div_right k.isLt.le
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hq : ∀ q ∈ Finset.range (N / L + 1),
      ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) / L = q),
        (ρ k * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * ((k : ℕ) / L)) θ)‖) ^ 2 ≤
        ρmax ^ 2 * B ^ 2 := by
    intro q _
    have hcont : Continuous (fun θ => ‖Ψ (L * q) θ‖ ^ 2) := ((hΨc (L * q)).norm).pow 2
    calc _ = ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) / L = q),
          ρ k ^ 2 * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * q) θ)‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [(Finset.mem_filter.mp hk).2, mul_pow]
      _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) / L = q),
          ρmax ^ 2 * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * q) θ)‖ ^ 2 := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hρ0 k) (hρ k k.isLt) 2)
            (sq_nonneg _)
      _ = ρmax ^ 2 * ∑ k ∈ Finset.univ.filter (fun k : Fin N => (k : ℕ) / L = q),
          ‖cavC (fun θ => conj (ex k θ) * Ψ (L * q) θ)‖ ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ρmax ^ 2 * cav (fun θ => ‖Ψ (L * q) θ‖ ^ 2) := by
          gcongr
          exact sens_aux_bessel (Ψ (L * q)) (hΨc _) _
      _ ≤ ρmax ^ 2 * B ^ 2 := by
          gcongr
          calc _ ≤ cav (fun _ => B ^ 2) :=
                sens_aux_cav_mono hcont continuous_const
                  (fun θ => pow_le_pow_left₀ (norm_nonneg _) (hΨ _ θ) 2)
            _ = B ^ 2 := sens_aux_cav_const _
  calc _ ≤ ∑ _q ∈ Finset.range (N / L + 1), ρmax ^ 2 * B ^ 2 := Finset.sum_le_sum hq
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast; ring

/- ### Assembling the bound for a single coefficient -/

lemma sens_aux_bk_sq {N L : ℕ} (hL : 0 < L) (ρ : ℕ → ℝ) (ρmax : ℝ)
    (hρ0 : ∀ k, 0 ≤ ρ k) (hρ : ∀ k < N, ρ k ≤ ρmax)
    (m : ℝ → ℂ) (hm : Continuous m)
    (φ : ℂ → ℝ) (g : ℂ → ℂ) (L₂ : ℝ) (hφ : Continuous φ) (hgc : Continuous g)
    (hT : ∀ z w : ℂ, |φ (z + w) - φ z - (starRingEnd ℂ w * g z).re| ≤ L₂ / 2 * ‖w‖ ^ 2)
    (hgL : ∀ z w, ‖g z - g w‖ ≤ L₂ * ‖z - w‖) (x : Fin N → Bool) (k : Fin N) :
    mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x ^ 2 ≤
      3 * (ρ k * ‖cavC (fun θ => conj (ex k θ) *
          ∑ y : Fin N → Bool, g (sens_aux_S ρ m x y (L * ((k : ℕ) / L)) θ))‖ / 2 ^ N) ^ 2 +
        (12 * L₂ ^ 2 * ρmax ^ 4 * L + L₂ ^ 2 * ρmax ^ 4) := by
  have hk₀k : L * ((k : ℕ) / L) ≤ (k : ℕ) := Nat.mul_div_le (k : ℕ) L
  have hwin : (k : ℕ) + 1 - L * ((k : ℕ) / L) ≤ L := by
    have h1 := Nat.mod_lt (k : ℕ) hL
    have h2 := Nat.div_add_mod (k : ℕ) L
    omega
  have h2 := sens_aux_step2 ρ hρ0 m hm φ g L₂ hφ hgc hT x k
  have h4 := sens_aux_step4 ρ ρmax hρ0 hρ m hm g L₂ hgc hgL x k hk₀k
  have h5 := sens_aux_main_term ρ hρ0 m hm g hgc x k (L * ((k : ℕ) / L))
  set b := mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x with hb
  set M := (∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) * g (sens_aux_S ρ m x y k θ)).re)) / 2 ^ N with hM
  set M' := (∑ y : Fin N → Bool, cav (fun θ =>
        (conj (((ρ k : ℝ) : ℂ) * ex k θ) *
          g (sens_aux_S ρ m x y (L * ((k : ℕ) / L)) θ)).re)) / 2 ^ N with hM'
  set A := ρ k * ‖cavC (fun θ => conj (ex k θ) *
          ∑ y : Fin N → Bool, g (sens_aux_S ρ m x y (L * ((k : ℕ) / L)) θ))‖ / 2 ^ N with hA
  have hρk : ρ k ≤ ρmax := hρ k k.isLt
  have hρk0 : 0 ≤ ρ k := hρ0 k
  have hwinR : (((k : ℕ) + 1 - L * ((k : ℕ) / L) : ℕ) : ℝ) ≤ L := by exact_mod_cast hwin
  have hB : (M - M') ^ 2 ≤ 4 * L₂ ^ 2 * ρmax ^ 4 * L := by
    calc (M - M') ^ 2 ≤ ρ k ^ 2 * L₂ ^ 2 *
          (4 * (((k : ℕ) + 1 - L * ((k : ℕ) / L) : ℕ) : ℝ) * ρmax ^ 2) := h4
      _ ≤ ρmax ^ 2 * L₂ ^ 2 * (4 * (L : ℝ) * ρmax ^ 2) := by
          have e1 : ρ k ^ 2 ≤ ρmax ^ 2 := pow_le_pow_left₀ hρk0 hρk 2
          have e2 : 4 * (((k : ℕ) + 1 - L * ((k : ℕ) / L) : ℕ) : ℝ) * ρmax ^ 2 ≤
              4 * (L : ℝ) * ρmax ^ 2 := by gcongr
          have e3 : 0 ≤ 4 * (((k : ℕ) + 1 - L * ((k : ℕ) / L) : ℕ) : ℝ) * ρmax ^ 2 := by
            positivity
          calc ρ k ^ 2 * L₂ ^ 2 * (4 * (((k : ℕ) + 1 - L * ((k : ℕ) / L) : ℕ) : ℝ) * ρmax ^ 2)
              ≤ ρmax ^ 2 * L₂ ^ 2 *
                (4 * (((k : ℕ) + 1 - L * ((k : ℕ) / L) : ℕ) : ℝ) * ρmax ^ 2) := by gcongr
            _ ≤ ρmax ^ 2 * L₂ ^ 2 * (4 * (L : ℝ) * ρmax ^ 2) := by gcongr
      _ = 4 * L₂ ^ 2 * ρmax ^ 4 * L := by ring
  have hC : 3 * (L₂ * ρ k ^ 2 / 2) ^ 2 ≤ L₂ ^ 2 * ρmax ^ 4 := by
    have e1 : ρ k ^ 4 ≤ ρmax ^ 4 := pow_le_pow_left₀ hρk0 hρk 4
    have e2 : 0 ≤ L₂ ^ 2 := sq_nonneg _
    calc 3 * (L₂ * ρ k ^ 2 / 2) ^ 2 = 3 / 4 * (L₂ ^ 2 * ρ k ^ 4) := by ring
      _ ≤ 3 / 4 * (L₂ ^ 2 * ρmax ^ 4) := by gcongr
      _ ≤ L₂ ^ 2 * ρmax ^ 4 := by nlinarith [mul_nonneg e2 (pow_nonneg (hρk0.trans hρk) 4)]
  have habs : |b| ≤ A + |M - M'| + L₂ * ρ k ^ 2 / 2 := by
    calc |b| = |M' + (M - M') + (b - M)| := by congr 1; ring
      _ ≤ |M'| + |M - M'| + |b - M| := abs_add_three _ _ _
      _ ≤ A + |M - M'| + L₂ * ρ k ^ 2 / 2 := by linarith
  have hsq : b ^ 2 ≤ (A + |M - M'| + L₂ * ρ k ^ 2 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hB' : |M - M'| ^ 2 ≤ 4 * L₂ ^ 2 * ρmax ^ 4 * L := by rw [sq_abs]; exact hB
  nlinarith [sq_nonneg (A - |M - M'|), sq_nonneg (|M - M'| - L₂ * ρ k ^ 2 / 2),
    sq_nonneg (A - L₂ * ρ k ^ 2 / 2)]

end

/- ### The main theorem -/

theorem sum_mgDiff_sq_le {N L : ℕ} (hL : 0 < L) (ρ : ℕ → ℝ) (ρmax : ℝ)
    (hρ0 : ∀ k, 0 ≤ ρ k) (hρ : ∀ k < N, ρ k ≤ ρmax)
    (m : ℝ → ℂ) (hm : Continuous m)
    (φ : ℂ → ℝ) (g : ℂ → ℂ) (L₁ L₂ : ℝ) (hφ : Continuous φ) (hgc : Continuous g)
    (hT : ∀ z w : ℂ, |φ (z + w) - φ z - (starRingEnd ℂ w * g z).re| ≤ L₂ / 2 * ‖w‖ ^ 2)
    (hg : ∀ z, ‖g z‖ ≤ L₁) (hgL : ∀ z w, ‖g z - g w‖ ≤ L₂ * ‖z - w‖) (x : Fin N → Bool) :
    ∑ k, mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x ^ 2 ≤
      3 * L₁ ^ 2 * ρmax ^ 2 * ((N : ℝ) / L + 1) + 12 * L₂ ^ 2 * ρmax ^ 4 * L * N
        + L₂ ^ 2 * ρmax ^ 4 * N := by
  have hL₁ : 0 ≤ L₁ := (norm_nonneg _).trans (hg 0)
  set Ψ : ℕ → ℝ → ℂ := fun k₀ θ => ∑ y : Fin N → Bool, g (sens_aux_S ρ m x y k₀ θ) with hΨdef
  have hΨc : ∀ k₀, Continuous (Ψ k₀) := fun k₀ => by
    simp only [hΨdef]; fun_prop
  have hΨb : ∀ k₀ θ, ‖Ψ k₀ θ‖ ≤ 2 ^ N * L₁ := by
    intro k₀ θ
    calc ‖Ψ k₀ θ‖ ≤ ∑ y : Fin N → Bool, ‖g (sens_aux_S ρ m x y k₀ θ)‖ := norm_sum_le _ _
      _ ≤ ∑ _y : Fin N → Bool, L₁ := Finset.sum_le_sum (fun y _ => hg _)
      _ = 2 ^ N * L₁ := sens_aux_sum_const_cube N L₁
  have hblock := sens_aux_block_sum (L := L) ρ ρmax hρ0 hρ Ψ hΨc (2 ^ N * L₁) hΨb
  have hk : ∀ k : Fin N,
      mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x ^ 2 ≤
        3 * (ρ k * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * ((k : ℕ) / L)) θ)‖ / 2 ^ N) ^ 2 +
          (12 * L₂ ^ 2 * ρmax ^ 4 * L + L₂ ^ 2 * ρmax ^ 4) :=
    fun k => sens_aux_bk_sq hL ρ ρmax hρ0 hρ m hm φ g L₂ hφ hgc hT hgL x k
  have hNL : ((N / L : ℕ) : ℝ) ≤ (N : ℝ) / L := Nat.cast_div_le
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  calc ∑ k, mgDiff (fun y : Fin N → Bool => cav (fun θ => φ (Wfun ρ y θ + m θ))) k x ^ 2
      ≤ ∑ k : Fin N,
        (3 * (ρ k * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * ((k : ℕ) / L)) θ)‖ / 2 ^ N) ^ 2 +
          (12 * L₂ ^ 2 * ρmax ^ 4 * L + L₂ ^ 2 * ρmax ^ 4)) :=
        Finset.sum_le_sum (fun k _ => hk k)
    _ = 3 / (2 ^ N) ^ 2 * ∑ k : Fin N,
          (ρ k * ‖cavC (fun θ => conj (ex k θ) * Ψ (L * ((k : ℕ) / L)) θ)‖) ^ 2 +
        N * (12 * L₂ ^ 2 * ρmax ^ 4 * L + L₂ ^ 2 * ρmax ^ 4) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [div_pow]; ring
    _ ≤ 3 / (2 ^ N) ^ 2 * (ρmax ^ 2 * (2 ^ N * L₁) ^ 2 * (((N / L : ℕ) : ℝ) + 1)) +
        N * (12 * L₂ ^ 2 * ρmax ^ 4 * L + L₂ ^ 2 * ρmax ^ 4) := by
        gcongr
    _ = 3 * L₁ ^ 2 * ρmax ^ 2 * (((N / L : ℕ) : ℝ) + 1) +
        N * (12 * L₂ ^ 2 * ρmax ^ 4 * L + L₂ ^ 2 * ρmax ^ 4) := by
        field_simp
    _ ≤ 3 * L₁ ^ 2 * ρmax ^ 2 * ((N : ℝ) / L + 1) + 12 * L₂ ^ 2 * ρmax ^ 4 * L * N
        + L₂ ^ 2 * ρmax ^ 4 * N := by
        have : 3 * L₁ ^ 2 * ρmax ^ 2 * (((N / L : ℕ) : ℝ) + 1) ≤
            3 * L₁ ^ 2 * ρmax ^ 2 * ((N : ℝ) / L + 1) := by gcongr
        nlinarith

end E522

end

/- ## Section: `Gauss` -/

section

/-
# The standard complex Gaussian `cgauss` (law of `(g₁ + i g₂)/√2`, `E|z|² = 1`)

`cgauss = (stdGaussian ℂ).map (· / √2)`; here `ℂ` is a 2-dimensional real inner product
space, so `stdGaussian ℂ` has identity covariance (`E|z|² = 2`).

Useful Mathlib API: `ProbabilityTheory.stdGaussian`, `stdGaussian_map` (invariance under
`LinearIsometryEquiv`), `charFun_stdGaussian`, `Measure.ext_of_charFun`,
`isGaussian_stdGaussian`, `integral_id_stdGaussian`, `covarianceBilin_stdGaussian`,
`ProbabilityTheory.IsGaussian` moments (`memLp`), `gaussianReal`.
The stability statement can be proved with characteristic functions
(`charFun` of an independent sum is the product) or with an orthogonal map of
`WithLp 2 (ℂ × ℂ)`.

## Proof strategy (helper lemmas are prefixed `gauss_aux_`)

* Integrals against `cgauss` are transported to `stdGaussian ℂ` through the measurable
  embedding `z ↦ (√2)⁻¹ • z` (`gauss_aux_integral_cgauss`).
* `cgauss` is Gaussian (image of `stdGaussian ℂ` by a continuous linear map), which gives
  all moments via Fernique (`IsGaussian.memLp_id`).
* `charFun cgauss t = exp (-‖t‖²/4)`, and more generally
  `∫ exp(i⟪a x, t⟫) dcgauss(x) = exp (-‖a‖²‖t‖²/4)`; this yields `cgauss_map_neg` and
  `cgauss_stable` via `Measure.ext_of_charFun` and `integral_prod_mul`.
* Second moments of continuous linear functionals come from `variance_dual_stdGaussian`;
  the fourth moment of `gaussianReal 0 1` is `3` (fourth derivative of its mgf at `0`),
  which gives `E (Re z)⁴ = E (Im z)⁴ = 3/4` under `cgauss`, and then
  `‖z‖³ ≤ ‖z‖²/2 + (Re z)⁴ + (Im z)⁴` yields `∫ ‖z‖³ ≤ 2`.
-/

open Real Complex MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace E522

/- ### Basic reductions to `stdGaussian ℂ` -/

lemma gauss_aux_cgauss_def :
    cgauss = (stdGaussian ℂ).map (fun z : ℂ => ((Real.sqrt 2)⁻¹ : ℝ) • z) := rfl

lemma gauss_aux_sqrt_two_inv_ne : ((Real.sqrt 2)⁻¹ : ℝ) ≠ 0 := by positivity

lemma gauss_aux_sqrt_two_inv_sq : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- Integrals against `cgauss` are integrals against `stdGaussian ℂ` of the rescaled function
(no measurability assumption needed: the scaling is a measurable embedding). -/
lemma gauss_aux_integral_cgauss {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) :
    ∫ z, f z ∂cgauss = ∫ w, f (((Real.sqrt 2)⁻¹ : ℝ) • w) ∂(stdGaussian ℂ) :=
  (Homeomorph.smulOfNeZero _ gauss_aux_sqrt_two_inv_ne).measurableEmbedding.integral_map f

/-- `cgauss` is a Gaussian measure (image of `stdGaussian ℂ` by a continuous linear map). -/
instance gauss_aux_isGaussian_cgauss : IsGaussian cgauss := by
  have : (fun z : ℂ => ((Real.sqrt 2)⁻¹ : ℝ) • z) =
      ⇑(((Real.sqrt 2)⁻¹ : ℝ) • ContinuousLinearMap.id ℝ ℂ) := by
    funext z; simp
  rw [gauss_aux_cgauss_def, this]
  infer_instance

instance cgauss_isProbabilityMeasure : IsProbabilityMeasure cgauss := by
  infer_instance

/- ### Characteristic function -/

lemma gauss_aux_charFun_cgauss (t : ℂ) : charFun cgauss t = cexp (-(‖t‖ ^ 2 / 4 : ℝ)) := by
  rw [gauss_aux_cgauss_def, charFun_map_smul, charFun_stdGaussian]
  congr 1
  have h : ‖((Real.sqrt 2)⁻¹ : ℝ) • t‖ ^ 2 = ‖t‖ ^ 2 / 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, gauss_aux_sqrt_two_inv_sq]; ring
  rw [← ofReal_pow, h]; push_cast; ring

lemma gauss_aux_integral_exp_inner_mul (a t : ℂ) :
    ∫ x, cexp (⟪a * x, t⟫ * I) ∂cgauss = cexp (-(‖a‖ ^ 2 * ‖t‖ ^ 2 / 4 : ℝ)) := by
  have h : ∀ x : ℂ, ⟪a * x, t⟫ = ⟪x, (starRingEnd ℂ) a * t⟫ := by
    intro x; simp only [Complex.inner]; simp [Complex.mul_re, Complex.mul_im]; ring
  simp_rw [h]
  rw [← charFun_apply, gauss_aux_charFun_cgauss, norm_mul, Complex.norm_conj, mul_pow]

lemma gauss_aux_charFun_map_mul (a t : ℂ) :
    charFun (cgauss.map (fun z => a * z)) t = cexp (-(‖a‖ ^ 2 * ‖t‖ ^ 2 / 4 : ℝ)) := by
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  exact gauss_aux_integral_exp_inner_mul a t

theorem cgauss_map_neg : cgauss.map (fun z => -z) = cgauss := by
  apply Measure.ext_of_charFun
  funext t
  have h1 : (fun z : ℂ => -z) = fun z => (-1 : ℂ) * z := by funext z; ring
  rw [h1, gauss_aux_charFun_map_mul, gauss_aux_charFun_cgauss]
  congr 2; simp

/-- Stability: `aγ + bγ'` has the law of `√(|a|²+|b|²) γ`. -/
theorem cgauss_stable (a b : ℂ) :
    (cgauss.prod cgauss).map (fun p : ℂ × ℂ => a * p.1 + b * p.2) =
      cgauss.map (fun z => ((Real.sqrt (‖a‖ ^ 2 + ‖b‖ ^ 2) : ℝ) : ℂ) * z) := by
  apply Measure.ext_of_charFun
  funext t
  rw [gauss_aux_charFun_map_mul, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [inner_add_left, ofReal_add, add_mul, Complex.exp_add]
  rw [integral_prod_mul (fun x : ℂ => cexp (⟪a * x, t⟫ * I))
    (fun y : ℂ => cexp (⟪b * y, t⟫ * I))]
  rw [gauss_aux_integral_exp_inner_mul, gauss_aux_integral_exp_inner_mul, ← Complex.exp_add]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  push_cast; ring

/- ### Moments -/

theorem cgauss_integrable_norm_pow (k : ℕ) : Integrable (fun z : ℂ => ‖z‖ ^ k) cgauss := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have h := (IsGaussian.memLp_id cgauss k (by simp)).integrable_norm_pow hk.ne'
    simpa using h

/-- Second moment of a continuous linear functional under `stdGaussian ℂ`. -/
lemma gauss_aux_std_sq (L : StrongDual ℝ ℂ) :
    ∫ w, (L w) ^ 2 ∂(stdGaussian ℂ) = ‖L‖ ^ 2 := by
  rw [← variance_of_integral_eq_zero L.continuous.aemeasurable
    (integral_strongDual_stdGaussian L)]
  exact variance_dual_stdGaussian L

lemma gauss_aux_std_norm_sq : ∫ w, ‖w‖ ^ 2 ∂(stdGaussian ℂ) = 2 := by
  have h : ∀ w : ℂ, ‖w‖ ^ 2 = (reCLM w) ^ 2 + (imCLM w) ^ 2 := by
    intro w; rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  simp_rw [h]
  rw [integral_add, gauss_aux_std_sq, gauss_aux_std_sq, reCLM_norm, imCLM_norm]
  · norm_num
  · exact (IsGaussian.memLp_dual _ reCLM 2 (by simp)).integrable_sq
  · exact (IsGaussian.memLp_dual _ imCLM 2 (by simp)).integrable_sq

theorem cgauss_integral_norm_sq : ∫ z, ‖z‖ ^ 2 ∂cgauss = 1 := by
  rw [gauss_aux_integral_cgauss]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, gauss_aux_std_norm_sq, gauss_aux_sqrt_two_inv_sq]; norm_num

theorem cgauss_integral_norm_le : ∫ z, ‖z‖ ∂cgauss ≤ 1 := by
  have h2 := cgauss_integrable_norm_pow 2
  have h1 : Integrable (fun z : ℂ => ‖z‖) cgauss := by
    simpa using cgauss_integrable_norm_pow 1
  have : ∫ z, ‖z‖ ∂cgauss ≤ ∫ z, (1 + ‖z‖ ^ 2) / 2 ∂cgauss := by
    apply integral_mono h1 (((integrable_const 1).add h2).div_const 2)
    intro z
    show ‖z‖ ≤ (1 + ‖z‖ ^ 2) / 2
    nlinarith [sq_nonneg (‖z‖ - 1)]
  rw [integral_div, integral_add (integrable_const 1) h2, cgauss_integral_norm_sq] at this
  simp at this; linarith

/-- Fourth moment of the standard real Gaussian (fourth derivative of `exp (t²/2)` at `0`). -/
lemma gauss_aux_gaussianReal_pow_four : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  have h := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1) (by simp) 4
  rw [mgf_id_gaussianReal] at h
  have e0 : (fun t : ℝ => rexp ((0:ℝ) * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2)) =
      fun t => rexp (t ^ 2 / 2) := by
    funext t; simp
  rw [e0] at h
  have d0 : deriv (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2) := by
    funext t
    have h' : HasDerivAt (fun t : ℝ => rexp (t ^ 2 / 2)) (t * rexp (t ^ 2 / 2)) t :=
      ((hasDerivAt_pow 2 t).div_const 2).exp.congr_deriv (by norm_num; ring)
    exact h'.deriv
  have d1 : deriv (fun t : ℝ => t * rexp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
    funext t
    have h' : HasDerivAt (fun t : ℝ => t * rexp (t ^ 2 / 2)) ((1 + t ^ 2) * rexp (t ^ 2 / 2)) t :=
      ((hasDerivAt_id' t).mul ((hasDerivAt_pow 2 t).div_const 2).exp).congr_deriv
        (by norm_num; ring)
    exact h'.deriv
  have d2 : deriv (fun t : ℝ => (1 + t ^ 2) * rexp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
    funext t
    have h' : HasDerivAt (fun t : ℝ => (1 + t ^ 2) * rexp (t ^ 2 / 2))
        ((3 * t + t ^ 3) * rexp (t ^ 2 / 2)) t :=
      (((hasDerivAt_pow 2 t).const_add 1).mul ((hasDerivAt_pow 2 t).div_const 2).exp).congr_deriv
        (by norm_num; ring)
    exact h'.deriv
  have d3 : deriv (fun t : ℝ => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)) 0 = 3 := by
    have h' : HasDerivAt (fun t : ℝ => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)) 3 0 :=
      ((((hasDerivAt_id' (0:ℝ)).const_mul 3).add (hasDerivAt_pow 3 (0:ℝ))).mul
        ((hasDerivAt_pow 2 (0:ℝ)).div_const 2).exp).congr_deriv (by norm_num)
    exact h'.deriv
  rw [iteratedDeriv_succ', d0, iteratedDeriv_succ', d1, iteratedDeriv_succ', d2,
    iteratedDeriv_one, d3] at h
  simpa using h.symm

lemma gauss_aux_std_map_eq (L : StrongDual ℝ ℂ) (hL : ‖L‖ = 1) :
    (stdGaussian ℂ).map L = gaussianReal 0 1 := by
  rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian, hL]
  simp

lemma gauss_aux_std_pow_four (L : StrongDual ℝ ℂ) (hL : ‖L‖ = 1) :
    ∫ w, (L w) ^ 4 ∂(stdGaussian ℂ) = 3 := by
  have := gauss_aux_gaussianReal_pow_four
  rw [← gauss_aux_std_map_eq L hL, integral_map (by fun_prop) (by fun_prop)] at this
  exact this

lemma gauss_aux_cgauss_re_pow_four : ∫ z, z.re ^ 4 ∂cgauss = 3 / 4 := by
  rw [gauss_aux_integral_cgauss]
  have h : ∀ w : ℂ, ((((Real.sqrt 2)⁻¹ : ℝ) • w).re) ^ 4 =
      (((Real.sqrt 2)⁻¹ : ℝ) ^ 2) ^ 2 * (reCLM w) ^ 4 := by
    intro w; rw [Complex.smul_re, smul_eq_mul, reCLM_apply]; ring
  simp_rw [h]
  rw [integral_const_mul, gauss_aux_std_pow_four _ reCLM_norm, gauss_aux_sqrt_two_inv_sq]
  norm_num

lemma gauss_aux_cgauss_im_pow_four : ∫ z, z.im ^ 4 ∂cgauss = 3 / 4 := by
  rw [gauss_aux_integral_cgauss]
  have h : ∀ w : ℂ, ((((Real.sqrt 2)⁻¹ : ℝ) • w).im) ^ 4 =
      (((Real.sqrt 2)⁻¹ : ℝ) ^ 2) ^ 2 * (imCLM w) ^ 4 := by
    intro w; rw [Complex.smul_im, smul_eq_mul, imCLM_apply]; ring
  simp_rw [h]
  rw [integral_const_mul, gauss_aux_std_pow_four _ imCLM_norm, gauss_aux_sqrt_two_inv_sq]
  norm_num

theorem cgauss_integral_norm_cube_le : ∫ z, ‖z‖ ^ 3 ∂cgauss ≤ 2 := by
  have h4 := cgauss_integrable_norm_pow 4
  have hre : Integrable (fun z : ℂ => z.re ^ 4) cgauss := by
    refine h4.mono' (by fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 4
  have him : Integrable (fun z : ℂ => z.im ^ 4) cgauss := by
    refine h4.mono' (by fun_prop) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm z) 4
  have hA : Integrable (fun z : ℂ => ‖z‖ ^ 2 / 2 + z.re ^ 4) cgauss :=
    ((cgauss_integrable_norm_pow 2).div_const 2).add hre
  have hB : Integrable (fun z : ℂ => ‖z‖ ^ 2 / 2) cgauss :=
    (cgauss_integrable_norm_pow 2).div_const 2
  have hg : Integrable (fun z : ℂ => ‖z‖ ^ 2 / 2 + z.re ^ 4 + z.im ^ 4) cgauss := hA.add him
  have hle : ∫ z, ‖z‖ ^ 3 ∂cgauss ≤ ∫ z, (‖z‖ ^ 2 / 2 + z.re ^ 4 + z.im ^ 4) ∂cgauss := by
    refine integral_mono (cgauss_integrable_norm_pow 3) hg fun z => ?_
    have hr : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hn : 0 ≤ ‖z‖ := norm_nonneg z
    simp only
    nlinarith [sq_nonneg (‖z‖ * (‖z‖ - 1)), sq_nonneg (z.re ^ 2 - z.im ^ 2)]
  rw [integral_add hA him, integral_add hB hre, integral_div,
    cgauss_integral_norm_sq, gauss_aux_cgauss_re_pow_four, gauss_aux_cgauss_im_pow_four] at hle
  linarith

theorem cgauss_integral_re_mul (c : ℂ) : ∫ z, (starRingEnd ℂ z * c).re ∂cgauss = 0 := by
  have h : ∫ z, (starRingEnd ℂ z * c).re ∂(cgauss.map (fun z => -z)) =
      ∫ z, (starRingEnd ℂ z * c).re ∂cgauss := by rw [cgauss_map_neg]
  rw [integral_map (by fun_prop) (by fun_prop)] at h
  simp only [map_neg, neg_mul, neg_re, integral_neg] at h
  linarith

theorem cgauss_integral_re_mul_sq (c : ℂ) :
    ∫ z, (starRingEnd ℂ z * c).re ^ 2 ∂cgauss = ‖c‖ ^ 2 / 2 := by
  rw [gauss_aux_integral_cgauss]
  have h : ∀ w : ℂ, (starRingEnd ℂ (((Real.sqrt 2)⁻¹ : ℝ) • w) * c).re ^ 2 =
      ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 * (innerSL ℝ c w) ^ 2 := by
    intro w
    rw [innerSL_apply_apply, Complex.inner, Complex.real_smul, map_mul, Complex.conj_ofReal]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [h]
  rw [integral_const_mul, gauss_aux_std_sq, innerSL_apply_norm, gauss_aux_sqrt_two_inv_sq]
  ring

/-- `|κ_δ| ≤ |log δ| + 1` for `0 < δ ≤ 1` (since `log δ ≤ φ_δ(z) ≤ |z|²/2`). -/
theorem kappa_abs_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : |kappa δ| ≤ |Real.log δ| + 1 := by
  have hlogneg : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlow : ∀ z : ℂ, Real.log δ ≤ phiD δ z := by
    intro z
    unfold phiD
    have h1 : δ ^ 2 ≤ ‖z‖ ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg ‖z‖]
    have h2 : Real.log (δ ^ 2) ≤ Real.log (‖z‖ ^ 2 + δ ^ 2) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2; push_cast at h2; linarith
  have hup : ∀ z : ℂ, phiD δ z ≤ ‖z‖ ^ 2 / 2 := by
    intro z
    unfold phiD
    have h := Real.log_le_sub_one_of_pos (show 0 < ‖z‖ ^ 2 + δ ^ 2 by positivity)
    have : δ ^ 2 ≤ 1 := by nlinarith
    linarith
  have hmeas : Measurable (phiD δ) := by unfold phiD; fun_prop
  have hint : Integrable (phiD δ) cgauss := by
    refine Integrable.mono' ((integrable_const |Real.log δ|).add
      ((cgauss_integrable_norm_pow 2).div_const 2)) hmeas.aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_le, abs_of_nonpos hlogneg]
    have h1 := hlow z
    have h2 := hup z
    have h3 : 0 ≤ ‖z‖ ^ 2 / 2 := by positivity
    constructor <;> simp only [Pi.add_apply] <;> linarith
  have hk1 : Real.log δ ≤ kappa δ := by
    unfold kappa
    have := integral_mono (integrable_const (Real.log δ)) hint hlow
    simpa using this
  have hk2 : kappa δ ≤ 1 / 2 := by
    unfold kappa
    have := integral_mono hint ((cgauss_integrable_norm_pow 2).div_const 2) hup
    rw [integral_div, cgauss_integral_norm_sq] at this
    linarith
  rw [abs_le]; constructor
  · have := neg_abs_le (Real.log δ); linarith
  · have := abs_nonneg (Real.log δ); linarith

end E522

end

/- ## Section: `Lindeberg` -/

section

/-
# Lindeberg replacement with a rotation-invariant complex Gaussian and Abel summation

Target: for a Rademacher sum `W = ∑_{k<N} sgn(x_k) ρ_k e^{ikθ}` with `∑ ρ_k² = 1`,
`E_x φ_δ(W)` is close to `κ_δ = E φ_δ(γ)`.

Proof plan (single Gaussian telescoping, only finite cube averages + integrals over `ℂ`):
* `τ_j := √(∑_{k<j} ρ_k²)`, `a_j := ρ_j e^{ijθ}`, `R_j(x) := ∑_{k>j} sgn(x_k) a_k`
  (so `R_j` does not depend on `x_j`), and
  `H_j := avg_x ∫ φ(τ_j γ + sgn(x_j) a_j + R_j(x)) dγ`,
  `H'_j := avg_x ∫ φ(τ_{j+1} γ + R_j(x)) dγ`.
  Then `H_0 = E_x φ(W)` (since `τ_0 = 0`), `H'_{N-1} = κ_δ` (since `τ_N = 1`), and
  `H'_j = H_{j+1}` (reindexing).
* Stability (`cgauss_stable`): `H'_j = avg_x ∫∫ φ(τ_j γ + γ' a_j + R_j(x)) dγ dγ'`.
* Taylor (`phiD_taylor3`) at `U = τ_j γ + R_j(x)` for `w = sgn(x_j) a_j` and for `w = γ' a_j`:
  first order terms vanish (flip `x_j`; `cgauss_integral_re_mul`), the second order terms
  differ by `−½ Re(conj(a_j)² Qfun δ U)` (`second_order_mismatch`,
  `cgauss_integral_re_mul_sq`, `cgauss_integral_norm_sq`), and the remainders are
  `≤ (7/3)(1 + E|γ|³) ρ_j³/δ³ ≤ 7 ρ_j³/δ³`.
* Abel summation (`Finset.sum_range_by_parts`) with `c_j := avg_x ∫ Qfun δ (τ_j γ + R_j(x)) dγ`,
  `‖c_j‖ ≤ 1/(4δ²)`, `‖c_{j+1} − c_j‖ ≤ (2/δ³)·(ρ_j E|γ| + ρ_{j+1}) ≤ 4ρmax/δ³`
  (note `τ_{j+1} − τ_j ≤ ρ_j`), and partial sums `P_J = ∑_{j<J} ρ_j² e^{-2ijθ}` bounded by `Pmax`.

Implementation (helper lemmas, all prefixed `lind_aux_`):
* cube averages: `cubeAvg_const`, `abs_cubeAvg_le`, the coordinate flip `flip` and
  `cubeAvg_sgn_mul` (first order terms vanish), complex averages `avgC`;
* integrability over `cgauss`: `int_phiD`, `int_bdd`, `int_re_mul`, `int_re_mul_sq`;
* `gauss_taylor`: `|E φ(U + γa) − φ(U) − ½(|a|²/q − |U|²|a|²/q²)| ≤ (14/3)|a|³/δ³`;
* `stable`: stability + Fubini for `φ(τγ + aγ' + R)`;
* `core`: one replacement step for a fixed tail `R` and sign `s`;
* `a`, `tau`, `tail`, `H`, `c`, `step`: here `H_j` uses the tail `∑_{k ≥ j}` (so `H'_j = H_{j+1}`
  holds by definition), and `|H_j − H_{j+1} + ½Re(conj(a_j)² c_j)| ≤ 7ρ_j³/δ³`;
* `c_norm`, `c_diff`, `abel` (summation by parts, proved by induction) and the assembly;
  the final constant obtained is `7ρmax/δ³ + Pmax(1/(8δ²) + 2Nρmax/δ³)`.
-/

open Real Complex MeasureTheory

namespace E522

/- ### Cube averages -/

lemma lind_aux_cubeAvg_const (N : ℕ) (c : ℝ) : cubeAvg N (fun _ => c) = c := by
  unfold cubeAvg
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin]

lemma lind_aux_abs_cubeAvg_le {N : ℕ} (F : (Fin N → Bool) → ℝ) (C : ℝ) (h : ∀ x, |F x| ≤ C) :
    |cubeAvg N F| ≤ C := by
  unfold cubeAvg
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
  calc |∑ x, F x| ≤ ∑ x, |F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : Fin N → Bool, C := Finset.sum_le_sum (fun x _ => h x)
    _ = C * 2 ^ N := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        Fintype.card_fin]
      ring

/-- flipping coordinate `i` -/
def lind_aux_flip {N : ℕ} (i : Fin N) (x : Fin N → Bool) : Fin N → Bool :=
  Function.update x i (!x i)

lemma lind_aux_flip_involutive {N : ℕ} (i : Fin N) : Function.Involutive (lind_aux_flip i) := by
  intro x
  funext k
  by_cases hk : k = i
  · subst hk; simp [lind_aux_flip]
  · simp [lind_aux_flip, Function.update_of_ne hk]

lemma lind_aux_sgn_not (b : Bool) : sgn (!b) = - sgn b := by
  cases b <;> simp [sgn]

lemma lind_aux_cubeAvg_sgn_mul {N : ℕ} (i : Fin N) (G : (Fin N → Bool) → ℝ)
    (hG : ∀ x, G (lind_aux_flip i x) = G x) :
    cubeAvg N (fun x => sgn (x i) * G x) = 0 := by
  unfold cubeAvg
  have key : ∑ x, sgn (x i) * G x = -∑ x, sgn (x i) * G x := by
    set σ := (lind_aux_flip_involutive i).toPerm (lind_aux_flip i) with hσ
    calc ∑ x, sgn (x i) * G x = ∑ x, sgn (σ x i) * G (σ x) :=
          (Equiv.sum_comp σ (fun x => sgn (x i) * G x)).symm
      _ = ∑ x, -(sgn (x i) * G x) := by
          apply Finset.sum_congr rfl
          intro x _
          simp only [hσ, Function.Involutive.coe_toPerm, hG]
          simp [lind_aux_flip, lind_aux_sgn_not]
      _ = -∑ x, sgn (x i) * G x := Finset.sum_neg_distrib _
  have : ∑ x, sgn (x i) * G x = 0 := by linarith
  rw [this, zero_div]

/-- complex cube average -/
noncomputable def lind_aux_avgC (N : ℕ) (G : (Fin N → Bool) → ℂ) : ℂ :=
  (∑ x, G x) / ((2 ^ N : ℝ) : ℂ)

lemma lind_aux_re_mul_avgC {N : ℕ} (w : ℂ) (G : (Fin N → Bool) → ℂ) :
    (w * lind_aux_avgC N G).re = cubeAvg N (fun x => (w * G x).re) := by
  unfold lind_aux_avgC cubeAvg
  rw [mul_div_assoc', Complex.div_ofReal_re, Finset.mul_sum, Complex.re_sum]

lemma lind_aux_avgC_sub {N : ℕ} (G G' : (Fin N → Bool) → ℂ) :
    lind_aux_avgC N G - lind_aux_avgC N G' = lind_aux_avgC N (fun x => G x - G' x) := by
  unfold lind_aux_avgC
  rw [Finset.sum_sub_distrib, sub_div]

lemma lind_aux_norm_avgC_le {N : ℕ} (G : (Fin N → Bool) → ℂ) (C : ℝ) (h : ∀ x, ‖G x‖ ≤ C) :
    ‖lind_aux_avgC N G‖ ≤ C := by
  unfold lind_aux_avgC
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2, div_le_iff₀ h2]
  calc ‖∑ x, G x‖ ≤ ∑ x, ‖G x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Fin N → Bool, C := Finset.sum_le_sum (fun x _ => h x)
    _ = C * 2 ^ N := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_bool,
        Fintype.card_fin]
      ring

/- ### Integrability over `cgauss` -/

lemma lind_aux_abs_phiD_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (w : ℂ) :
    |phiD δ w| ≤ |Real.log δ| + ‖w‖ ^ 2 / 2 := by
  obtain ⟨h1, h2⟩ := phiD_bounds hδ hδ1 w
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log δ)
    have : 0 ≤ ‖w‖ ^ 2 / 2 := by positivity
    linarith
  · have := abs_nonneg (Real.log δ)
    linarith

lemma lind_aux_int_phiD {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (c R : ℂ) :
    Integrable (fun z => phiD δ (c * z + R)) cgauss := by
  refine Integrable.mono' (g := fun z => |Real.log δ| + ‖R‖ ^ 2 + ‖c‖ ^ 2 * ‖z‖ ^ 2)
    ((integrable_const _).add ((cgauss_integrable_norm_pow 2).const_mul _)) ?_ ?_
  · exact ((phiD_continuous hδ).comp ((continuous_const.mul continuous_id).add
      continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (lind_aux_abs_phiD_le hδ hδ1 _).trans ?_
    have h1 : ‖c * z + R‖ ≤ ‖c‖ * ‖z‖ + ‖R‖ := by
      calc ‖c * z + R‖ ≤ ‖c * z‖ + ‖R‖ := norm_add_le _ _
        _ = ‖c‖ * ‖z‖ + ‖R‖ := by rw [norm_mul]
    have h2 : ‖c * z + R‖ ^ 2 ≤ (‖c‖ * ‖z‖ + ‖R‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (‖c‖ * ‖z‖ + ‖R‖) ^ 2 ≤ 2 * (‖c‖ ^ 2 * ‖z‖ ^ 2) + 2 * ‖R‖ ^ 2 := by
      nlinarith [sq_nonneg (‖c‖ * ‖z‖ - ‖R‖)]
    linarith

lemma lind_aux_int_bdd {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
    (f : ℂ → E) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ ≤ C) : Integrable f cgauss :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable (Filter.Eventually.of_forall hC)

lemma lind_aux_int_re_mul (c : ℂ) : Integrable (fun z : ℂ => (starRingEnd ℂ z * c).re) cgauss := by
  refine Integrable.mono' (g := fun z => ‖c‖ * ‖z‖ ^ 1)
    ((cgauss_integrable_norm_pow 1).const_mul _) ?_ ?_
  · exact (Complex.continuous_re.comp
      (Complex.continuous_conj.mul continuous_const)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, pow_one]
    calc |(starRingEnd ℂ z * c).re| ≤ ‖starRingEnd ℂ z * c‖ := Complex.abs_re_le_norm _
      _ = ‖c‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj, mul_comm]

lemma lind_aux_int_re_mul_sq (c : ℂ) :
    Integrable (fun z : ℂ => (starRingEnd ℂ z * c).re ^ 2) cgauss := by
  refine Integrable.mono' (g := fun z => ‖c‖ ^ 2 * ‖z‖ ^ 2)
    ((cgauss_integrable_norm_pow 2).const_mul _) ?_ ?_
  · exact ((Complex.continuous_re.comp (Complex.continuous_conj.mul continuous_const)).pow
      2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have : |(starRingEnd ℂ z * c).re| ≤ ‖c‖ * ‖z‖ := by
      calc |(starRingEnd ℂ z * c).re| ≤ ‖starRingEnd ℂ z * c‖ := Complex.abs_re_le_norm _
        _ = ‖c‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj, mul_comm]
    calc |(starRingEnd ℂ z * c).re| ^ 2 ≤ (‖c‖ * ‖z‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ‖c‖ ^ 2 * ‖z‖ ^ 2 := by ring

/- ### Gaussian second order expansion -/

lemma lind_aux_gauss_taylor {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (U a : ℂ) :
    |(∫ z, phiD δ (U + a * z) ∂cgauss) - phiD δ U
      - (‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2) - ‖U‖ ^ 2 * ‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2) ^ 2) / 2|
      ≤ 14 / 3 * ‖a‖ ^ 3 / δ ^ 3 := by
  set q := ‖U‖ ^ 2 + δ ^ 2 with hq
  set c1 := starRingEnd ℂ a * gphiD δ U with hc1
  set c2 := U * starRingEnd ℂ a with hc2
  set P : ℂ → ℝ := fun z => phiD δ U + (starRingEnd ℂ z * c1).re
    + ‖a‖ ^ 2 / (2 * q) * ‖z‖ ^ 2 - 1 / q ^ 2 * (starRingEnd ℂ z * c2).re ^ 2 with hP
  have hpt : ∀ z, |phiD δ (U + a * z) - P z| ≤ 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 * ‖z‖ ^ 3 := by
    intro z
    have h := phiD_taylor3 hδ U (a * z)
    have e1 : (starRingEnd ℂ (a * z) * gphiD δ U).re = (starRingEnd ℂ z * c1).re := by
      rw [hc1, map_mul]; ring_nf
    have e3 : (U * starRingEnd ℂ (a * z)).re = (starRingEnd ℂ z * c2).re := by
      rw [hc2, map_mul]; ring_nf
    rw [e1, e3, norm_mul, ← hq] at h
    calc |phiD δ (U + a * z) - P z|
        = |phiD δ (U + a * z) - phiD δ U - (starRingEnd ℂ z * c1).re
            - ((‖a‖ * ‖z‖) ^ 2 / q - 2 * (starRingEnd ℂ z * c2).re ^ 2 / q ^ 2) / 2| := by
          congr 1; simp only [hP]; ring_nf
      _ ≤ 7 / 3 * (‖a‖ * ‖z‖) ^ 3 / δ ^ 3 := h
      _ = 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 * ‖z‖ ^ 3 := by ring
  have i1 : Integrable (fun z => phiD δ (U + a * z)) cgauss := by
    have := lind_aux_int_phiD hδ hδ1 a U
    refine this.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [add_comm]
  have iP : Integrable P cgauss := by
    simp only [hP]
    refine (((integrable_const _).add (lind_aux_int_re_mul c1)).add
      ((cgauss_integrable_norm_pow 2).const_mul _)).sub ((lind_aux_int_re_mul_sq c2).const_mul _)
  have hPint : ∫ z, P z ∂cgauss = phiD δ U + (‖a‖ ^ 2 / q - ‖U‖ ^ 2 * ‖a‖ ^ 2 / q ^ 2) / 2 := by
    simp only [hP]
    rw [integral_sub, integral_add, integral_add, integral_const, integral_const_mul,
      integral_const_mul, cgauss_integral_re_mul, cgauss_integral_norm_sq,
      cgauss_integral_re_mul_sq]
    · simp only [probReal_univ, smul_eq_mul, one_mul]
      rw [hc2, norm_mul, Complex.norm_conj]
      ring_nf
    · exact integrable_const _
    · exact lind_aux_int_re_mul c1
    · exact (integrable_const _).add (lind_aux_int_re_mul c1)
    · exact (cgauss_integrable_norm_pow 2).const_mul _
    · exact ((integrable_const _).add (lind_aux_int_re_mul c1)).add
        ((cgauss_integrable_norm_pow 2).const_mul _)
    · exact (lind_aux_int_re_mul_sq c2).const_mul _
  have hdiff : (∫ z, phiD δ (U + a * z) ∂cgauss) - ∫ z, P z ∂cgauss
      = ∫ z, (phiD δ (U + a * z) - P z) ∂cgauss := (integral_sub i1 iP).symm
  have hbound : ‖∫ z, (phiD δ (U + a * z) - P z) ∂cgauss‖
      ≤ ∫ z, 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 * ‖z‖ ^ 3 ∂cgauss :=
    norm_integral_le_of_norm_le ((cgauss_integrable_norm_pow 3).const_mul _)
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hpt z))
  rw [integral_const_mul] at hbound
  have h3 := cgauss_integral_norm_cube_le
  have hc : 0 ≤ 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 := by positivity
  have h4 : 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 * ∫ z, ‖z‖ ^ 3 ∂cgauss ≤ 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 * 2 :=
    mul_le_mul_of_nonneg_left h3 hc
  rw [Real.norm_eq_abs, ← hdiff, hPint] at hbound
  calc _ = |(∫ z, phiD δ (U + a * z) ∂cgauss)
            - (phiD δ U + (‖a‖ ^ 2 / q - ‖U‖ ^ 2 * ‖a‖ ^ 2 / q ^ 2) / 2)| := by
          congr 1; ring
    _ ≤ _ := hbound.trans h4
    _ = 14 / 3 * ‖a‖ ^ 3 / δ ^ 3 := by ring

/- ### Stability + Fubini -/

lemma lind_aux_stable {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (τ τ' : ℝ) (hτ' : 0 ≤ τ') (a R : ℂ)
    (h : τ' ^ 2 = τ ^ 2 + ‖a‖ ^ 2) :
    Integrable (fun p : ℂ × ℂ => phiD δ ((τ : ℂ) * p.1 + a * p.2 + R)) (cgauss.prod cgauss) ∧
    ∫ z, phiD δ ((τ' : ℂ) * z + R) ∂cgauss
      = ∫ p, phiD δ ((τ : ℂ) * p.1 + a * p.2 + R) ∂(cgauss.prod cgauss) := by
  have hs := cgauss_stable (τ : ℂ) a
  have hsq : Real.sqrt (‖(τ : ℂ)‖ ^ 2 + ‖a‖ ^ 2) = τ' := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ← h]
    exact Real.sqrt_sq hτ'
  rw [hsq] at hs
  have hL : Measurable (fun p : ℂ × ℂ => (τ : ℂ) * p.1 + a * p.2) :=
    Continuous.measurable (by fun_prop)
  have hM : Measurable (fun z : ℂ => (τ' : ℂ) * z) := Continuous.measurable (by fun_prop)
  have hh : Continuous (fun w : ℂ => phiD δ (w + R)) :=
    (phiD_continuous hδ).comp (continuous_id.add continuous_const)
  have hint1 : Integrable (fun w : ℂ => phiD δ (w + R))
      (cgauss.map (fun z : ℂ => (τ' : ℂ) * z)) := by
    rw [integrable_map_measure hh.aestronglyMeasurable hM.aemeasurable]
    exact lind_aux_int_phiD hδ hδ1 (τ' : ℂ) R
  rw [← hs] at hint1
  refine ⟨(integrable_map_measure hh.aestronglyMeasurable hL.aemeasurable).mp hint1, ?_⟩
  calc ∫ z, phiD δ ((τ' : ℂ) * z + R) ∂cgauss
      = ∫ w, phiD δ (w + R) ∂(cgauss.map (fun z : ℂ => (τ' : ℂ) * z)) :=
        (integral_map hM.aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ w, phiD δ (w + R)
          ∂((cgauss.prod cgauss).map (fun p : ℂ × ℂ => (τ : ℂ) * p.1 + a * p.2)) := by
        rw [hs]
    _ = ∫ p, phiD δ ((τ : ℂ) * p.1 + a * p.2 + R) ∂(cgauss.prod cgauss) :=
        integral_map hL.aemeasurable hh.aestronglyMeasurable

/- ### One replacement step, for fixed tail `R` and sign `s` -/

lemma lind_aux_core {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (τ τ' : ℝ) (hτ' : 0 ≤ τ') (a R : ℂ)
    (h : τ' ^ 2 = τ ^ 2 + ‖a‖ ^ 2) (s : ℝ) (hs : s ^ 2 = 1) :
    |(∫ γ, phiD δ ((τ : ℂ) * γ + ((s : ℂ) * a + R)) ∂cgauss)
      - (∫ γ, phiD δ ((τ' : ℂ) * γ + R) ∂cgauss)
      + (starRingEnd ℂ a ^ 2 * ∫ γ, Qfun δ ((τ : ℂ) * γ + R) ∂cgauss).re / 2
      - s * ∫ γ, (starRingEnd ℂ a * gphiD δ ((τ : ℂ) * γ + R)).re ∂cgauss|
      ≤ 7 * ‖a‖ ^ 3 / δ ^ 3 := by
  obtain ⟨hint, heq⟩ := lind_aux_stable hδ hδ1 τ τ' hτ' a R h
  rw [heq, integral_prod _ hint]
  have i1 : Integrable (fun γ : ℂ => phiD δ ((τ : ℂ) * γ + ((s : ℂ) * a + R))) cgauss :=
    lind_aux_int_phiD hδ hδ1 _ _
  have i2 := hint.integral_prod_left
  have i3c : Integrable (fun γ : ℂ => starRingEnd ℂ a ^ 2 * Qfun δ ((τ : ℂ) * γ + R)) cgauss :=
    lind_aux_int_bdd _ (continuous_const.mul ((Qfun_continuous hδ).comp (by fun_prop)))
      (‖a‖ ^ 2 * (1 / (4 * δ ^ 2))) (fun γ => by
        rw [norm_mul, norm_pow, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (Qfun_norm_le hδ _) (by positivity))
  have i3 : Integrable (fun γ : ℂ => (starRingEnd ℂ a ^ 2 * Qfun δ ((τ : ℂ) * γ + R)).re / 2)
      cgauss := i3c.re.div_const 2
  have i4c : Integrable (fun γ : ℂ => starRingEnd ℂ a * gphiD δ ((τ : ℂ) * γ + R)) cgauss :=
    lind_aux_int_bdd _ (continuous_const.mul ((gphiD_continuous hδ).comp (by fun_prop)))
      (‖a‖ * (1 / (2 * δ))) (fun γ => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (gphiD_norm_le hδ _) (by positivity))
  have i4 : Integrable (fun γ : ℂ => s * (starRingEnd ℂ a * gphiD δ ((τ : ℂ) * γ + R)).re)
      cgauss := i4c.re.const_mul s
  have e3 : (∫ γ, starRingEnd ℂ a ^ 2 * Qfun δ ((τ : ℂ) * γ + R) ∂cgauss).re
      = ∫ γ, (starRingEnd ℂ a ^ 2 * Qfun δ ((τ : ℂ) * γ + R)).re ∂cgauss :=
    (integral_re i3c).symm
  have i12 : Integrable (fun γ : ℂ => phiD δ ((τ : ℂ) * γ + ((s : ℂ) * a + R))
      - ∫ z, phiD δ ((τ : ℂ) * (γ, z).1 + a * (γ, z).2 + R) ∂cgauss) cgauss := i1.sub i2
  have i123 : Integrable (fun γ : ℂ => phiD δ ((τ : ℂ) * γ + ((s : ℂ) * a + R))
      - (∫ z, phiD δ ((τ : ℂ) * (γ, z).1 + a * (γ, z).2 + R) ∂cgauss)
      + (starRingEnd ℂ a ^ 2 * Qfun δ ((τ : ℂ) * γ + R)).re / 2) cgauss := i12.add i3
  rw [← integral_const_mul (starRingEnd ℂ a ^ 2), e3, ← integral_div, ← integral_const_mul s,
    ← integral_sub i1 i2, ← integral_add i12 i3, ← integral_sub i123 i4]
  have hb := norm_integral_le_of_norm_le_const (μ := cgauss) (C := 7 * ‖a‖ ^ 3 / δ ^ 3)
    (f := fun γ => phiD δ ((τ : ℂ) * γ + ((s : ℂ) * a + R))
      - (∫ z, phiD δ ((τ : ℂ) * (γ, z).1 + a * (γ, z).2 + R) ∂cgauss)
      + (starRingEnd ℂ a ^ 2 * Qfun δ ((τ : ℂ) * γ + R)).re / 2
      - s * (starRingEnd ℂ a * gphiD δ ((τ : ℂ) * γ + R)).re) ?_
  · rw [probReal_univ, mul_one, Real.norm_eq_abs] at hb
    exact hb
  refine Filter.Eventually.of_forall (fun γ => ?_)
  rw [Real.norm_eq_abs]
  -- pointwise estimate
  have hU1 : (τ : ℂ) * γ + ((s : ℂ) * a + R) = ((τ : ℂ) * γ + R) + (s : ℂ) * a := by ring
  have hU2 : ∫ z, phiD δ ((τ : ℂ) * (γ, z).1 + a * (γ, z).2 + R) ∂cgauss
      = ∫ z, phiD δ (((τ : ℂ) * γ + R) + a * z) ∂cgauss := by
    congr 1; funext z
    show phiD δ ((τ : ℂ) * γ + a * z + R) = phiD δ (((τ : ℂ) * γ + R) + a * z)
    congr 1; ring
  rw [hU1, hU2]
  generalize (τ : ℂ) * γ + R = U
  have h1 := phiD_taylor3 hδ U ((s : ℂ) * a)
  have h2 := lind_aux_gauss_taylor hδ hδ1 U a
  have h3 := second_order_mismatch δ U a
  have habs : |s| = 1 := by rw [← Real.sqrt_sq_eq_abs, hs, Real.sqrt_one]
  have e1 : (starRingEnd ℂ ((s : ℂ) * a) * gphiD δ U).re
      = s * (starRingEnd ℂ a * gphiD δ U).re := by
    rw [map_mul, Complex.conj_ofReal, mul_assoc, Complex.re_ofReal_mul]
  have e2 : ‖(s : ℂ) * a‖ = ‖a‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, habs, one_mul]
  have e3 : (U * starRingEnd ℂ ((s : ℂ) * a)).re ^ 2 = (U * starRingEnd ℂ a).re ^ 2 := by
    rw [map_mul, Complex.conj_ofReal, show U * ((s : ℂ) * starRingEnd ℂ a)
      = (s : ℂ) * (U * starRingEnd ℂ a) by ring, Complex.re_ofReal_mul, mul_pow, hs, one_mul]
  rw [e1, e2, e3] at h1
  calc |phiD δ (U + (s : ℂ) * a) - (∫ z, phiD δ (U + a * z) ∂cgauss)
        + (starRingEnd ℂ a ^ 2 * Qfun δ U).re / 2 - s * (starRingEnd ℂ a * gphiD δ U).re|
      = |(phiD δ (U + (s : ℂ) * a) - phiD δ U - s * (starRingEnd ℂ a * gphiD δ U).re
          - (‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2)
            - 2 * (U * starRingEnd ℂ a).re ^ 2 / (‖U‖ ^ 2 + δ ^ 2) ^ 2) / 2)
        - ((∫ z, phiD δ (U + a * z) ∂cgauss) - phiD δ U
          - (‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2)
            - ‖U‖ ^ 2 * ‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2) ^ 2) / 2)| := by
        congr 1; linear_combination (1 / 2 : ℝ) * h3
    _ ≤ |phiD δ (U + (s : ℂ) * a) - phiD δ U - s * (starRingEnd ℂ a * gphiD δ U).re
          - (‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2)
            - 2 * (U * starRingEnd ℂ a).re ^ 2 / (‖U‖ ^ 2 + δ ^ 2) ^ 2) / 2|
        + |(∫ z, phiD δ (U + a * z) ∂cgauss) - phiD δ U
          - (‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2)
            - ‖U‖ ^ 2 * ‖a‖ ^ 2 / (‖U‖ ^ 2 + δ ^ 2) ^ 2) / 2| := abs_sub _ _
    _ ≤ 7 / 3 * ‖a‖ ^ 3 / δ ^ 3 + 14 / 3 * ‖a‖ ^ 3 / δ ^ 3 := add_le_add h1 h2
    _ = 7 * ‖a‖ ^ 3 / δ ^ 3 := by ring

/- ### The objects of the telescoping argument -/

/-- `a_j = ρ_j e^{ijθ}`. -/
noncomputable def lind_aux_a (ρ : ℕ → ℝ) (θ : ℝ) (j : ℕ) : ℂ := ((ρ j : ℝ) : ℂ) * ex j θ

/-- `τ_j = √(∑_{k<j} ρ_k²)`. -/
noncomputable def lind_aux_tau (ρ : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (∑ k ∈ Finset.range j, ρ k ^ 2)

/-- Tail sum `∑_{j ≤ k < N} sgn(x_k) a_k`. -/
noncomputable def lind_aux_tail {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) (j : ℕ) (x : Fin N → Bool) : ℂ :=
  ∑ k : Fin N, if j ≤ (k : ℕ) then ((sgn (x k) * ρ k : ℝ) : ℂ) * ex k θ else 0

/-- `H_j = avg_x ∫ φ(τ_j γ + ∑_{k ≥ j} sgn(x_k) a_k) dγ`. -/
noncomputable def lind_aux_H (N : ℕ) (ρ : ℕ → ℝ) (θ δ : ℝ) (j : ℕ) : ℝ :=
  cubeAvg N (fun x => ∫ γ, phiD δ ((lind_aux_tau ρ j : ℂ) * γ + lind_aux_tail ρ θ j x) ∂cgauss)

/-- `c_j = avg_x ∫ Q(τ_j γ + ∑_{k > j} sgn(x_k) a_k) dγ`. -/
noncomputable def lind_aux_c (N : ℕ) (ρ : ℕ → ℝ) (θ δ : ℝ) (j : ℕ) : ℂ :=
  lind_aux_avgC N (fun x =>
    ∫ γ, Qfun δ ((lind_aux_tau ρ j : ℂ) * γ + lind_aux_tail ρ θ (j + 1) x) ∂cgauss)

lemma lind_aux_norm_a (ρ : ℕ → ℝ) (θ : ℝ) (j : ℕ) : ‖lind_aux_a ρ θ j‖ = |ρ j| := by
  unfold lind_aux_a ex
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma lind_aux_conj_a_sq (ρ : ℕ → ℝ) (θ : ℝ) (j : ℕ) :
    starRingEnd ℂ (lind_aux_a ρ θ j) ^ 2
      = ((ρ j ^ 2 : ℝ) : ℂ) * Complex.exp (((-(2 * (j : ℝ) * θ)) : ℝ) * I) := by
  unfold lind_aux_a ex
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

lemma lind_aux_tail_zero {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) (x : Fin N → Bool) :
    lind_aux_tail ρ θ 0 x = Wfun ρ x θ := by
  simp [lind_aux_tail, Wfun]

lemma lind_aux_tail_ge {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) {j : ℕ} (hj : N ≤ j) (x : Fin N → Bool) :
    lind_aux_tail ρ θ j x = 0 := by
  unfold lind_aux_tail
  apply Finset.sum_eq_zero
  intro k _
  have := k.isLt
  rw [if_neg (by omega)]

lemma lind_aux_tail_succ {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) {j : ℕ} (hj : j < N) (x : Fin N → Bool) :
    lind_aux_tail ρ θ j x
      = ((sgn (x ⟨j, hj⟩) : ℝ) : ℂ) * lind_aux_a ρ θ j + lind_aux_tail ρ θ (j + 1) x := by
  unfold lind_aux_tail lind_aux_a
  have key : ∀ k : Fin N, (if j ≤ (k : ℕ) then ((sgn (x k) * ρ k : ℝ) : ℂ) * ex k θ else 0)
      = (if k = ⟨j, hj⟩ then ((sgn (x k) * ρ k : ℝ) : ℂ) * ex k θ else 0)
        + (if j + 1 ≤ (k : ℕ) then ((sgn (x k) * ρ k : ℝ) : ℂ) * ex k θ else 0) := by
    intro k
    by_cases h1 : k = ⟨j, hj⟩
    · subst h1; simp
    · have h2 : (k : ℕ) ≠ j := fun h => h1 (Fin.ext h)
      by_cases h3 : j + 1 ≤ (k : ℕ)
      · rw [if_pos (by omega), if_neg h1, if_pos h3, zero_add]
      · rw [if_neg (by omega), if_neg h1, if_neg h3, add_zero]
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  push_cast
  ring

lemma lind_aux_tail_flip {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) {j : ℕ} (hj : j < N) (x : Fin N → Bool) :
    lind_aux_tail ρ θ (j + 1) (lind_aux_flip ⟨j, hj⟩ x) = lind_aux_tail ρ θ (j + 1) x := by
  unfold lind_aux_tail
  apply Finset.sum_congr rfl
  intro k _
  by_cases h3 : j + 1 ≤ (k : ℕ)
  · have hk : k ≠ ⟨j, hj⟩ := fun h => by rw [h] at h3; simp at h3
    rw [if_pos h3, if_pos h3, lind_aux_flip, Function.update_of_ne hk]
  · rw [if_neg h3, if_neg h3]

lemma lind_aux_tau_nonneg (ρ : ℕ → ℝ) (j : ℕ) : 0 ≤ lind_aux_tau ρ j := Real.sqrt_nonneg _

lemma lind_aux_tau_sq (ρ : ℕ → ℝ) (j : ℕ) :
    lind_aux_tau ρ j ^ 2 = ∑ k ∈ Finset.range j, ρ k ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma lind_aux_tau_zero (ρ : ℕ → ℝ) : lind_aux_tau ρ 0 = 0 := by
  simp [lind_aux_tau]

lemma lind_aux_tau_N {N : ℕ} (ρ : ℕ → ℝ) (hρ1 : ∑ k ∈ Finset.range N, ρ k ^ 2 = 1) :
    lind_aux_tau ρ N = 1 := by
  simp [lind_aux_tau, hρ1]

lemma lind_aux_tau_succ_sq (ρ : ℕ → ℝ) (θ : ℝ) (j : ℕ) :
    lind_aux_tau ρ (j + 1) ^ 2 = lind_aux_tau ρ j ^ 2 + ‖lind_aux_a ρ θ j‖ ^ 2 := by
  rw [lind_aux_tau_sq, lind_aux_tau_sq, Finset.sum_range_succ, lind_aux_norm_a, sq_abs]

lemma lind_aux_tau_mono (ρ : ℕ → ℝ) (j : ℕ) : lind_aux_tau ρ j ≤ lind_aux_tau ρ (j + 1) := by
  unfold lind_aux_tau
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_range_succ]
  linarith [sq_nonneg (ρ j)]

lemma lind_aux_tau_succ_le (ρ : ℕ → ℝ) {j : ℕ} (hρ : 0 ≤ ρ j) :
    lind_aux_tau ρ (j + 1) ≤ lind_aux_tau ρ j + ρ j := by
  have h := lind_aux_tau_succ_sq ρ 0 j
  rw [lind_aux_norm_a, sq_abs] at h
  have h0 := lind_aux_tau_nonneg ρ j
  have h1 := lind_aux_tau_nonneg ρ (j + 1)
  nlinarith

lemma lind_aux_H_zero (N : ℕ) (ρ : ℕ → ℝ) (θ δ : ℝ) :
    lind_aux_H N ρ θ δ 0 = cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) := by
  unfold lind_aux_H
  congr 1
  funext x
  rw [lind_aux_tau_zero, lind_aux_tail_zero]
  simp

lemma lind_aux_H_N (N : ℕ) (ρ : ℕ → ℝ) (θ δ : ℝ) (hρ1 : ∑ k ∈ Finset.range N, ρ k ^ 2 = 1) :
    lind_aux_H N ρ θ δ N = kappa δ := by
  unfold lind_aux_H
  simp only [lind_aux_tau_N ρ hρ1, lind_aux_tail_ge ρ θ le_rfl]
  simp only [Complex.ofReal_one, one_mul, add_zero]
  exact lind_aux_cubeAvg_const N _

lemma lind_aux_cubeAvg_bound {N : ℕ} (F G K L : (Fin N → Bool) → ℝ) (hL : cubeAvg N L = 0)
    (C : ℝ) (h : ∀ x, |F x - G x + K x / 2 - L x| ≤ C) :
    |cubeAvg N F - cubeAvg N G + cubeAvg N K / 2| ≤ C := by
  have e : cubeAvg N F - cubeAvg N G + cubeAvg N K / 2
      = cubeAvg N (fun x => F x - G x + K x / 2 - L x) := by
    unfold cubeAvg at hL ⊢
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
    rw [div_eq_zero_iff] at hL
    rcases hL with hL | hL
    · rw [hL]; ring
    · exact absurd hL (pow_ne_zero _ two_ne_zero)
  rw [e]
  exact lind_aux_abs_cubeAvg_le _ C h

/-- One Lindeberg replacement step. -/
lemma lind_aux_step {N : ℕ} (ρ : ℕ → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k) (θ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) {j : ℕ} (hj : j < N) :
    |lind_aux_H N ρ θ δ j - lind_aux_H N ρ θ δ (j + 1)
      + (starRingEnd ℂ (lind_aux_a ρ θ j) ^ 2 * lind_aux_c N ρ θ δ j).re / 2|
      ≤ 7 * ρ j ^ 3 / δ ^ 3 := by
  set a := lind_aux_a ρ θ j with ha
  set L : (Fin N → Bool) → ℝ := fun x => ∫ γ, (starRingEnd ℂ a
    * gphiD δ ((lind_aux_tau ρ j : ℂ) * γ + lind_aux_tail ρ θ (j + 1) x)).re ∂cgauss with hLdef
  have hL : ∀ x, L (lind_aux_flip ⟨j, hj⟩ x) = L x := by
    intro x
    simp only [hLdef, lind_aux_tail_flip]
  have hzero := lind_aux_cubeAvg_sgn_mul ⟨j, hj⟩ L hL
  unfold lind_aux_H lind_aux_c
  rw [lind_aux_re_mul_avgC]
  refine lind_aux_cubeAvg_bound _ _ _ _ hzero _ (fun x => ?_)
  simp only [hLdef]
  rw [lind_aux_tail_succ ρ θ hj x]
  have := lind_aux_core hδ hδ1 (lind_aux_tau ρ j) (lind_aux_tau ρ (j + 1))
    (lind_aux_tau_nonneg ρ (j + 1)) a (lind_aux_tail ρ θ (j + 1) x)
    (lind_aux_tau_succ_sq ρ θ j) (sgn (x ⟨j, hj⟩)) (sgn_sq _)
  rw [ha, lind_aux_norm_a, abs_of_nonneg (hρ0 j)] at this
  exact this

/- ### Bounds on `c_j` -/

lemma lind_aux_c_norm {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ‖lind_aux_c N ρ θ δ j‖ ≤ 1 / (4 * δ ^ 2) := by
  unfold lind_aux_c
  apply lind_aux_norm_avgC_le
  intro x
  have := norm_integral_le_of_norm_le_const (μ := cgauss)
    (Filter.Eventually.of_forall (fun γ => Qfun_norm_le hδ
      ((lind_aux_tau ρ j : ℂ) * γ + lind_aux_tail ρ θ (j + 1) x)))
  rwa [probReal_univ, mul_one] at this

lemma lind_aux_tail_diff {N : ℕ} (ρ : ℕ → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k) (θ : ℝ) (ρmax : ℝ)
    (hρmax : ∀ k < N, ρ k ≤ ρmax) (hρmax0 : 0 ≤ ρmax) (j : ℕ) (x : Fin N → Bool) :
    ‖lind_aux_tail ρ θ (j + 1 + 1) x - lind_aux_tail ρ θ (j + 1) x‖ ≤ ρmax := by
  by_cases h1 : j + 1 < N
  · rw [lind_aux_tail_succ ρ θ h1 x]
    have e : lind_aux_tail ρ θ (j + 1 + 1) x
        - (((sgn (x ⟨j + 1, h1⟩) : ℝ) : ℂ) * lind_aux_a ρ θ (j + 1)
          + lind_aux_tail ρ θ (j + 1 + 1) x)
        = -(((sgn (x ⟨j + 1, h1⟩) : ℝ) : ℂ) * lind_aux_a ρ θ (j + 1)) := by ring
    rw [e, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_sgn, one_mul,
      lind_aux_norm_a, abs_of_nonneg (hρ0 _)]
    exact hρmax _ h1
  · rw [lind_aux_tail_ge ρ θ (by omega) x, lind_aux_tail_ge ρ θ (by omega) x, sub_zero, norm_zero]
    exact hρmax0

lemma lind_aux_c_diff {N : ℕ} (ρ : ℕ → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k) (θ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (ρmax : ℝ) (hρmax : ∀ k < N, ρ k ≤ ρmax) (hρmax0 : 0 ≤ ρmax) {j : ℕ} (hj : j < N) :
    ‖lind_aux_c N ρ θ δ (j + 1) - lind_aux_c N ρ θ δ j‖ ≤ 4 * ρmax / δ ^ 3 := by
  unfold lind_aux_c
  rw [lind_aux_avgC_sub]
  apply lind_aux_norm_avgC_le
  intro x
  have hint : ∀ (t : ℝ) (R : ℂ), Integrable (fun γ : ℂ => Qfun δ ((t : ℂ) * γ + R)) cgauss :=
    fun t R => lind_aux_int_bdd _ ((Qfun_continuous hδ).comp (by fun_prop)) _
      (fun γ => Qfun_norm_le hδ _)
  rw [← integral_sub (hint _ _) (hint _ _)]
  have hT := lind_aux_tail_diff ρ hρ0 θ ρmax hρmax hρmax0 j x
  have hτ1 := lind_aux_tau_mono ρ j
  have hτ2 := lind_aux_tau_succ_le ρ (hρ0 j)
  have hρj := hρmax j hj
  have hnorm : Integrable (fun γ : ℂ => ‖γ‖) cgauss := by
    simpa using cgauss_integrable_norm_pow 1
  refine (norm_integral_le_of_norm_le (g := fun γ : ℂ => 2 / δ ^ 3 * (ρmax * ‖γ‖ + ρmax))
    (((hnorm.const_mul ρmax).add (integrable_const ρmax)).const_mul _)
    (Filter.Eventually.of_forall (fun γ => ?_))).trans ?_
  · refine (Qfun_lip hδ _ _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc ‖(lind_aux_tau ρ (j + 1) : ℂ) * γ + lind_aux_tail ρ θ (j + 1 + 1) x
          - ((lind_aux_tau ρ j : ℂ) * γ + lind_aux_tail ρ θ (j + 1) x)‖
        = ‖((lind_aux_tau ρ (j + 1) - lind_aux_tau ρ j : ℝ) : ℂ) * γ
          + (lind_aux_tail ρ θ (j + 1 + 1) x - lind_aux_tail ρ θ (j + 1) x)‖ := by
          congr 1; push_cast; ring
      _ ≤ ‖((lind_aux_tau ρ (j + 1) - lind_aux_tau ρ j : ℝ) : ℂ) * γ‖
          + ‖lind_aux_tail ρ θ (j + 1 + 1) x - lind_aux_tail ρ θ (j + 1) x‖ := norm_add_le _ _
      _ ≤ ρmax * ‖γ‖ + ρmax := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
          exact add_le_add (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)) hT
  · rw [integral_const_mul, integral_add (hnorm.const_mul ρmax) (integrable_const ρmax),
      integral_const_mul, integral_const, probReal_univ, one_smul]
    have h1 := cgauss_integral_norm_le
    calc 2 / δ ^ 3 * (ρmax * ∫ γ, ‖γ‖ ∂cgauss + ρmax) ≤ 2 / δ ^ 3 * (ρmax * 1 + ρmax) := by
          gcongr
      _ = 4 * ρmax / δ ^ 3 := by ring

/- ### Abel summation -/

lemma lind_aux_abel (b c : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range n, b j * c j
      = (∑ i ∈ Finset.range n, b i) * c n
        - ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range (j + 1), b i) * (c (j + 1) - c j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => b j * c j), ih,
      Finset.sum_range_succ (fun j => (∑ i ∈ Finset.range (j + 1), b i) * (c (j + 1) - c j)),
      Finset.sum_range_succ b n]
    ring

theorem lindeberg {N : ℕ} (ρ : ℕ → ℝ) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hρ1 : ∑ k ∈ Finset.range N, ρ k ^ 2 = 1) (ρmax : ℝ) (hρmax : ∀ k < N, ρ k ≤ ρmax)
    (θ δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (Pmax : ℝ)
    (hP : ∀ J ≤ N, ‖∑ j ∈ Finset.range J,
        ((ρ j ^ 2 : ℝ) : ℂ) * Complex.exp (((-(2 * (j : ℝ) * θ)) : ℝ) * I)‖ ≤ Pmax) :
    |cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) - kappa δ| ≤
      10 * ρmax / δ ^ 3 + Pmax * (1 / δ ^ 2 + 10 * N * ρmax / δ ^ 3) := by
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hρ1
    · exact h
  have hρmax0 : 0 ≤ ρmax := (hρ0 0).trans (hρmax 0 hN)
  have hPmax0 : 0 ≤ Pmax := (norm_nonneg _).trans (hP 0 (Nat.zero_le _))
  set b : ℕ → ℂ := fun j => ((ρ j ^ 2 : ℝ) : ℂ) * Complex.exp (((-(2 * (j : ℝ) * θ)) : ℝ) * I)
    with hbdef
  set H := lind_aux_H N ρ θ δ with hH
  set c := lind_aux_c N ρ θ δ with hc
  have hstep : ∀ j ∈ Finset.range N,
      |H j - H (j + 1) + (b j * c j).re / 2| ≤ 7 * ρ j ^ 3 / δ ^ 3 := by
    intro j hj
    have := lind_aux_step ρ hρ0 θ hδ hδ1 (Finset.mem_range.mp hj)
    rw [lind_aux_conj_a_sq] at this
    exact this
  have htel : cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) - kappa δ
      = ∑ j ∈ Finset.range N, (H j - H (j + 1)) := by
    rw [Finset.sum_range_sub', hH, lind_aux_H_zero, lind_aux_H_N N ρ θ δ hρ1]
  have hsplit : ∑ j ∈ Finset.range N, (H j - H (j + 1))
      = ∑ j ∈ Finset.range N, (H j - H (j + 1) + (b j * c j).re / 2)
        - (∑ j ∈ Finset.range N, b j * c j).re / 2 := by
    rw [Complex.re_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hr : |∑ j ∈ Finset.range N, (H j - H (j + 1) + (b j * c j).re / 2)|
      ≤ 7 * ρmax / δ ^ 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
    have hle : ∀ j ∈ Finset.range N, 7 * ρ j ^ 3 / δ ^ 3 ≤ 7 * ρmax / δ ^ 3 * ρ j ^ 2 := by
      intro j hj
      have h1 := hρmax j (Finset.mem_range.mp hj)
      have h2 : ρ j * ρ j ^ 2 ≤ ρmax * ρ j ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
      calc 7 * ρ j ^ 3 / δ ^ 3 = 7 * (ρ j * ρ j ^ 2) / δ ^ 3 := by ring
        _ ≤ 7 * (ρmax * ρ j ^ 2) / δ ^ 3 := by gcongr
        _ = 7 * ρmax / δ ^ 3 * ρ j ^ 2 := by ring
    calc ∑ j ∈ Finset.range N, 7 * ρ j ^ 3 / δ ^ 3
        ≤ ∑ j ∈ Finset.range N, 7 * ρmax / δ ^ 3 * ρ j ^ 2 := Finset.sum_le_sum hle
      _ = 7 * ρmax / δ ^ 3 := by rw [← Finset.mul_sum, hρ1, mul_one]
  have habel : ‖∑ j ∈ Finset.range N, b j * c j‖
      ≤ Pmax * (1 / (4 * δ ^ 2)) + N * (Pmax * (4 * ρmax / δ ^ 3)) := by
    rw [lind_aux_abel b c N]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      exact mul_le_mul (hP N le_rfl) (lind_aux_c_norm ρ θ hδ N) (norm_nonneg _) hPmax0
    · refine (norm_sum_le _ _).trans ?_
      calc ∑ j ∈ Finset.range N, ‖(∑ i ∈ Finset.range (j + 1), b i) * (c (j + 1) - c j)‖
          ≤ ∑ j ∈ Finset.range N, Pmax * (4 * ρmax / δ ^ 3) := by
            apply Finset.sum_le_sum
            intro j hj
            have hj' := Finset.mem_range.mp hj
            rw [norm_mul]
            exact mul_le_mul (hP (j + 1) hj')
              (lind_aux_c_diff ρ hρ0 θ hδ ρmax hρmax hρmax0 hj') (norm_nonneg _) hPmax0
        _ = N * (Pmax * (4 * ρmax / δ ^ 3)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hre : |(∑ j ∈ Finset.range N, b j * c j).re| ≤ ‖∑ j ∈ Finset.range N, b j * c j‖ :=
    Complex.abs_re_le_norm _
  rw [htel, hsplit]
  have hX : 0 ≤ ρmax / δ ^ 3 := div_nonneg hρmax0 (by positivity)
  have hY : 0 ≤ 1 / δ ^ 2 := by positivity
  have hNP : 0 ≤ (N : ℝ) * Pmax * (ρmax / δ ^ 3) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) hPmax0) hX
  have hPY : 0 ≤ Pmax * (1 / δ ^ 2) := mul_nonneg hPmax0 hY
  calc |∑ j ∈ Finset.range N, (H j - H (j + 1) + (b j * c j).re / 2)
        - (∑ j ∈ Finset.range N, b j * c j).re / 2|
      ≤ |∑ j ∈ Finset.range N, (H j - H (j + 1) + (b j * c j).re / 2)|
        + |(∑ j ∈ Finset.range N, b j * c j).re / 2| := abs_sub _ _
    _ = |∑ j ∈ Finset.range N, (H j - H (j + 1) + (b j * c j).re / 2)|
        + |(∑ j ∈ Finset.range N, b j * c j).re| / 2 := by rw [abs_div, abs_two]
    _ ≤ 7 * ρmax / δ ^ 3 + (Pmax * (1 / (4 * δ ^ 2)) + N * (Pmax * (4 * ρmax / δ ^ 3))) / 2 := by
        gcongr
        exact hre.trans habel
    _ ≤ 10 * ρmax / δ ^ 3 + Pmax * (1 / δ ^ 2 + 10 * N * ρmax / δ ^ 3) := by
        have e : 10 * ρmax / δ ^ 3 + Pmax * (1 / δ ^ 2 + 10 * N * ρmax / δ ^ 3)
            - (7 * ρmax / δ ^ 3 + (Pmax * (1 / (4 * δ ^ 2)) + N * (Pmax * (4 * ρmax / δ ^ 3))) / 2)
            = 3 * (ρmax / δ ^ 3) + 7 / 8 * (Pmax * (1 / δ ^ 2))
              + 8 * ((N : ℝ) * Pmax * (ρmax / δ ^ 3)) := by ring
        linarith

end E522

end

/- ## Section: `SmallBall` -/

section

/-
# Super-polynomially small balls via separation of subset sums

For `θ` outside the bad set
`B = {θ | ∃ c ∈ {-1,0,1}^K \ {0}, |∑_{j<K} c_j e^{ijθ}| < 2ε}`,
the `2^K` values `∑_{j<K} bit(x_j) e^{ijθ}` are pairwise `≥ 2ε` apart, so conditioning on
`x_j, j ≥ K`, at most one choice of `x_{<K}` gives `|f_x(e^{iθ})| < ε`; hence
`P_x(|f_x(e^{iθ})| < ε) ≤ 2^{-K}`.

Measure of `B`: for fixed nonzero `c`, `q_c(z) = ∑ c_j z^j = z^v p(z)` with `p(0) ≠ 0`,
`d = deg p ≤ K-1`; if `d = 0` then `|q_c(e^{iθ})| = 1 ≥ 2ε`; otherwise `p = lead ∏(z − α_i)`
with `|lead| ≥ 1` (nonzero integer), so `|q_c(e^{iθ})| < 2ε` forces some
`|e^{iθ} − α_i| < (2ε)^{1/d} ≤ (2ε)^{1/K}`, and `{θ ∈ [0,2π] | |e^{iθ} − α| < r}` has normalised
measure `≤ r` (it lies in an arc of length `2πr`, as `|e^{iθ}−e^{iθ₀}| ≥ (2/π)·dist(θ,θ₀)`).
Union bound over `≤ 3^K` vectors `c` and `≤ K` roots.
-/

open Real Complex MeasureTheory

namespace E522

lemma sb_aux_ii_lt {h : ℝ → ℝ} (hh : Continuous h) (r a b : ℝ) :
    IntervalIntegrable (fun θ => if h θ < r then (1:ℝ) else 0) volume a b := by
  have hm : Measurable (fun θ => if h θ < r then (1:ℝ) else 0) :=
    Measurable.ite (measurableSet_lt hh.measurable measurable_const) measurable_const
      measurable_const
  refine (intervalIntegrable_const (c := (1:ℝ))).mono_fun hm.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun θ => ?_)
  simp only
  split_ifs <;> simp

lemma sb_aux_cav_mono {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π))
    (hG : IntervalIntegrable G volume 0 (2 * π)) (h : ∀ θ, F θ ≤ G θ) : cav F ≤ cav G := by
  unfold cav
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono (by positivity) hF hG h) (by positivity)

lemma sb_aux_cav_const (c : ℝ) : cav (fun _ => c) = c := by
  unfold cav
  rw [intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

lemma sb_aux_cav_add {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π))
    (hG : IntervalIntegrable G volume 0 (2 * π)) :
    cav (fun θ => F θ + G θ) = cav F + cav G := by
  unfold cav
  rw [intervalIntegral.integral_add hF hG]
  ring

lemma sb_aux_cav_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    (hF : ∀ i ∈ s, IntervalIntegrable (F i) volume 0 (2 * π)) :
    cav (fun θ => ∑ i ∈ s, F i θ) = ∑ i ∈ s, cav (F i) := by
  unfold cav
  rw [intervalIntegral.integral_finsetSum hF, Finset.mul_sum]

lemma sb_aux_ii_sum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (F i) volume a b) :
    IntervalIntegrable (fun θ => ∑ i ∈ s, F i θ) volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- `‖e^{iθ} − e^{iθ₀}‖ = 2 |sin((θ − θ₀)/2)|`. -/
lemma sb_aux_norm_exp_sub (θ θ₀ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - Complex.exp ((θ₀ : ℂ) * I)‖ = 2 * |Real.sin ((θ - θ₀) / 2)| := by
  have h1 : Complex.exp ((θ : ℂ) * I) - Complex.exp ((θ₀ : ℂ) * I) =
      Complex.exp ((θ₀ : ℂ) * I) * (Complex.exp (I * ((θ - θ₀ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul,
    Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  norm_num

/-- Jordan: for `|u| ≤ π`, `|u| / π ≤ |sin (u/2)|`. -/
lemma sb_aux_jordan {u : ℝ} (hu : |u| ≤ π) : |u| / π ≤ |Real.sin (u / 2)| := by
  have key : ∀ v : ℝ, 0 ≤ v → v ≤ π → v / π ≤ Real.sin (v / 2) := by
    intro v hv0 hvπ
    have := Real.mul_le_sin (x := v / 2) (by linarith) (by linarith)
    have hπ : 0 < π := Real.pi_pos
    calc v / π = 2 / π * (v / 2) := by field_simp
      _ ≤ Real.sin (v / 2) := this
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu ⊢
    have := key u h hu
    exact this.trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hu ⊢
    have := key (-u) (by linarith) hu
    rw [show -u / 2 = -(u / 2) by ring, Real.sin_neg] at this
    exact this.trans (neg_le_abs _)

/-- Normalised measure of an arc: `cav 1[|e^{iθ} − α| < ρ] ≤ ρ`. -/
lemma sb_aux_arc (α : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    cav (fun θ => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) ≤ ρ := by
  have hcont : Continuous (fun θ : ℝ => ‖Complex.exp ((θ : ℂ) * I) - α‖) := by fun_prop
  by_cases hex : ∃ θ₀ : ℝ, ‖Complex.exp ((θ₀ : ℂ) * I) - α‖ < ρ
  swap
  · push Not at hex
    have : (fun θ : ℝ => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) =
        fun _ => 0 := by
      funext θ; rw [if_neg (not_lt.2 (hex θ))]
    rw [this, sb_aux_cav_const]; exact hρ
  obtain ⟨θ₀, hθ₀⟩ := hex
  set g : ℝ → ℝ := fun u => if |Real.sin (u / 2)| < ρ then 1 else 0 with hg
  have hgcont : Continuous (fun u : ℝ => |Real.sin (u / 2)|) := by fun_prop
  have hpt : ∀ θ : ℝ, (if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) ≤ g (θ - θ₀) := by
    intro θ
    by_cases hθ : ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ
    · rw [if_pos hθ]
      have h2 : ‖Complex.exp ((θ : ℂ) * I) - Complex.exp ((θ₀ : ℂ) * I)‖ < 2 * ρ := by
        calc ‖Complex.exp ((θ : ℂ) * I) - Complex.exp ((θ₀ : ℂ) * I)‖
            ≤ ‖Complex.exp ((θ : ℂ) * I) - α‖ + ‖α - Complex.exp ((θ₀ : ℂ) * I)‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ < ρ + ρ := by
              rw [norm_sub_rev α]
              exact add_lt_add hθ hθ₀
          _ = 2 * ρ := by ring
      rw [sb_aux_norm_exp_sub] at h2
      have h3 : |Real.sin ((θ - θ₀) / 2)| < ρ := by linarith
      simp only [hg, if_pos h3, le_refl]
    · rw [if_neg hθ]
      simp only [hg]
      split_ifs <;> norm_num
  have hgper : Function.Periodic g (2 * π) := by
    intro u
    simp only [hg]
    rw [show (u + 2 * π) / 2 = u / 2 + π by ring, Real.sin_add_pi, abs_neg]
  have hII1 : IntervalIntegrable (fun θ : ℝ => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ)
      else 0) volume 0 (2 * π) := sb_aux_ii_lt hcont ρ 0 (2 * π)
  have hII2 : IntervalIntegrable (fun θ : ℝ => g (θ - θ₀)) volume 0 (2 * π) := by
    have := sb_aux_ii_lt (h := fun θ : ℝ => |Real.sin ((θ - θ₀) / 2)|) (by fun_prop) ρ 0 (2 * π)
    simpa only [hg] using this
  have hshift : ∫ θ in (0:ℝ)..(2 * π), g (θ - θ₀) = ∫ u in (-π)..π, g u := by
    rw [intervalIntegral.integral_comp_sub_right g θ₀]
    have := hgper.intervalIntegral_add_eq (0 - θ₀) (-π)
    rw [show (0:ℝ) - θ₀ + 2 * π = 2 * π - θ₀ by ring, show -π + 2 * π = π by ring] at this
    exact this
  have hII3 : IntervalIntegrable g volume (-π) π := by
    have := sb_aux_ii_lt (h := fun u : ℝ => |Real.sin (u / 2)|) hgcont ρ (-π) π
    simpa only [hg] using this
  have hII4 : IntervalIntegrable (fun u : ℝ => if |u| < π * ρ then (1:ℝ) else 0) volume (-π) π :=
    sb_aux_ii_lt (h := fun u : ℝ => |u|) continuous_abs (π * ρ) (-π) π
  have hmono : ∫ u in (-π)..π, g u ≤ ∫ u in (-π)..π, (if |u| < π * ρ then (1:ℝ) else 0) := by
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos]) hII3 hII4
    intro u hu
    have hu' : |u| ≤ π := abs_le.2 ⟨hu.1, hu.2⟩
    simp only [hg]
    by_cases hs : |Real.sin (u / 2)| < ρ
    · rw [if_pos hs]
      have hj := sb_aux_jordan hu'
      have : |u| < π * ρ := by
        have hπ : 0 < π := Real.pi_pos
        have : |u| / π < ρ := lt_of_le_of_lt hj hs
        rw [div_lt_iff₀ hπ] at this
        linarith
      rw [if_pos this]
    · rw [if_neg hs]
      split_ifs <;> norm_num
  have hind : ∫ u in (-π)..π, (if |u| < π * ρ then (1:ℝ) else 0) ≤ 2 * π * ρ := by
    have hπ : 0 < π := Real.pi_pos
    rw [intervalIntegral.integral_of_le (by linarith)]
    have heq : (fun u : ℝ => if |u| < π * ρ then (1:ℝ) else 0) =
        (Set.Ioo (-(π * ρ)) (π * ρ)).indicator 1 := by
      funext u
      simp only [Set.indicator_apply, Set.mem_Ioo, Pi.one_apply, abs_lt]
    rw [heq, integral_indicator_one measurableSet_Ioo,
      measureReal_restrict_apply measurableSet_Ioo]
    calc volume.real (Set.Ioo (-(π * ρ)) (π * ρ) ∩ Set.Ioc (-π) π)
        ≤ volume.real (Set.Ioo (-(π * ρ)) (π * ρ)) :=
          measureReal_mono Set.inter_subset_left (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
      _ = 2 * π * ρ := by
          rw [Real.volume_real_Ioo_of_le (by nlinarith)]
          ring
  have hπ : 0 < π := Real.pi_pos
  calc cav (fun θ => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0)
      ≤ cav (fun θ => g (θ - θ₀)) := sb_aux_cav_mono hII1 hII2 hpt
    _ = (2 * π)⁻¹ * ∫ u in (-π)..π, g u := by unfold cav; rw [hshift]
    _ ≤ (2 * π)⁻¹ * (2 * π * ρ) := by
        apply mul_le_mul_of_nonneg_left (hmono.trans hind) (by positivity)
    _ = ρ := by field_simp


/-- A nonzero complex polynomial with leading coefficient of norm `≥ 1` and degree `≤ K`
that is `< δ` at `z` has a root within `δ^{1/K}` of `z`. -/
lemma sb_aux_root_close {K : ℕ} (hK : 1 ≤ K) (p : Polynomial ℂ) (hlead : 1 ≤ ‖p.leadingCoeff‖)
    (hdeg : p.natDegree ≤ K) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (z : ℂ)
    (hz : ‖p.eval z‖ < δ) : ∃ α ∈ p.roots, ‖z - α‖ < δ ^ ((1:ℝ) / K) := by
  by_contra hcon
  push Not at hcon
  set ρ := δ ^ ((1:ℝ) / K) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := Real.rpow_le_one hδ0.le hδ1.le (by positivity)
  have hρK : ρ ^ K = δ := by
    rw [hρ, one_div, Real.rpow_inv_natCast_pow hδ0.le (by omega)]
  have hnorm : ‖p.eval z‖ = ‖p.leadingCoeff‖ * (p.roots.map (fun α => ‖z - α‖)).prod := by
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots z, norm_mul]
    congr 1
    have := map_multiset_prod (normHom : ℂ →*₀ ℝ) (p.roots.map (fun α => z - α))
    rw [Multiset.map_map] at this
    exact this
  have hprod : ∀ s : Multiset ℂ, (∀ α ∈ s, ρ ≤ ‖z - α‖) →
      ρ ^ Multiset.card s ≤ (s.map (fun α => ‖z - α‖)).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons a s ih =>
      intro h
      rw [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, pow_succ, mul_comm]
      apply mul_le_mul (h a (Multiset.mem_cons_self a s))
        (ih (fun α hα => h α (Multiset.mem_cons_of_mem hα))) (by positivity) (norm_nonneg _)
  have hcard : Multiset.card p.roots ≤ K := (Polynomial.card_roots' p).trans hdeg
  have h1 : δ ≤ (p.roots.map (fun α => ‖z - α‖)).prod := by
    rw [← hρK]
    exact (pow_le_pow_of_le_one hρ0 hρ1 hcard).trans (hprod _ hcon)
  have h2 : 0 ≤ (p.roots.map (fun α => ‖z - α‖)).prod := by
    apply Multiset.prod_nonneg
    intro a ha
    simp only [Multiset.mem_map] at ha
    obtain ⟨b, _, rfl⟩ := ha
    exact norm_nonneg _
  have : δ ≤ ‖p.eval z‖ := by
    rw [hnorm]
    nlinarith
  linarith

/-- The polynomial `∑_{j<K} c_j X^j`. -/
noncomputable def sb_aux_P {K : ℕ} (c : Fin K → ℤ) : Polynomial ℂ :=
  ∑ j : Fin K, Polynomial.monomial (j : ℕ) ((c j : ℤ) : ℂ)

lemma sb_aux_P_eval {K : ℕ} (c : Fin K → ℤ) (z : ℂ) :
    (sb_aux_P c).eval z = ∑ j : Fin K, (c j : ℂ) * z ^ (j : ℕ) := by
  simp [sb_aux_P, Polynomial.eval_finsetSum]

lemma sb_aux_P_coeff {K : ℕ} (c : Fin K → ℤ) (n : ℕ) :
    (sb_aux_P c).coeff n = ((∑ j : Fin K, if (j : ℕ) = n then c j else 0 : ℤ) : ℂ) := by
  simp only [sb_aux_P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

lemma sb_aux_P_natDegree {K : ℕ} (c : Fin K → ℤ) : (sb_aux_P c).natDegree ≤ K := by
  unfold sb_aux_P
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans j.isLt.le

lemma sb_aux_P_lead {K : ℕ} (c : Fin K → ℤ) (hc : c ≠ 0) :
    1 ≤ ‖(sb_aux_P c).leadingCoeff‖ := by
  have hne : sb_aux_P c ≠ 0 := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hc
    intro h0
    have h1 := congrArg (fun p => Polynomial.coeff p (j : ℕ)) h0
    simp only [sb_aux_P_coeff, Polynomial.coeff_zero] at h1
    have h2 : (∑ j' : Fin K, if (j' : ℕ) = (j : ℕ) then c j' else 0 : ℤ) = c j := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [if_neg (fun h => hb (Fin.ext h))]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [h2] at h1
    exact hj (by exact_mod_cast h1)
  have hlc : (sb_aux_P c).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hne
  rw [Polynomial.leadingCoeff, sb_aux_P_coeff] at hlc ⊢
  set m := (∑ j : Fin K, if (j : ℕ) = (sb_aux_P c).natDegree then c j else 0 : ℤ)
  have hm0 : m ≠ 0 := by
    intro h; apply hlc; simp [h]
  rw [Complex.norm_intCast]
  exact_mod_cast Int.one_le_abs hm0


lemma sb_aux_eval_poly {N : ℕ} (x : Fin N → Bool) (z : ℂ) :
    (poly x).eval z = ∑ k : Fin N, ((bit (x k) : ℝ) : ℂ) * z ^ (k : ℕ) := by
  simp [poly, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma sb_aux_sum_castLE {M : Type*} [AddCommMonoid M] {N K : ℕ} (hKN : K ≤ N) (g : Fin N → M)
    (hg : ∀ k : Fin N, K ≤ (k : ℕ) → g k = 0) :
    ∑ k : Fin N, g k = ∑ j : Fin K, g (Fin.castLE hKN j) := by
  classical
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE hKN)
    (fun a _ b _ h => Fin.castLE_injective hKN h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply hg
  by_contra hlt
  push Not at hlt
  exact hk (Finset.mem_image.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

/-- The nonzero `{-1,0,1}` vectors. -/
def sb_aux_S (K : ℕ) : Finset (Fin K → ℤ) :=
  (Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ)).erase 0

lemma sb_aux_S_card (K : ℕ) : (sb_aux_S K).card ≤ 3 ^ K := by
  unfold sb_aux_S
  refine (Finset.card_erase_le).trans ?_
  rw [Fintype.card_piFinset]
  simp

/-- Separation: if all nonzero `{-1,0,1}` combinations of `1, z, …, z^{K-1}` have norm `≥ 2ε`,
then at most a `2^{-K}` fraction of the cube has `|f_x(z)| < ε`. -/
lemma sb_aux_sep {N K : ℕ} (hKN : K ≤ N) (ε : ℝ) (z : ℂ)
    (hz : ∀ c ∈ sb_aux_S K, 2 * ε ≤ ‖∑ j : Fin K, (c j : ℂ) * z ^ (j : ℕ)‖) :
    cubeProb N (fun x => ‖(poly x).eval z‖ < ε) ≤ (1 / 2) ^ K := by
  classical
  unfold cubeProb
  set s := Finset.univ.filter (fun x : Fin N → Bool => ‖(poly x).eval z‖ < ε) with hs
  let f : (Fin N → Bool) → (Fin (N - K) → Bool) := fun x i => x ⟨(i : ℕ) + K, by omega⟩
  have hinj : Set.InjOn f s := by
    intro x hx x' hx' hfx
    simp only [hs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
    -- the difference vector
    let c : Fin K → ℤ := fun j =>
      (if x (Fin.castLE hKN j) then 1 else 0) - (if x' (Fin.castLE hKN j) then 1 else 0)
    have hcmem : c ∈ Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ) := by
      rw [Fintype.mem_piFinset]
      intro j
      simp only [c]
      split_ifs <;> simp
    have hsame : ∀ k : Fin N, K ≤ (k : ℕ) → x k = x' k := by
      intro k hk
      have := congrFun hfx ⟨(k : ℕ) - K, by omega⟩
      simp only [f] at this
      have hk' : (⟨(k : ℕ) - K + K, by omega⟩ : Fin N) = k := Fin.ext (by simp; omega)
      rwa [hk'] at this
    have hdiff : (poly x).eval z - (poly x').eval z = ∑ j : Fin K, (c j : ℂ) * z ^ (j : ℕ) := by
      rw [sb_aux_eval_poly, sb_aux_eval_poly, ← Finset.sum_sub_distrib]
      rw [sb_aux_sum_castLE hKN]
      · apply Finset.sum_congr rfl
        intro j _
        simp only [c, bit, Fin.val_castLE]
        split_ifs <;> simp
      · intro k hk
        rw [hsame k hk, sub_self]
    have hc0 : c = 0 := by
      by_contra hne
      have h1 := hz c (Finset.mem_erase.2 ⟨hne, hcmem⟩)
      rw [← hdiff] at h1
      have h2 : ‖(poly x).eval z - (poly x').eval z‖ < 2 * ε := by
        calc ‖(poly x).eval z - (poly x').eval z‖
            ≤ ‖(poly x).eval z‖ + ‖(poly x').eval z‖ := norm_sub_le _ _
          _ < ε + ε := add_lt_add hx hx'
          _ = 2 * ε := by ring
      linarith
    funext k
    by_cases hk : (k : ℕ) < K
    · have h1 := congrFun hc0 ⟨k, hk⟩
      simp only [c, Pi.zero_apply] at h1
      have hk' : Fin.castLE hKN ⟨(k : ℕ), hk⟩ = k := Fin.ext rfl
      rw [hk'] at h1
      cases hxk : x k <;> cases hx'k : x' k <;> simp_all
    · exact hsame k (by omega)
  have hcard : s.card ≤ 2 ^ (N - K) := by
    have := Finset.card_le_card_of_injOn f (t := Finset.univ) (fun _ _ => Finset.mem_coe.2
      (Finset.mem_univ _)) hinj
    simpa using this
  have h2N : (2:ℝ) ^ N = 2 ^ (N - K) * 2 ^ K := by
    rw [← pow_add, Nat.sub_add_cancel hKN]
  rw [div_le_iff₀ (by positivity), h2N]
  have : ((s.card : ℕ) : ℝ) ≤ 2 ^ (N - K) := by exact_mod_cast hcard
  calc ((s.card : ℕ) : ℝ) ≤ 2 ^ (N - K) := this
    _ = (1 / 2) ^ K * (2 ^ (N - K) * 2 ^ K) := by
        rw [one_div, inv_pow]; field_simp


/-- Bad set bound for a fixed nonzero `{-1,0,1}` vector `c`. -/
lemma sb_aux_bad_c {K : ℕ} (hK : 1 ≤ K) (c : Fin K → ℤ) (hc : c ≠ 0) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) :
    cav (fun θ => if ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < δ
      then (1:ℝ) else 0) ≤ K * δ ^ ((1:ℝ) / K) := by
  classical
  set p := sb_aux_P c with hp
  set ρ := δ ^ ((1:ℝ) / K) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set R := p.roots.toFinset with hR
  have hpt : ∀ θ : ℝ, (if ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < δ
      then (1:ℝ) else 0) ≤
      ∑ α ∈ R, (if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) := by
    intro θ
    by_cases h : ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < δ
    · rw [if_pos h]
      rw [← sb_aux_P_eval] at h
      obtain ⟨α, hα, hlt⟩ := sb_aux_root_close hK p (sb_aux_P_lead c hc)
        (sb_aux_P_natDegree c) hδ0 hδ1 _ h
      calc (1:ℝ) = (if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) :=
            (if_pos hlt).symm
        _ ≤ ∑ α ∈ R, (if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) :=
            Finset.single_le_sum (f := fun α => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ
              then (1:ℝ) else 0) (fun β _ => by split_ifs <;> norm_num)
              (Multiset.mem_toFinset.2 hα)
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun β _ => by split_ifs <;> norm_num)
  have hcont1 : Continuous (fun θ : ℝ =>
      ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖) := by fun_prop
  have hII : ∀ α ∈ R, IntervalIntegrable
      (fun θ : ℝ => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) volume 0 (2 * π) :=
    fun α _ => sb_aux_ii_lt (h := fun θ : ℝ => ‖Complex.exp ((θ : ℂ) * I) - α‖) (by fun_prop)
      ρ 0 (2 * π)
  have hIIsum : IntervalIntegrable (fun θ : ℝ =>
      ∑ α ∈ R, (if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0)) volume 0 (2 * π) := by
    exact sb_aux_ii_sum R hII
  have hcardR : R.card ≤ K :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans (sb_aux_P_natDegree c))
  calc cav (fun θ => if ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < δ
        then (1:ℝ) else 0)
      ≤ cav (fun θ => ∑ α ∈ R, (if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0)) :=
        sb_aux_cav_mono (sb_aux_ii_lt hcont1 δ 0 (2 * π)) hIIsum hpt
    _ = ∑ α ∈ R, cav (fun θ => if ‖Complex.exp ((θ : ℂ) * I) - α‖ < ρ then (1:ℝ) else 0) :=
        sb_aux_cav_sum R hII
    _ ≤ ∑ α ∈ R, ρ := Finset.sum_le_sum (fun α _ => sb_aux_arc α hρ0)
    _ = R.card * ρ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * ρ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcardR) hρ0

/-- `cubeProb` of the small-value event as an average of indicators. -/
lemma sb_aux_cubeProb_eq {N : ℕ} (ε : ℝ) (θ : ℝ) :
    cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε) =
      (∑ x : Fin N → Bool,
        if ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε then (1:ℝ) else 0) / 2 ^ N := by
  classical
  unfold cubeProb
  rw [Finset.natCast_card_filter]

lemma sb_aux_ii_ind_poly {N : ℕ} (x : Fin N → Bool) (ε a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ =>
      if ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε then (1:ℝ) else 0) volume a b := by
  apply sb_aux_ii_lt (h := fun θ : ℝ => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖) _ ε a b
  exact ((poly x).continuous.comp (by fun_prop)).norm

lemma sb_aux_ii_cubeProb {N : ℕ} (ε a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ =>
      cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε)) volume a b := by
  simp_rw [sb_aux_cubeProb_eq]
  apply IntervalIntegrable.div_const
  exact sb_aux_ii_sum (Finset.univ : Finset (Fin N → Bool))
    (F := fun x θ => if ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε then (1:ℝ) else 0)
    (fun x _ => sb_aux_ii_ind_poly x ε a b)

theorem small_ball_sep {N K : ℕ} (hK1 : 1 ≤ K) (hKN : K ≤ N) (ε : ℝ) (hε : 0 < ε)
    (hε2 : 2 * ε < 1) :
    cav (fun θ => cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε)) ≤
      (1 / 2) ^ K + 3 ^ K * K * (2 * ε) ^ ((1 : ℝ) / K) := by
  classical
  set ρ := (2 * ε) ^ ((1:ℝ) / K) with hρ
  set S := sb_aux_S K with hS
  set Ic : (Fin K → ℤ) → ℝ → ℝ := fun c θ =>
    if ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < 2 * ε
      then (1:ℝ) else 0 with hIc
  have hIc_nonneg : ∀ c θ, 0 ≤ Ic c θ := fun c θ => by
    simp only [hIc]; split_ifs <;> norm_num
  have hpt : ∀ θ : ℝ, cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε) ≤
      (1 / 2) ^ K + ∑ c ∈ S, Ic c θ := by
    intro θ
    by_cases hB : ∃ c ∈ S,
        ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < 2 * ε
    · obtain ⟨c, hcS, hc⟩ := hB
      have h1 : cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε) ≤ 1 := by
        unfold cubeProb
        rw [div_le_one (by positivity)]
        have := Finset.card_filter_le (Finset.univ : Finset (Fin N → Bool))
          (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε)
        have h2 : ((Finset.univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
          simp
        rw [← h2]
        exact_mod_cast this
      have h2 : 1 ≤ ∑ c ∈ S, Ic c θ := by
        calc (1:ℝ) = Ic c θ := by simp only [hIc]; rw [if_pos hc]
          _ ≤ ∑ c ∈ S, Ic c θ :=
            Finset.single_le_sum (f := fun c => Ic c θ) (fun c _ => hIc_nonneg c θ) hcS
      have h3 : (0:ℝ) ≤ (1 / 2) ^ K := by positivity
      linarith
    · push Not at hB
      have h1 := sb_aux_sep hKN ε (Complex.exp ((θ : ℂ) * I)) hB
      have h2 : 0 ≤ ∑ c ∈ S, Ic c θ := Finset.sum_nonneg (fun c _ => hIc_nonneg c θ)
      linarith
  have hIIc : ∀ c ∈ S, IntervalIntegrable (Ic c) volume 0 (2 * π) := by
    intro c _
    exact sb_aux_ii_lt (h := fun θ : ℝ =>
      ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖) (by fun_prop)
      (2 * ε) 0 (2 * π)
  have hIIsum : IntervalIntegrable (fun θ => ∑ c ∈ S, Ic c θ) volume 0 (2 * π) := by
    exact sb_aux_ii_sum S hIIc
  have hIIconst : IntervalIntegrable (fun _ : ℝ => ((1:ℝ) / 2) ^ K) volume 0 (2 * π) :=
    intervalIntegrable_const
  have hc_bound : ∀ c ∈ S, cav (Ic c) ≤ K * ρ := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
    exact sb_aux_bad_c hK1 c hc0 (by positivity) hε2
  calc cav (fun θ => cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε))
      ≤ cav (fun θ => (1 / 2) ^ K + ∑ c ∈ S, Ic c θ) :=
        sb_aux_cav_mono (sb_aux_ii_cubeProb ε 0 (2 * π)) (hIIconst.add hIIsum) hpt
    _ = (1 / 2) ^ K + ∑ c ∈ S, cav (Ic c) := by
        rw [sb_aux_cav_add hIIconst hIIsum, sb_aux_cav_const, sb_aux_cav_sum S hIIc]
    _ ≤ (1 / 2) ^ K + ∑ c ∈ S, (K * ρ) := by
        gcongr with c hc
        exact hc_bound c hc
    _ = (1 / 2) ^ K + S.card * (K * ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / 2) ^ K + 3 ^ K * K * ρ := by
        have hS3 : (S.card : ℝ) ≤ 3 ^ K := by exact_mod_cast sb_aux_S_card K
        have hKρ : 0 ≤ (K : ℝ) * ρ := by positivity
        nlinarith

open scoped Classical in
/-- Fubini on `cube × [0,2π]`: the averaged small-ball probability equals the expected
measure of the small-value set. -/
theorem cav_cubeProb_eq {N : ℕ} (ε : ℝ) :
    cav (fun θ => cubeProb N (fun x => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε)) =
      cubeAvg N (fun x => cav (fun θ =>
        if ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε then 1 else 0)) := by
  unfold cav cubeAvg
  simp_rw [sb_aux_cubeProb_eq]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum (fun x _ => sb_aux_ii_ind_poly x ε 0 (2 * π)),
    ← Finset.mul_sum]
  ring

end E522

end

/- ## Section: `Anticonc` -/

section

/-
# Littlewood–Offord anti-concentration (Erdős' Sperner argument)

For every `θ`, either `#{k | |cos kθ| ≥ 1/√2} ≥ N/2` or `#{k | |sin kθ| ≥ 1/√2} ≥ N/2`
(pigeonhole, since `cos² + sin² = 1`). Project onto the real or imaginary part.
Conditioning on the coordinates outside the good index set `J` (`|J| = M ≥ N/2`),
the sign vectors on `J` whose (real) sum lies in a half-open interval of length
`2a` (`a = 1/√2 ≤ |y_k|`) form an antichain after flipping signs so that all `y_k > 0`,
hence at most `choose M (M/2)` of them (`IsAntichain.sperner`). The interval
`(t−r, t+r)` is covered by `⌈r/a⌉ ≤ √2 r + 1` such intervals, and
`choose M (M/2) · √M ≤ 2^M` (prove e.g. `(choose (2n) n)² (3n+1) ≤ 16^n` by induction).
-/

open Real Complex

namespace E522

section LoAux

open Finset

lemma lo_aux_sgn_mul (b : Bool) (y : ℝ) :
    sgn b * y = if b = decide (0 ≤ y) then |y| else -|y| := by
  by_cases hy : 0 ≤ y
  · cases b <;> simp [sgn, hy, abs_of_nonneg hy]
  · push Not at hy
    cases b <;> simp [sgn, hy.not_ge, abs_of_neg hy]

theorem lo_aux_sperner {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → ℝ) (a : ℝ)
    (hy : ∀ k, a ≤ |y k|) (c : ℝ) :
    (univ.filter (fun u : ι → Bool =>
      c ≤ ∑ k, sgn (u k) * y k ∧ ∑ k, sgn (u k) * y k < c + 2 * a)).card ≤
      (Fintype.card ι).choose (Fintype.card ι / 2) := by
  classical
  set S := univ.filter (fun u : ι → Bool =>
      c ≤ ∑ k, sgn (u k) * y k ∧ ∑ k, sgn (u k) * y k < c + 2 * a) with hS
  let φ : (ι → Bool) → Finset ι := fun u => univ.filter (fun k => u k = decide (0 ≤ y k))
  have hφ : Function.Injective φ := by
    intro u v huv
    funext k
    have := congrArg (fun s => k ∈ s) huv
    simp only [φ, mem_filter, mem_univ, true_and, eq_iff_iff] at this
    cases hu : u k <;> cases hv : v k <;> cases hd : decide (0 ≤ y k) <;> simp_all
  have hterm : ∀ u k, sgn (u k) * y k = if k ∈ φ u then |y k| else -|y k| := by
    intro u k
    rw [lo_aux_sgn_mul]
    simp [φ]
  have hanti : IsAntichain (· ⊆ ·) (SetLike.coe (S.image φ)) := by
    intro A hA B hB hAB hsub
    simp only [coe_image, Set.mem_image, mem_coe] at hA hB
    obtain ⟨u, hu, rfl⟩ := hA
    obtain ⟨v, hv, rfl⟩ := hB
    simp only [hS, mem_filter, mem_univ, true_and] at hu hv
    obtain ⟨k₀, hk₀v, hk₀u⟩ : ∃ k₀, k₀ ∈ φ v ∧ k₀ ∉ φ u := by
      by_contra hcon
      push Not at hcon
      exact hAB (Finset.Subset.antisymm hsub hcon)
    have key : ∑ k, sgn (u k) * y k + 2 * a ≤ ∑ k, sgn (v k) * y k := by
      have h1 : ∑ k, sgn (v k) * y k - ∑ k, sgn (u k) * y k =
          ∑ k, (sgn (v k) * y k - sgn (u k) * y k) := by
        rw [Finset.sum_sub_distrib]
      have h2 : ∀ k ∈ (univ : Finset ι), 0 ≤ sgn (v k) * y k - sgn (u k) * y k := by
        intro k _
        rw [hterm u k, hterm v k]
        by_cases hku : k ∈ φ u
        · have hkv : k ∈ φ v := hsub hku
          simp [hku, hkv]
        · by_cases hkv : k ∈ φ v
          · simp only [hku, hkv, if_true, if_false]
            have := abs_nonneg (y k)
            linarith
          · simp [hku, hkv]
      have h3 : sgn (v k₀) * y k₀ - sgn (u k₀) * y k₀ ≤
          ∑ k, (sgn (v k) * y k - sgn (u k) * y k) :=
        Finset.single_le_sum h2 (mem_univ k₀)
      have h4 : sgn (v k₀) * y k₀ - sgn (u k₀) * y k₀ = 2 * |y k₀| := by
        rw [hterm u k₀, hterm v k₀]
        simp only [hk₀u, hk₀v, if_true, if_false]
        ring
      have h5 := hy k₀
      linarith
    linarith [hu.1, hv.2]
  calc S.card = (S.image φ).card := (Finset.card_image_of_injective S hφ).symm
    _ ≤ _ := hanti.sperner
theorem lo_aux_fibre {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Finset ι) (y : ι → ℝ) (a : ℝ)
    (hy : ∀ k ∈ J, a ≤ |y k|) (c : ℝ) :
    (univ.filter (fun x : ι → Bool =>
      c ≤ ∑ k, sgn (x k) * y k ∧ ∑ k, sgn (x k) * y k < c + 2 * a)).card ≤
      2 ^ (Fintype.card ι - J.card) * J.card.choose (J.card / 2) := by
  classical
  set S := univ.filter (fun x : ι → Bool =>
      c ≤ ∑ k, sgn (x k) * y k ∧ ∑ k, sgn (x k) * y k < c + 2 * a) with hS
  let g : (ι → Bool) → ({k // k ∉ J} → Bool) := fun x k => x k
  have hfib : ∀ v ∈ S.image g,
      (S.filter (fun x => g x = v)).card ≤ J.card.choose (J.card / 2) := by
    intro v _
    set c' := c - ∑ k : {k // k ∉ J}, sgn (v k) * y k with hc'
    have hsp := lo_aux_sperner (ι := {k // k ∈ J}) (fun k => y k) a (fun k => hy k k.2) c'
    rw [Fintype.card_coe] at hsp
    refine le_trans ?_ hsp
    apply Finset.card_le_card_of_injOn (fun x (k : {k // k ∈ J}) => x k)
    · intro x hx
      simp only [mem_coe, hS, mem_filter, mem_univ, true_and] at hx
      obtain ⟨⟨h1, h2⟩, hgx⟩ := hx
      have hxv : ∀ k : {k // k ∉ J}, x k = v k := fun k => congrFun hgx k
      have hsplit : ∑ k, sgn (x k) * y k =
          ∑ k : {k // k ∈ J}, sgn (x k) * y k + ∑ k : {k // k ∉ J}, sgn (v k) * y k := by
        have e1 : ∑ k : {k // k ∉ J}, sgn (v k) * y k = ∑ k : {k // k ∉ J}, sgn (x k) * y k :=
          Finset.sum_congr rfl (fun k _ => by rw [hxv k])
        rw [e1, ← Finset.sum_subtype J (fun k => Iff.rfl) (fun k => sgn (x k) * y k),
          ← Finset.sum_subtype Jᶜ (fun k => Finset.mem_compl) (fun k => sgn (x k) * y k)]
        exact (Finset.sum_add_sum_compl J _).symm
      simp only [mem_coe, mem_filter, mem_univ, true_and]
      constructor <;> linarith
    · intro x hx x' hx' hxx'
      simp only [mem_coe, hS, mem_filter, mem_univ, true_and] at hx hx'
      funext k
      by_cases hk : k ∈ J
      · exact congrFun hxx' ⟨k, hk⟩
      · exact congrFun (hx.2.trans hx'.2.symm) ⟨k, hk⟩
  calc S.card ≤ J.card.choose (J.card / 2) * (S.image g).card :=
        Finset.card_le_mul_card_image S _ hfib
    _ ≤ J.card.choose (J.card / 2) * 2 ^ (Fintype.card ι - J.card) := by
        gcongr
        calc (S.image g).card ≤ (univ : Finset ({k // k ∉ J} → Bool)).card :=
              Finset.card_le_univ _
          _ = 2 ^ (Fintype.card ι - J.card) := by
            rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
              Fintype.card_subtype_compl, Fintype.card_coe]
    _ = _ := mul_comm _ _

theorem lo_aux_cover {α : Type*} [Fintype α] (L : α → ℝ) (a : ℝ) (ha : 0 < a) (B : ℕ)
    (hB : ∀ c : ℝ, (univ.filter (fun x => c ≤ L x ∧ L x < c + 2 * a)).card ≤ B)
    (t' r : ℝ) :
    (univ.filter (fun x => |L x + t'| < r)).card ≤ ⌈r / a⌉₊ * B := by
  classical
  set m := ⌈r / a⌉₊ with hm
  have hsub : univ.filter (fun x => |L x + t'| < r) ⊆
      (range m).biUnion (fun i : ℕ => univ.filter (fun x =>
        (-t' - r + 2 * a * i) ≤ L x ∧ L x < (-t' - r + 2 * a * i) + 2 * a)) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [abs_lt] at hx
    simp only [mem_biUnion, mem_range, mem_filter, mem_univ, true_and]
    set z := (L x + t' + r) / (2 * a) with hz
    have hz0 : 0 ≤ z := by
      rw [hz]
      apply div_nonneg _ (by positivity)
      linarith [hx.1]
    have hz2 : 2 * a * z = L x + t' + r := by
      rw [hz]
      field_simp
    have hfl1 : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le hz0
    have hfl2 : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
    refine ⟨⌊z⌋₊, ?_, ?_, ?_⟩
    · have h2 : z < r / a := by
        rw [hz, div_lt_div_iff₀ (by positivity) ha]
        nlinarith [hx.2]
      have h3 : r / a ≤ m := Nat.le_ceil _
      exact_mod_cast (lt_of_le_of_lt hfl1 (lt_of_lt_of_le h2 h3))
    · have : 2 * a * ⌊z⌋₊ ≤ 2 * a * z := by gcongr
      linarith
    · have : 2 * a * z < 2 * a * (⌊z⌋₊ + 1) := by gcongr
      linarith
  calc (univ.filter (fun x => |L x + t'| < r)).card
      ≤ ((range m).biUnion (fun i : ℕ => univ.filter (fun x =>
        (-t' - r + 2 * a * i) ≤ L x ∧ L x < (-t' - r + 2 * a * i) + 2 * a))).card :=
        card_le_card hsub
    _ ≤ ∑ i ∈ range m, (univ.filter (fun x =>
        (-t' - r + 2 * a * i) ≤ L x ∧ L x < (-t' - r + 2 * a * i) + 2 * a)).card :=
        card_biUnion_le
    _ ≤ ∑ i ∈ range m, B := sum_le_sum (fun i _ => hB _)
    _ = m * B := by simp

lemma lo_aux_centralBinom (n : ℕ) : n.centralBinom ^ 2 * (3 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Nat.succ_mul_centralBinom_succ n
    have hpos : 0 < (n + 1) ^ 2 := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    have hpoly : (2 * n + 1) ^ 2 * (3 * n + 4) ≤ 4 * (n + 1) ^ 2 * (3 * n + 1) := by
      ring_nf
      nlinarith
    calc (n + 1) ^ 2 * ((n + 1).centralBinom ^ 2 * (3 * (n + 1) + 1))
        = ((n + 1) * (n + 1).centralBinom) ^ 2 * (3 * n + 4) := by ring
      _ = (2 * (2 * n + 1) * n.centralBinom) ^ 2 * (3 * n + 4) := by rw [h]
      _ = 4 * ((2 * n + 1) ^ 2 * (3 * n + 4)) * n.centralBinom ^ 2 := by ring
      _ ≤ 4 * (4 * (n + 1) ^ 2 * (3 * n + 1)) * n.centralBinom ^ 2 := by gcongr
      _ = 16 * (n + 1) ^ 2 * (n.centralBinom ^ 2 * (3 * n + 1)) := by ring
      _ ≤ 16 * (n + 1) ^ 2 * 16 ^ n := by gcongr
      _ = (n + 1) ^ 2 * 16 ^ (n + 1) := by ring

lemma lo_aux_choose_odd (n : ℕ) : (2 * n + 1).choose n ≤ 2 * n.centralBinom := by
  have e1 : (n + 1).centralBinom = (2 * n + 1).choose n + (2 * n + 1).choose (n + 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (n + 1) = (2 * n + 1) + 1 by ring,
      Nat.choose_succ_succ']
  have e2 := Nat.choose_symm_half n
  have e3 := Nat.succ_mul_centralBinom_succ n
  rw [e1, e2] at e3
  nlinarith

lemma lo_aux_choose_sq (M : ℕ) : (M.choose (M / 2)) ^ 2 * M ≤ 4 ^ M := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' M
  · have h1 : 2 * n / 2 = n := by omega
    rw [h1, ← Nat.centralBinom_eq_two_mul_choose]
    have := lo_aux_centralBinom n
    calc n.centralBinom ^ 2 * (2 * n) ≤ n.centralBinom ^ 2 * (3 * n + 1) := by gcongr; omega
      _ ≤ 16 ^ n := this
      _ = 4 ^ (2 * n) := by rw [pow_mul]; norm_num
  · have h1 : (2 * n + 1) / 2 = n := by omega
    rw [h1]
    have h2 := lo_aux_choose_odd n
    have := lo_aux_centralBinom n
    calc ((2 * n + 1).choose n) ^ 2 * (2 * n + 1)
        ≤ (2 * n.centralBinom) ^ 2 * (3 * n + 1) := by gcongr; omega
      _ = 4 * (n.centralBinom ^ 2 * (3 * n + 1)) := by ring
      _ ≤ 4 * 16 ^ n := by gcongr
      _ = 4 ^ (2 * n + 1) := by rw [pow_succ, pow_mul]; norm_num; ring

lemma lo_aux_choose_sqrt (M : ℕ) : (M.choose (M / 2) : ℝ) * Real.sqrt M ≤ 2 ^ M := by
  have h := lo_aux_choose_sq M
  have h' : ((M.choose (M / 2) : ℝ)) ^ 2 * M ≤ ((2 : ℝ) ^ M) ^ 2 := by
    have : (((M.choose (M / 2)) ^ 2 * M : ℕ) : ℝ) ≤ ((4 ^ M : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    calc _ ≤ (4 : ℝ) ^ M := this
      _ = ((2 : ℝ) ^ M) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have e : ((M.choose (M / 2) : ℝ) * Real.sqrt M) ^ 2 = (M.choose (M / 2) : ℝ) ^ 2 * M := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
  rw [← e] at h'
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h'


lemma lo_aux_mono {N : ℕ} (P Q : (Fin N → Bool) → Prop) [DecidablePred Q]
    (h : ∀ x, P x → Q x) :
    cubeProb N P ≤ ((univ.filter Q).card : ℝ) / 2 ^ N := by
  classical
  unfold cubeProb
  gcongr
  exact h _

theorem lo_aux_real {N : ℕ} (hN : 1 ≤ N) (y : Fin N → ℝ) (J : Finset (Fin N))
    (hJ : N ≤ 2 * J.card) (hy : ∀ k ∈ J, 1 / 2 ≤ y k ^ 2) (t' r : ℝ) (hr : 0 ≤ r) :
    ((univ.filter (fun x : Fin N → Bool => |∑ k, sgn (x k) * y k + t'| < r)).card : ℝ) /
      2 ^ N ≤ (2 * r + 2) / Real.sqrt N := by
  classical
  set s := Real.sqrt 2 with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsle : s ≤ 2 := by nlinarith
  set a := s / 2 with ha
  have ha0 : 0 < a := by positivity
  have hya : ∀ k ∈ J, a ≤ |y k| := by
    intro k hk
    have h1 := hy k hk
    have h2 : a ^ 2 ≤ |y k| ^ 2 := by
      rw [sq_abs, ha, div_pow, hs2]; linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg _) h2
  have hM1 : 1 ≤ J.card := by omega
  have hMN : J.card ≤ N := by
    have := J.card_le_univ
    rwa [Fintype.card_fin] at this
  have hB : ∀ c : ℝ, (univ.filter (fun x : Fin N → Bool =>
      c ≤ ∑ k, sgn (x k) * y k ∧ ∑ k, sgn (x k) * y k < c + 2 * a)).card ≤
      2 ^ (N - J.card) * J.card.choose (J.card / 2) := by
    intro c
    have := lo_aux_fibre J y a hya c
    rwa [Fintype.card_fin] at this
  have hcov := lo_aux_cover (fun x : Fin N → Bool => ∑ k, sgn (x k) * y k) a ha0 _ hB t' r
  have hmr : (⌈r / a⌉₊ : ℝ) ≤ r / a + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hC := lo_aux_choose_sqrt J.card
  have hE : ((univ.filter (fun x : Fin N → Bool => |∑ k, sgn (x k) * y k + t'| < r)).card : ℝ)
      ≤ (⌈r / a⌉₊ : ℝ) * (2 ^ (N - J.card) * (J.card.choose (J.card / 2) : ℝ)) := by
    exact_mod_cast hcov
  have h2N : (2 : ℝ) ^ N = 2 ^ (N - J.card) * 2 ^ J.card := by
    rw [← pow_add, Nat.sub_add_cancel hMN]
  have hsM : 0 < Real.sqrt J.card := Real.sqrt_pos.mpr (by exact_mod_cast hM1)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hsNM : Real.sqrt N ≤ s * Real.sqrt J.card := by
    rw [hs, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hJ
  have hra : r / a * s = 2 * r := by
    rw [ha]; field_simp
  calc ((univ.filter (fun x : Fin N → Bool => |∑ k, sgn (x k) * y k + t'| < r)).card : ℝ) / 2 ^ N
      ≤ ((⌈r / a⌉₊ : ℝ) * (2 ^ (N - J.card) * (J.card.choose (J.card / 2) : ℝ))) /
          (2 ^ (N - J.card) * 2 ^ J.card) := by
        rw [h2N]; gcongr
    _ = (⌈r / a⌉₊ : ℝ) * (J.card.choose (J.card / 2) : ℝ) / 2 ^ J.card := by
        field_simp
    _ ≤ (2 * r + 2) / Real.sqrt N := by
        rw [div_le_div_iff₀ (by positivity) hsN]
        calc (⌈r / a⌉₊ : ℝ) * (J.card.choose (J.card / 2) : ℝ) * Real.sqrt N
            ≤ (r / a + 1) * (J.card.choose (J.card / 2) : ℝ) * (s * Real.sqrt J.card) := by
              gcongr
          _ = (r / a * s + s) * ((J.card.choose (J.card / 2) : ℝ) * Real.sqrt J.card) := by ring
          _ ≤ (2 * r + 2) * 2 ^ J.card := by
              rw [hra]
              gcongr

end LoAux

theorem lo_bound {N : ℕ} (hN : 1 ≤ N) (θ : ℝ) (t : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    cubeProb N (fun x => ‖∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + t‖ < r) ≤
      (2 * r + 2) / Real.sqrt N := by
  classical
  have hre : ∀ x : Fin N → Bool,
      (∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + t).re =
        ∑ k : Fin N, sgn (x k) * Real.cos (((k : ℕ) : ℝ) * θ) + t.re := by
    intro x
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, ex,
      Complex.exp_ofReal_mul_I_re]
  have him : ∀ x : Fin N → Bool,
      (∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + t).im =
        ∑ k : Fin N, sgn (x k) * Real.sin (((k : ℕ) : ℝ) * θ) + t.im := by
    intro x
    simp only [Complex.add_im, Complex.im_sum, Complex.im_ofReal_mul, ex,
      Complex.exp_ofReal_mul_I_im]
  set J₁ := Finset.univ.filter (fun k : Fin N => 1 / 2 ≤ Real.cos (((k : ℕ) : ℝ) * θ) ^ 2)
    with hJ₁
  set J₂ := Finset.univ.filter (fun k : Fin N => 1 / 2 ≤ Real.sin (((k : ℕ) : ℝ) * θ) ^ 2)
    with hJ₂
  have hunion : J₁ ∪ J₂ = Finset.univ := by
    ext k
    simp only [hJ₁, hJ₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    by_contra hcon
    push Not at hcon
    have := Real.cos_sq_add_sin_sq (((k : ℕ) : ℝ) * θ)
    linarith [hcon.1, hcon.2]
  have hcard : N ≤ J₁.card + J₂.card := by
    calc N = (Finset.univ : Finset (Fin N)).card := by simp
      _ = (J₁ ∪ J₂).card := by rw [hunion]
      _ ≤ J₁.card + J₂.card := Finset.card_union_le _ _
  rcases le_total J₂.card J₁.card with h | h
  · calc cubeProb N (fun x => ‖∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + t‖ < r)
        ≤ ((Finset.univ.filter (fun x : Fin N → Bool =>
            |∑ k, sgn (x k) * Real.cos (((k : ℕ) : ℝ) * θ) + t.re| < r)).card : ℝ) / 2 ^ N := by
          apply lo_aux_mono
          intro x hx
          rw [← hre x]
          exact lt_of_le_of_lt (Complex.abs_re_le_norm _) hx
      _ ≤ (2 * r + 2) / Real.sqrt N :=
          lo_aux_real hN (fun k => Real.cos (((k : ℕ) : ℝ) * θ)) J₁ (by omega)
            (fun k hk => (Finset.mem_filter.mp hk).2) t.re r hr
  · calc cubeProb N (fun x => ‖∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + t‖ < r)
        ≤ ((Finset.univ.filter (fun x : Fin N → Bool =>
            |∑ k, sgn (x k) * Real.sin (((k : ℕ) : ℝ) * θ) + t.im| < r)).card : ℝ) / 2 ^ N := by
          apply lo_aux_mono
          intro x hx
          rw [← him x]
          exact lt_of_le_of_lt (Complex.abs_im_le_norm _) hx
      _ ≤ (2 * r + 2) / Real.sqrt N :=
          lo_aux_real hN (fun k => Real.sin (((k : ℕ) : ℝ) * θ)) J₂ (by omega)
            (fun k hk => (Finset.mem_filter.mp hk).2) t.im r hr

end E522

end

/- ## Section: `LogL2` -/

section

/-
# Deterministic `L²` bound for `log |f_x(e^{iθ})|`

For a nonzero `0/1` polynomial `f = poly x` (so `leadingCoeff f = 1`):
* every nonzero root `α` satisfies `1/2 < |α| < 2`:
  if `|α| ≥ 2`, `|α|^d = |∑_{k<d} c_k α^k| ≤ (|α|^d − 1)/(|α| − 1) < |α|^d`;
  if `0 < |α| ≤ 1/2`, write `f = z^j g`, `g(0) = 1`, then
  `1 = |g(α) − 1|`... is impossible since `|∑_{k≥1} c_k α^k| < |α|/(1−|α|) ≤ 1`.
* `log |f(e^{iθ})| = ∑_{α ∈ roots} log |e^{iθ} − α|` for a.e. `θ` (zero roots contribute `0`).
* For `1/2 ≤ |α| ≤ 2`: `cav(θ ↦ (log|e^{iθ} − α|)²) ≤ C₀²` with an absolute `C₀`
  (`|e^{iθ} − α| ≥ |e^{iθ} − e^{iφ}|/√2`, `|e^{iθ} − e^{iφ}| = 2|sin((θ−φ)/2)| ≥ (2/π)|θ−φ|`,
  `log² v ≤ 16/√v` on `(0,1]`, and `∫ |u|^{-1/2} < ∞`).
* `(∑_{i≤d} u_i)² ≤ d ∑ u_i²` gives `cav((log|f|)²) ≤ d² C₀² ≤ 400 N²`.
-/

/-
## Implementation notes

Only the upper bound `|α| ≤ 2` (Cauchy bound, `l2_aux_root_norm_le`) is used: for every
`0 ≤ ρ ≤ 2` one has `|e^{it} − ρ| ≥ |sin(t/2)|` (`l2_aux_sin_le`), which gives
`(log|e^{it} − ρ|)² ≤ 4 + 16 √π t^{-1/2}` on `(0, π]` (`l2_aux_pt`), hence
`∫_{-π}^{π} (log|e^{it} − ρ|)² ≤ 72π` (`l2_aux_sym`); rotation by `arg α` and `2π`-periodicity
transfer this to `∫_0^{2π} (log|e^{iθ} − α|)² ≤ 72π` (`l2_aux_root`), so
`cav((log|f|)²) ≤ 36 d² ≤ 400 N²`.
-/

open Real Complex

namespace E522

/-- `‖e^{it} − ρ‖² = 1 − 2ρ cos t + ρ²`. -/
theorem l2_aux_norm_sq (ρ t : ℝ) :
    ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 = 1 - 2 * ρ * Real.cos t + ρ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  linear_combination Real.sin_sq_add_cos_sq t

theorem l2_aux_sin_le {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) :
    |Real.sin (t / 2)| ≤ ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ := by
  have h1 : Real.sin (t / 2) ^ 2 = 1 / 2 - Real.cos t / 2 := by
    rw [Real.sin_sq, Real.cos_sq, show 2 * (t / 2) = t by ring]; ring
  have h2 := l2_aux_norm_sq ρ t
  have hc1 := Real.neg_one_le_cos t
  have hc2 := Real.cos_le_one t
  have h3 : Real.sin (t / 2) ^ 2 ≤ ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 := by
    rw [h1, h2]
    rcases le_or_gt (Real.cos t) 0 with hc | hc
    · nlinarith [mul_nonneg hρ (neg_nonneg.mpr hc), sq_nonneg ρ]
    · nlinarith [sq_nonneg (ρ - Real.cos t),
        mul_nonneg (sub_nonneg.mpr hc2) (by linarith : (0:ℝ) ≤ 1 + 2 * Real.cos t)]
  exact (sq_le_sq.mp h3).trans_eq (abs_norm _)

theorem l2_aux_pt {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) {t : ℝ} (ht0 : 0 < t) (htπ : t ≤ π) :
    Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤
      4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)) := by
  set v := ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ with hv
  have hv3 : v ≤ 3 := by
    calc v ≤ ‖Complex.exp ((t : ℂ) * I)‖ + ‖(ρ : ℂ)‖ := norm_sub_le _ _
      _ = 1 + ρ := by rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hρ0]
      _ ≤ 3 := by linarith
  have hvt : t / π ≤ v := by
    have h1 := l2_aux_sin_le hρ0 t
    have h2 : 2 / π * (t / 2) ≤ Real.sin (t / 2) := Real.mul_le_sin (by linarith) (by linarith)
    have h3 : 2 / π * (t / 2) = t / π := by field_simp
    rw [h3] at h2
    exact h2.trans ((le_abs_self _).trans h1)
  have htπpos : 0 < t / π := div_pos ht0 Real.pi_pos
  have hvpos : 0 < v := htπpos.trans_le hvt
  have hsum_nonneg : 0 ≤ 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)) := by positivity
  rcases le_or_gt 1 v with hv1 | hv1
  · have hl0 : 0 ≤ Real.log v := Real.log_nonneg hv1
    have hl2 : Real.log v ≤ 2 := by
      have := Real.log_le_sub_one_of_pos hvpos
      linarith
    nlinarith
  · have hl : -Real.log v ≤ 4 * v ^ (-(1 / 4 : ℝ)) := by
      have := Real.log_le_rpow_div (inv_nonneg.mpr hvpos.le) (by norm_num : (0:ℝ) < 1 / 4)
      rw [Real.log_inv, Real.inv_rpow hvpos.le, ← Real.rpow_neg hvpos.le] at this
      linarith
    have hl0 : 0 ≤ -Real.log v := by
      have := Real.log_neg hvpos hv1
      linarith
    have hpow : (v ^ (-(1 / 4 : ℝ))) ^ 2 = v ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hvpos.le]
      norm_num
    have hsq : Real.log v ^ 2 ≤ 16 * v ^ (-(1 / 2 : ℝ)) := by
      have : (-Real.log v) ^ 2 ≤ (4 * v ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ hl0 hl 2
      rw [neg_sq, mul_pow, hpow] at this
      linarith
    have hmono : v ^ (-(1 / 2 : ℝ)) ≤ (t / π) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos htπpos hvt (by norm_num)
    have heq : (t / π) ^ (-(1 / 2 : ℝ)) = Real.sqrt π * t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.div_rpow ht0.le Real.pi_pos.le, Real.rpow_neg Real.pi_pos.le,
        ← Real.sqrt_eq_rpow]
      field_simp
    rw [heq] at hmono
    nlinarith

theorem l2_aux_meas (ρ : ℝ) :
    Measurable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2) := by
  fun_prop

theorem l2_aux_half {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      MeasureTheory.volume 0 π ∧
    ∫ t in (0:ℝ)..π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤ 36 * π := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) MeasureTheory.volume 0 π :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hg : IntervalIntegrable (fun t : ℝ => 4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 π :=
    intervalIntegrable_const.add (hr.const_mul _)
  have hle : ∀ t ∈ Set.Ioc 0 π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤
      4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)) :=
    fun t ht => l2_aux_pt hρ0 hρ2 ht.1 ht.2
  have hf : IntervalIntegrable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      MeasureTheory.volume 0 π := by
    apply hg.mono_fun' (l2_aux_meas ρ).aestronglyMeasurable
    rw [Set.uIoc_of_le Real.pi_pos.le]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro t ht
    dsimp only
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle t ht
  refine ⟨hf, ?_⟩
  calc ∫ t in (0:ℝ)..π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2
      ≤ ∫ t in (0:ℝ)..π, (4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ))) :=
        intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le hf hg
          (fun t ht => hle t ⟨ht.1, ht.2.le⟩)
    _ = 36 * π := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hr.const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by norm_num)), show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num,
          Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
        have := Real.mul_self_sqrt Real.pi_pos.le
        simp only [smul_eq_mul, sub_zero]
        nlinarith

theorem l2_aux_even (ρ t : ℝ) :
    ‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖ = ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ := by
  have h : ‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖ ^ 2 =
      ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 := by
    rw [l2_aux_norm_sq, l2_aux_norm_sq, Real.cos_neg]
  calc ‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖
      = Real.sqrt (‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2) := by rw [h]
    _ = ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

theorem l2_aux_sym {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      MeasureTheory.volume (-π) π ∧
    ∫ t in (-π)..π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤ 72 * π := by
  obtain ⟨hi, hb⟩ := l2_aux_half hρ0 hρ2
  set G := fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 with hG
  have heven : ∀ t, G (-t) = G t := fun t => by simp only [hG]; rw [l2_aux_even]
  have hi' : IntervalIntegrable G MeasureTheory.volume (-π) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simp only [neg_neg, neg_zero, heven]
    exact hi.symm
  have hint : ∫ t in (-π)..0, G t = ∫ t in (0:ℝ)..π, G t := by
    have := intervalIntegral.integral_comp_neg (a := -π) (b := 0) G
    simp only [heven, neg_zero, neg_neg] at this
    exact this
  refine ⟨hi'.trans hi, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi' hi, hint]
  linarith

theorem l2_aux_periodic (ρ : ℝ) :
    Function.Periodic (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      (2 * π) := by
  intro t
  simp only
  have : Complex.exp (((t + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((t : ℂ) * I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have h2 : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [h2, mul_one]
  rw [this]

theorem l2_aux_rot (α : ℂ) (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - α‖ =
      ‖Complex.exp (((θ - Complex.arg α : ℝ) : ℂ) * I) - ((‖α‖ : ℝ) : ℂ)‖ := by
  have hθ : Complex.exp ((θ : ℂ) * I) = Complex.exp ((Complex.arg α : ℂ) * I) *
      Complex.exp (((θ - Complex.arg α : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have key : Complex.exp ((θ : ℂ) * I) - α = Complex.exp ((Complex.arg α : ℂ) * I) *
      (Complex.exp (((θ - Complex.arg α : ℝ) : ℂ) * I) - ((‖α‖ : ℝ) : ℂ)) := by
    rw [mul_sub, ← hθ]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I α]
    ring
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem l2_aux_root {α : ℂ} (hα : ‖α‖ ≤ 2) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)
      MeasureTheory.volume 0 (2 * π) ∧
    ∫ θ in (0:ℝ)..(2 * π), Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2 ≤ 72 * π := by
  obtain ⟨hi, hb⟩ := l2_aux_sym (norm_nonneg α) hα
  set G := fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - ((‖α‖ : ℝ) : ℂ)‖ ^ 2 with hG
  have hper : Function.Periodic G (2 * π) := l2_aux_periodic ‖α‖
  have hfun : (fun θ : ℝ => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2) =
      fun θ => G (θ - Complex.arg α) := by
    funext θ
    simp only [hG]
    rw [l2_aux_rot]
  rw [hfun]
  have hi2 : IntervalIntegrable G MeasureTheory.volume (-π) (-π + 2 * π) := by
    rw [show -π + 2 * π = π by ring]
    exact hi
  have hall : ∀ a b, IntervalIntegrable G MeasureTheory.volume a b :=
    fun a b => hper.intervalIntegrable (by positivity) hi2 a b
  constructor
  · have := (hall (0 - Complex.arg α) (2 * π - Complex.arg α)).comp_sub_right (Complex.arg α)
    simpa using this
  · rw [intervalIntegral.integral_comp_sub_right]
    have := hper.intervalIntegral_add_eq (0 - Complex.arg α) (-π)
    rw [show 0 - Complex.arg α + 2 * π = 2 * π - Complex.arg α by ring,
      show -π + 2 * π = π by ring] at this
    rw [this]
    exact hb

theorem l2_aux_sq_sum_le (S : Multiset ℂ) (u : ℂ → ℝ) :
    (S.map u).sum ^ 2 ≤ (Multiset.card S : ℝ) * (S.map (fun a => u a ^ 2)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    set s := (S.map u).sum
    set t := (S.map (fun a => u a ^ 2)).sum
    set k := (Multiset.card S : ℝ)
    have ht : 0 ≤ t := Multiset.sum_nonneg (fun y hy => by
      obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hy
      positivity)
    have hk : 0 ≤ k := Nat.cast_nonneg _
    have key : 2 * u a * s ≤ k * u a ^ 2 + t := by
      rcases eq_or_lt_of_le hk with hk0 | hkpos
      · rw [← hk0] at ih
        have : s = 0 := by nlinarith [sq_nonneg s]
        rw [this, ← hk0]
        nlinarith
      · have h1 : 0 ≤ k * (k * u a ^ 2 + t - 2 * u a * s) := by
          nlinarith [sq_nonneg (k * u a - s)]
        have h2 : 0 ≤ k * u a ^ 2 + t - 2 * u a * s := (mul_nonneg_iff_of_pos_left hkpos).mp h1
        linarith
    nlinarith

theorem l2_aux_int_sum (S : Multiset ℂ) (hS : ∀ α ∈ S, ‖α‖ ≤ 2) :
    IntervalIntegrable
      (fun θ : ℝ => (S.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum)
      MeasureTheory.volume 0 (2 * π) ∧
    ∫ θ in (0:ℝ)..(2 * π), (S.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum
      ≤ (Multiset.card S : ℝ) * (72 * π) := by
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero]
    exact ⟨intervalIntegrable_const, by simp⟩
  | cons a S ih =>
    have ha := l2_aux_root (hS a (Multiset.mem_cons_self a S))
    have ih' := ih (fun α hα => hS α (Multiset.mem_cons_of_mem hα))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    refine ⟨ha.1.add ih'.1, ?_⟩
    rw [intervalIntegral.integral_add ha.1 ih'.1]
    push_cast
    linarith [ha.2, ih'.2]

/-- Explicit coefficients of `poly x`. -/
theorem l2_aux_coeff {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (poly x).coeff m = if h : m < N then ((bit (x ⟨m, h⟩) : ℝ) : ℂ) else 0 := by
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (Fin.ext hbm)
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbm
    exact h (hbm ▸ b.2)

theorem l2_aux_coeff_mem {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (poly x).coeff m = 0 ∨ (poly x).coeff m = 1 := by
  rw [l2_aux_coeff]
  split_ifs with h
  · cases x ⟨m, h⟩ <;> simp [bit]
  · simp

theorem l2_aux_leadingCoeff {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    (poly x).leadingCoeff = 1 := by
  rcases l2_aux_coeff_mem x (poly x).natDegree with h | h
  · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr hx)
  · exact h

theorem l2_aux_natDegree_le {N : ℕ} (x : Fin N → Bool) : (poly x).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [l2_aux_coeff, dif_neg]
  intro h
  exact absurd (lt_trans h hm) (lt_irrefl _)

/-- Every root of a nonzero `0/1` polynomial has modulus `< 2` (Cauchy bound). -/
theorem l2_aux_root_norm_le {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) (α : ℂ)
    (hα : α ∈ (poly x).roots) : ‖α‖ ≤ 2 := by
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hx ((Polynomial.mem_roots hx).mp hα)
  have h2 : Polynomial.cauchyBound (poly x) ≤ 2 := by
    unfold Polynomial.cauchyBound
    rw [l2_aux_leadingCoeff x hx, nnnorm_one, div_one]
    have : (Finset.range (poly x).natDegree).sup (fun i => ‖(poly x).coeff i‖₊) ≤ 1 := by
      apply Finset.sup_le
      intro i _
      rcases l2_aux_coeff_mem x i with h | h <;> simp [h]
    calc _ ≤ (1 : NNReal) + 1 := by gcongr
      _ = 2 := by norm_num
  have h3 : ‖α‖₊ < 2 := lt_of_lt_of_le h1 h2
  have h4 : ‖α‖ < 2 := by
    rw [← coe_nnnorm]
    exact_mod_cast h3
  exact h4.le

theorem l2_aux_log_norm_prod (S : Multiset ℂ) (z : ℂ) (hz : (S.map (z - ·)).prod ≠ 0) :
    Real.log ‖(S.map (z - ·)).prod‖ = (S.map (fun α => Real.log ‖z - α‖)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons] at hz ⊢
    have h1 : z - a ≠ 0 := left_ne_zero_of_mul hz
    have h2 : (S.map (z - ·)).prod ≠ 0 := right_ne_zero_of_mul hz
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2), ih h2]

theorem l2_aux_log_eval {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) (z : ℂ)
    (hz : (poly x).eval z ≠ 0) :
    Real.log ‖(poly x).eval z‖ = ((poly x).roots.map (fun α => Real.log ‖z - α‖)).sum := by
  have h := (IsAlgClosed.splits (poly x)).eval_eq_prod_roots z
  rw [l2_aux_leadingCoeff x hx, one_mul] at h
  rw [h] at hz ⊢
  exact l2_aux_log_norm_prod _ z hz

theorem l2_aux_ae_ne_zero {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    ∀ᵐ θ : ℝ ∂MeasureTheory.volume, (poly x).eval (Complex.exp ((θ : ℂ) * I)) ≠ 0 := by
  have hc : (circleMap 0 1 ⁻¹' {z | (poly x).IsRoot z}).Countable := by
    apply Set.Countable.preimage_circleMap _ 0 one_ne_zero
    exact ((poly x).roots.finite_toSet.subset
      (fun z hz => (Polynomial.mem_roots hx).mpr hz)).countable
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (hc.measure_zero _)
  intro θ hθ
  simpa [circleMap] using hθ

theorem l2_aux_pointwise {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    ∀ᵐ θ : ℝ ∂MeasureTheory.volume, Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2 ≤
      (Multiset.card (poly x).roots : ℝ) *
        ((poly x).roots.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum := by
  filter_upwards [l2_aux_ae_ne_zero x hx] with θ hθ
  rw [l2_aux_log_eval x hx _ hθ]
  exact l2_aux_sq_sum_le _ _

theorem l2_aux_meas_poly {N : ℕ} (x : Fin N → Bool) :
    Measurable (fun θ : ℝ => Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2) := by
  have : Continuous (fun θ : ℝ => ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖) := by
    fun_prop
  exact (Real.measurable_log.comp this.measurable).pow_const 2

/-- Integrability of `θ ↦ (log |f(e^{iθ})|)²` (dominated by `d · ∑_α (log|e^{iθ} − α|)²`). -/
theorem l2_aux_log_sq_intervalIntegrable {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    IntervalIntegrable (fun θ => Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2)
      MeasureTheory.volume 0 (2 * π) := by
  have hS := l2_aux_int_sum (poly x).roots (fun α hα => l2_aux_root_norm_le x hx α hα)
  apply (hS.1.const_mul (Multiset.card (poly x).roots : ℝ)).mono_fun'
  · exact (l2_aux_meas_poly x).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [l2_aux_pointwise x hx] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hθ

theorem log_sq_bound {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    cav (fun θ => Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2) ≤ 400 * N ^ 2 := by
  have hS := l2_aux_int_sum (poly x).roots (fun α hα => l2_aux_root_norm_le x hx α hα)
  have hcard : (Multiset.card (poly x).roots : ℝ) ≤ N := by
    have h1 := Polynomial.card_roots' (poly x)
    have h2 : (poly x).natDegree ≤ N := l2_aux_natDegree_le x
    exact_mod_cast h1.trans h2
  set d := (Multiset.card (poly x).roots : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hint := l2_aux_log_sq_intervalIntegrable x hx
  have hmono : ∫ θ in (0:ℝ)..(2 * π), Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2
      ≤ ∫ θ in (0:ℝ)..(2 * π), d *
        ((poly x).roots.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum :=
    intervalIntegral.integral_mono_ae (by positivity) hint (hS.1.const_mul d)
      (l2_aux_pointwise x hx)
  rw [intervalIntegral.integral_const_mul] at hmono
  have h2 := mul_le_mul_of_nonneg_left hS.2 hd0
  have hπ : 0 < π := Real.pi_pos
  unfold cav
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2
      ≤ (2 * π)⁻¹ * (d * (d * (72 * π))) :=
        mul_le_mul_of_nonneg_left (hmono.trans h2) (by positivity)
    _ = 36 * d ^ 2 := by field_simp; ring
    _ ≤ 36 * N ^ 2 := by gcongr
    _ ≤ 400 * N ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]

/-- Elementary Cauchy–Schwarz from the quadratic bound `2λI ≤ λ²A + B` for all `λ > 0`. -/
theorem l2_aux_cs_real (A B I : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ l : ℝ, 0 < l → 2 * l * I ≤ l ^ 2 * A + B) : I ≤ Real.sqrt A * Real.sqrt B := by
  rcases le_or_gt I 0 with hI | hI
  · exact hI.trans (by positivity)
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · exfalso
    have := h (B / I + 1) (by positivity)
    rw [← hA0] at this
    have e : 2 * (B / I + 1) * I = 2 * B + 2 * I := by field_simp
    rw [e] at this
    linarith
  · have := h (I / A) (by positivity)
    have e1 : 2 * (I / A) * I = 2 * (I ^ 2 / A) := by ring
    have e2 : (I / A) ^ 2 * A = I ^ 2 / A := by field_simp
    rw [e1, e2] at this
    have h3 : I ^ 2 / A ≤ B := by linarith
    have h4 : I ^ 2 ≤ A * B := by
      rw [div_le_iff₀ hApos] at h3
      linarith
    rw [← Real.sqrt_mul hA]
    calc I = Real.sqrt (I ^ 2) := (Real.sqrt_sq hI.le).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt h4

/-- Cauchy–Schwarz for `cav`. -/
theorem cav_mul_le_sqrt {F G : ℝ → ℝ} (hF : IntervalIntegrable (fun θ => F θ ^ 2) MeasureTheory.volume 0 (2 * π))
    (hG : IntervalIntegrable (fun θ => G θ ^ 2) MeasureTheory.volume 0 (2 * π)) :
    cav (fun θ => |F θ * G θ|) ≤ Real.sqrt (cav (fun θ => F θ ^ 2)) * Real.sqrt (cav (fun θ => G θ ^ 2)) := by
  have h2π : 0 < 2 * π := by positivity
  have hA : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), F θ ^ 2 :=
    intervalIntegral.integral_nonneg h2π.le (fun θ _ => sq_nonneg _)
  have hB : 0 ≤ ∫ θ in (0:ℝ)..(2 * π), G θ ^ 2 :=
    intervalIntegral.integral_nonneg h2π.le (fun θ _ => sq_nonneg _)
  have key : ∫ θ in (0:ℝ)..(2 * π), |F θ * G θ| ≤
      Real.sqrt (∫ θ in (0:ℝ)..(2 * π), F θ ^ 2) * Real.sqrt (∫ θ in (0:ℝ)..(2 * π), G θ ^ 2) := by
    by_cases hI : IntervalIntegrable (fun θ => |F θ * G θ|) MeasureTheory.volume 0 (2 * π)
    · apply l2_aux_cs_real _ _ _ hA hB
      intro l hl
      have hm : ∫ θ in (0:ℝ)..(2 * π), 2 * l * |F θ * G θ| ≤
          ∫ θ in (0:ℝ)..(2 * π), (l ^ 2 * F θ ^ 2 + G θ ^ 2) := by
        apply intervalIntegral.integral_mono_on h2π.le (hI.const_mul _) ((hF.const_mul _).add hG)
        intro θ _
        rw [abs_mul]
        nlinarith [sq_nonneg (l * |F θ| - |G θ|), sq_abs (F θ), sq_abs (G θ)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hF.const_mul _) hG,
        intervalIntegral.integral_const_mul] at hm
      exact hm
    · rw [intervalIntegral.integral_undef hI]
      positivity
  unfold cav
  have hinv : 0 ≤ (2 * π)⁻¹ := inv_nonneg.mpr h2π.le
  rw [Real.sqrt_mul hinv, Real.sqrt_mul hinv]
  have hs : Real.sqrt ((2 * π)⁻¹) * Real.sqrt ((2 * π)⁻¹) = (2 * π)⁻¹ := Real.mul_self_sqrt hinv
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π), |F θ * G θ|
      ≤ (2 * π)⁻¹ * (Real.sqrt (∫ θ in (0:ℝ)..(2 * π), F θ ^ 2) *
          Real.sqrt (∫ θ in (0:ℝ)..(2 * π), G θ ^ 2)) := mul_le_mul_of_nonneg_left key hinv
    _ = _ := by rw [mul_mul_mul_comm, hs]

/-- The function `θ ↦ (log |f_x(e^{iθ})|)²` is interval integrable (for `poly x ≠ 0`). -/
theorem log_sq_intervalIntegrable {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    IntervalIntegrable (fun θ => Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2)
      MeasureTheory.volume 0 (2 * π) :=
  l2_aux_log_sq_intervalIntegrable x hx

end E522

end

/- ## Section: `Jensen` -/

section

/-
# Jensen's formula for `0/1` polynomials, secant root counting, and normalisation

* `jensen_poly`: `circleAverage (log |f|) 0 (e^s) = ∑_{α ∈ roots f} log max(e^s, |α|)`
  (factor `f = ∏ (X − α)` using `leadingCoeff f = 1` and algebraic closedness; each factor via
  `circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`; a.e. equality off the finitely
  many roots on the circle; or `circleAverage_log_norm_factorizedRational`).
* `det_main` (deterministic main lemma): with `A(s) = ½ log σ²(s)`, `B(s) = A(s) − ns/2` is even
  and `0 ≤ B(s) − B(0) ≤ ½ log cosh(ns) ≤ n²s²/4` (pair `k ↔ n−k`; `Real.cosh_le_exp_half_sq`).
  Secants of `s ↦ log max(e^s, |α|)`:
  `g(h) − g(0) ≥ h·1[|α| ≤ 1]`, `g(0) − g(−h) ≤ h·1[|α| ≤ 1]`, hence
  `(L(0) − L(−h))/h ≤ R ≤ (L(h) − L(0))/h` for `L = circleAverage(log|f|)`.
* `lam_eq_cav`: `Z_x(s,θ) = 2 f_x(e^{s+iθ})/σ_N(s)` (`sgn_add_one`), so
  `Λ_x(s) = cav(log |Z_x(s,·)|) − log 2` (a.e. equality off the zeros).
-/

open Real Complex

namespace E522

theorem poly_eval {N : ℕ} (x : Fin N → Bool) (z : ℂ) :
    (poly x).eval z = ∑ k : Fin N, ((bit (x k) : ℝ) : ℂ) * z ^ (k : ℕ) := by
  simp [poly, Polynomial.eval_finsetSum]

/-- Explicit coefficients of `poly x`. -/
theorem jen_aux_coeff {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (poly x).coeff m = if h : m < N then ((bit (x ⟨m, h⟩) : ℝ) : ℂ) else 0 := by
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (Fin.ext hbm)
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbm
    exact h (hbm ▸ b.2)

/-- Every coefficient of `poly x` is `0` or `1`. -/
theorem jen_aux_coeff_mem {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (poly x).coeff m = 0 ∨ (poly x).coeff m = 1 := by
  rw [jen_aux_coeff]
  split_ifs with h
  · cases x ⟨m, h⟩ <;> simp [bit]
  · simp

theorem poly_ne_zero_of {N : ℕ} (x : Fin N → Bool) (k : Fin N) (hk : x k = true) : poly x ≠ 0 := by
  intro h0
  have := jen_aux_coeff x k
  rw [h0, dif_pos k.2] at this
  simp [bit, hk] at this

theorem poly_leadingCoeff {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    (poly x).leadingCoeff = 1 := by
  rcases jen_aux_coeff_mem x (poly x).natDegree with h | h
  · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr hx)
  · exact h

/-- `log` of the norm of a product of linear factors is the sum of the logs. -/
theorem jen_aux_log_norm_prod (S : Multiset ℂ) (z : ℂ) (hz : (S.map (z - ·)).prod ≠ 0) :
    Real.log ‖(S.map (z - ·)).prod‖ = (S.map (fun α => Real.log ‖z - α‖)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons] at hz ⊢
    have h1 : z - a ≠ 0 := left_ne_zero_of_mul hz
    have h2 : (S.map (z - ·)).prod ≠ 0 := right_ne_zero_of_mul hz
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2), ih h2]

/-- Off the zeros, `log |f(z)| = ∑_{α ∈ roots} log |z − α|`. -/
theorem jen_aux_log_eval {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) (z : ℂ)
    (hz : (poly x).eval z ≠ 0) :
    Real.log ‖(poly x).eval z‖ = ((poly x).roots.map (fun α => Real.log ‖z - α‖)).sum := by
  have h := (IsAlgClosed.splits (poly x)).eval_eq_prod_roots z
  rw [poly_leadingCoeff x hx, one_mul] at h
  rw [h] at hz ⊢
  exact jen_aux_log_norm_prod _ z hz

/-- Circle averages commute with the finite (multiset) sum of `log |· − α|`. -/
theorem jen_aux_circleAverage_sum (S : Multiset ℂ) (R : ℝ) :
    CircleIntegrable (fun z => (S.map (fun α => Real.log ‖z - α‖)).sum) 0 R ∧
    Real.circleAverage (fun z => (S.map (fun α => Real.log ‖z - α‖)).sum) 0 R =
      (S.map (fun α => Real.circleAverage (fun z => Real.log ‖z - α‖) 0 R)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [Real.circleAverage_const]
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have ha : CircleIntegrable (fun z => Real.log ‖z - a‖) 0 R :=
      circleIntegrable_log_norm_sub_const R
    refine ⟨ha.fun_add ih.1, ?_⟩
    rw [Real.circleAverage_fun_add ha ih.1, ih.2]

/-- `f` does not vanish at almost every point of a circle of nonzero radius. -/
theorem jen_aux_ae_ne_zero {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) {R : ℝ} (hR : R ≠ 0) :
    ∀ᵐ θ ∂MeasureTheory.volume, (poly x).eval (circleMap 0 R θ) ≠ 0 := by
  have hc : (circleMap 0 R ⁻¹' {z | (poly x).IsRoot z}).Countable := by
    apply Set.Countable.preimage_circleMap _ 0 hR
    exact ((poly x).roots.finite_toSet.subset
      (fun z hz => (Polynomial.mem_roots hx).mpr hz)).countable
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (hc.measure_zero _)
  intro θ hθ
  simpa using hθ

theorem jensen_poly {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) (s : ℝ) :
    Real.circleAverage (fun z => Real.log ‖(poly x).eval z‖) 0 (Real.exp s) =
      ((poly x).roots.map (fun α => Real.log (max (Real.exp s) ‖α‖))).sum := by
  have hR : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have h1 : Real.circleAverage (fun z => Real.log ‖(poly x).eval z‖) 0 (Real.exp s) =
      Real.circleAverage (fun z => ((poly x).roots.map (fun α => Real.log ‖z - α‖)).sum) 0
        (Real.exp s) := by
    unfold Real.circleAverage
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [jen_aux_ae_ne_zero x hx hR] with θ hθ _
    exact jen_aux_log_eval x hx _ hθ
  rw [h1, (jen_aux_circleAverage_sum _ _).2]
  congr 1
  apply Multiset.map_congr rfl
  intro α _
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR, zero_sub, norm_neg,
    Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hR (by positivity),
    mul_max_of_nonneg _ _ (Real.exp_pos s).le, mul_one, mul_inv_cancel_left₀ hR]

/-- Secant bounds for `s ↦ ∑_α log max(e^s, |α|)` at `s = h, 0, -h`. -/
theorem jen_aux_secant (S : Multiset ℂ) {h : ℝ} (hh : 0 < h)
    [DecidablePred (· ∈ Metric.closedBall (0 : ℂ) 1)] :
    h * (S.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) ≤
      (S.map (fun α => Real.log (max (Real.exp h) ‖α‖))).sum -
        (S.map (fun α => Real.log (max (Real.exp 0) ‖α‖))).sum ∧
    (S.map (fun α => Real.log (max (Real.exp 0) ‖α‖))).sum -
        (S.map (fun α => Real.log (max (Real.exp (-h)) ‖α‖))).sum ≤
      h * (S.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons]
    push_cast
    by_cases ha : a ∈ Metric.closedBall (0 : ℂ) 1
    · rw [if_pos ha]
      have ha' : ‖a‖ ≤ 1 := by simpa using ha
      have e1 : Real.log (max (Real.exp h) ‖a‖) = h := by
        rw [max_eq_left (by linarith [Real.add_one_le_exp h] : ‖a‖ ≤ Real.exp h), Real.log_exp]
      have e2 : Real.log (max (Real.exp 0) ‖a‖) = 0 := by
        rw [Real.exp_zero, max_eq_left ha', Real.log_one]
      have e3 : -h ≤ Real.log (max (Real.exp (-h)) ‖a‖) := by
        have := Real.log_le_log (Real.exp_pos (-h)) (le_max_left (Real.exp (-h)) ‖a‖)
        rwa [Real.log_exp] at this
      constructor <;> linarith [ih.1, ih.2]
    · rw [if_neg ha]
      have ha' : 1 < ‖a‖ := by simpa using ha
      have e2 : Real.log (max (Real.exp 0) ‖a‖) = Real.log ‖a‖ := by
        rw [Real.exp_zero, max_eq_right ha'.le]
      have e1 : Real.log ‖a‖ ≤ Real.log (max (Real.exp h) ‖a‖) :=
        Real.log_le_log (by linarith) (le_max_right _ _)
      have e3 : Real.log (max (Real.exp (-h)) ‖a‖) = Real.log ‖a‖ := by
        rw [max_eq_right]
        have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith
      constructor <;> linarith [ih.1, ih.2]

/-- `σ²_{n+1}(s) ≤ (n+1) e^{ns + n²s²/2}` (pair `k ↔ n − k` and use `cosh u ≤ e^{u²/2}`). -/
theorem jen_aux_sig2_le (n : ℕ) (s : ℝ) :
    sig2 (n + 1) s ≤ (n + 1) * Real.exp (n * s + n ^ 2 * s ^ 2 / 2) := by
  have hsplit : sig2 (n + 1) s =
      Real.exp (n * s) * ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) := by
    rw [sig2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Real.exp_add]
    ring_nf
  have hrefl : ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) =
      ∑ k ∈ Finset.range (n + 1), Real.exp (-((2 * k - n) * s)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    congr 1
    rw [show n + 1 - 1 - k = n - k by omega, Nat.cast_sub hk']
    ring
  have hcosh : ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) =
      ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s) := by
    have : 2 * ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) =
        2 * ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s) := by
      rw [two_mul]
      nth_rewrite 2 [hrefl]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.cosh_eq]; ring
    linarith
  have hbound : ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s) ≤
      (n + 1) * Real.exp (n ^ 2 * s ^ 2 / 2) := by
    calc ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s)
        ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (n ^ 2 * s ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          refine (Real.cosh_le_exp_half_sq _).trans (Real.exp_le_exp.mpr ?_)
          have : ((2 * k - n) * s) ^ 2 ≤ n ^ 2 * s ^ 2 := by
            rw [mul_pow]
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
            nlinarith
          linarith
      _ = (n + 1) * Real.exp (n ^ 2 * s ^ 2 / 2) := by simp
  rw [hsplit, hcosh, Real.exp_add]
  calc Real.exp (n * s) * ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s)
      ≤ Real.exp (n * s) * ((n + 1) * Real.exp (n ^ 2 * s ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (n + 1) * (Real.exp (n * s) * Real.exp (n ^ 2 * s ^ 2 / 2)) := by ring

theorem jen_aux_sig2_pos {N : ℕ} (hN : 1 ≤ N) (s : ℝ) : 0 < sig2 N s := by
  rw [sig2]
  exact Finset.sum_pos (fun k _ => Real.exp_pos _) (Finset.nonempty_range_iff.mpr (by omega))

theorem jen_aux_sig2_zero (N : ℕ) : sig2 N 0 = N := by simp [sig2]

/-- `A(s) − A(0) ≤ ns/2 + n²s²/4` for `A(s) = ½ log σ²_{n+1}(s)`. -/
theorem jen_aux_A_le (n : ℕ) (s : ℝ) :
    Real.log (sig2 (n + 1) s) / 2 - Real.log (sig2 (n + 1) 0) / 2 ≤
      n * s / 2 + n ^ 2 * s ^ 2 / 4 := by
  have h2 : Real.log (sig2 (n + 1) s) ≤
      Real.log ((n + 1) * Real.exp (n * s + n ^ 2 * s ^ 2 / 2)) :=
    Real.log_le_log (jen_aux_sig2_pos (by omega) s) (jen_aux_sig2_le n s)
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [jen_aux_sig2_zero]
  push_cast
  linarith

/-- Deterministic main lemma. -/
theorem det_main {n : ℕ} (x : Fin (n + 1) → Bool) (hx : poly x ≠ 0) (h κ E : ℝ) (hh : 0 < h)
    (hup : Lam x h ≤ κ + E) (hdn : Lam x (-h) ≤ κ + E) (hlo : κ - E ≤ Lam x 0) :
    |(rootCount x : ℝ) - n / 2| ≤ n ^ 2 * h / 4 + 2 * E / h := by
  classical
  have hL : ∀ s, Lam x s = ((poly x).roots.map (fun α => Real.log (max (Real.exp s) ‖α‖))).sum -
      Real.log (sig2 (n + 1) s) / 2 := by
    intro s
    rw [Lam, jensen_poly x hx s]
  obtain ⟨hs1, hs2⟩ := jen_aux_secant (poly x).roots hh
  have hA1 := jen_aux_A_le n h
  have hA2 := jen_aux_A_le n (-h)
  rw [hL] at hup hdn hlo
  have hR : (rootCount x : ℝ) =
      ((poly x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) := by
    rfl
  rw [hR]
  have hB : h * (n ^ 2 * h / 4 + 2 * E / h) = n ^ 2 * h ^ 2 / 4 + 2 * E := by
    field_simp
  rw [abs_le]
  constructor
  · have : h * (-(n ^ 2 * h / 4 + 2 * E / h)) ≤
        h * (((poly x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) - n / 2) := by
      rw [mul_neg, hB]
      nlinarith
    exact le_of_mul_le_mul_left this hh
  · have : h * (((poly x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) - n / 2) ≤
        h * (n ^ 2 * h / 4 + 2 * E / h) := by
      rw [hB]
      nlinarith
    exact le_of_mul_le_mul_left this hh

/-- `Z_x(s, θ) = (2/σ_N(s)) · f_x(e^s e^{iθ})`. -/
theorem jen_aux_Zfun_eq {N : ℕ} (x : Fin N → Bool) (s θ : ℝ) :
    Zfun x s θ = ((2 / Real.sqrt (sig2 N s) : ℝ) : ℂ) *
      (poly x).eval (circleMap 0 (Real.exp s) θ) := by
  rw [poly_eval, Finset.mul_sum, Zfun, Wfun, mfun, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hb : sgn (x k) = 2 * bit (x k) - 1 := by linarith [sgn_add_one (x k)]
  simp only [rho, ex, circleMap, zero_add, hb]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem jen_aux_circleIntegrable {N : ℕ} (x : Fin N → Bool) (R : ℝ) :
    CircleIntegrable (fun z => Real.log ‖(poly x).eval z‖) 0 R :=
  (analyticOnNhd_id.aeval_polynomial (poly x)).meromorphicOn.circleIntegrable_log_norm

theorem lam_eq_cav {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (hx : poly x ≠ 0) (s : ℝ) :
    Lam x s = cav (fun θ => Real.log ‖Zfun x s θ‖) - Real.log 2 := by
  have hsig : 0 < sig2 N s := jen_aux_sig2_pos hN s
  have hR : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have hc : (0:ℝ) < 2 / Real.sqrt (sig2 N s) := by positivity
  have hae : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc 0 (2 * π) →
      Real.log ‖Zfun x s θ‖ = (Real.log 2 - Real.log (sig2 N s) / 2) +
        Real.log ‖(poly x).eval (circleMap 0 (Real.exp s) θ)‖ := by
    filter_upwards [jen_aux_ae_ne_zero x hx hR] with θ hθ _
    rw [jen_aux_Zfun_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le,
      Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hθ),
      Real.log_div two_ne_zero (Real.sqrt_pos.mpr hsig).ne', Real.log_sqrt hsig.le]
  have hint : IntervalIntegrable
      (fun θ => Real.log ‖(poly x).eval (circleMap 0 (Real.exp s) θ)‖)
      MeasureTheory.volume 0 (2 * π) := jen_aux_circleIntegrable x _
  rw [cav, intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const,
    Lam, Real.circleAverage_def, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- The zeros of `Z_x(s, ·)` on `[0, 2π]` form a null set (finitely many). -/
theorem Zfun_ne_zero_ae {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (hx : poly x ≠ 0) (s : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.uIoc 0 (2 * π))), Zfun x s θ ≠ 0 := by
  have hsig : 0 < sig2 N s := jen_aux_sig2_pos hN s
  have hc : (0:ℝ) < 2 / Real.sqrt (sig2 N s) := by positivity
  apply MeasureTheory.ae_restrict_of_ae
  filter_upwards [jen_aux_ae_ne_zero x hx (Real.exp_pos s).ne'] with θ hθ
  rw [jen_aux_Zfun_eq]
  exact mul_ne_zero (by exact_mod_cast hc.ne') hθ

/-- At radius `1` the normalised polynomial is `Z = 2 f / √N`. -/
theorem Zfun_zero_eq {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (θ : ℝ) :
    Zfun x 0 θ = (2 / Real.sqrt N : ℝ) * (poly x).eval (Complex.exp ((θ : ℂ) * I)) := by
  -- `hN` is not needed: for `N = 0` both sides vanish.
  have _ := hN
  rw [jen_aux_Zfun_eq, jen_aux_sig2_zero, Real.exp_zero]
  congr 2
  simp [circleMap]

end E522

end

/- ## Section: `Profile` -/

section

/-
# The radial profile `ρ_k(s) = e^{ks}/σ_N(s)` near the unit circle

Here `N = n + 1` and `|s| ≤ 1/(2n)`, so `e^{2k|s|} ≤ e` for `k ≤ n` and `σ² ≥ N/e`.
Geometric sums: `|∑_{j<J} w^j| = |1 − w^J|/|1 − w|` and
`|1 − r e^{iφ}| ≥ 2 √r |sin(φ/2)|`.
Parseval for trigonometric polynomials: `∫_0^{2π} e^{i(j−k)θ} dθ = 2π δ_{jk}`.
-/

open Real Complex

namespace E522

theorem sig2_pos {N : ℕ} (hN : 1 ≤ N) (s : ℝ) : 0 < sig2 N s := by
  unfold sig2
  apply Finset.sum_pos (fun k _ => Real.exp_pos _)
  exact Finset.nonempty_range_iff.mpr (by omega)

theorem sig2_zero (N : ℕ) : sig2 N 0 = N := by
  simp [sig2]

theorem rho_nonneg (N : ℕ) (s : ℝ) (k : ℕ) : 0 ≤ rho N s k := by
  unfold rho
  positivity

theorem rho_zero {N : ℕ} (k : ℕ) : rho N 0 k = 1 / Real.sqrt N := by
  rw [rho, sig2_zero, mul_zero, Real.exp_zero]

lemma profile_aux_rho_sq {N : ℕ} (hN : 1 ≤ N) (s : ℝ) (k : ℕ) :
    rho N s k ^ 2 = Real.exp (2 * k * s) / sig2 N s := by
  rw [rho, div_pow, Real.sq_sqrt (sig2_pos hN s).le, sq, ← Real.exp_add]
  congr 2
  ring

theorem sum_rho_sq {N : ℕ} (hN : 1 ≤ N) (s : ℝ) : ∑ k ∈ Finset.range N, rho N s k ^ 2 = 1 := by
  rw [Finset.sum_congr rfl (fun k _ => profile_aux_rho_sq hN s k), ← Finset.sum_div]
  exact div_self (sig2_pos hN s).ne'

/-- For `j, k ≤ n` and `|s| ≤ 1/(2n)`: `2ks - 2js ≤ 1`. -/
lemma profile_aux_ks {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {j k : ℕ}
    (hj : j ≤ n) (hk : k ≤ n) : 2 * (k : ℝ) * s - 2 * j * s ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ n := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hsn : |s| * n ≤ 1 / 2 := by
    calc |s| * n ≤ 1 / (2 * n) * n := by gcongr
      _ = 1 / 2 := by field_simp
  have h : ((k : ℝ) - j) * s ≤ |s| * n := by
    calc ((k : ℝ) - j) * s ≤ |((k : ℝ) - j) * s| := le_abs_self _
      _ = |(k : ℝ) - j| * |s| := abs_mul _ _
      _ ≤ n * |s| := by
          gcongr
          rw [abs_le]
          constructor <;> linarith
      _ = |s| * n := mul_comm _ _
  linarith

/-- `e^{2ks} ≤ e · e^{2js}` for `j, k ≤ n`. -/
lemma profile_aux_exp_le {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {j k : ℕ}
    (hj : j ≤ n) (hk : k ≤ n) :
    Real.exp (2 * k * s) ≤ Real.exp 1 * Real.exp (2 * j * s) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have := profile_aux_ks hn hs hj hk
  linarith

/-- `(n+1) e^{2ks} ≤ e · σ²` for `k ≤ n`. -/
lemma profile_aux_sig2_ge {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {k : ℕ}
    (hk : k ≤ n) :
    ((n : ℝ) + 1) * Real.exp (2 * k * s) ≤ Real.exp 1 * sig2 (n + 1) s := by
  unfold sig2
  rw [Finset.mul_sum]
  calc ((n : ℝ) + 1) * Real.exp (2 * k * s)
      = ∑ j ∈ Finset.range (n + 1), Real.exp (2 * k * s) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ ∑ j ∈ Finset.range (n + 1), Real.exp 1 * Real.exp (2 * j * s) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_range] at hj
        exact profile_aux_exp_le hn hs (by omega) hk

lemma profile_aux_e_lt : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9

theorem rho_le {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {k : ℕ} (hk : k < n + 1) :
    rho (n + 1) s k ≤ 2 / Real.sqrt (n + 1) := by
  have hσ := sig2_pos (N := n + 1) (by omega) s
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkey := profile_aux_sig2_ge hn hs (k := k) (by omega)
  have he := profile_aux_e_lt
  have hsq : rho (n + 1) s k ^ 2 ≤ (2 / Real.sqrt (n + 1)) ^ 2 := by
    rw [profile_aux_rho_sq (by omega), div_pow, Real.sq_sqrt hn1.le, div_le_div_iff₀ hσ hn1]
    have hexp : 0 < Real.exp (2 * k * s) := Real.exp_pos _
    nlinarith
  rwa [sq_le_sq₀ (rho_nonneg _ _ _) (by positivity)] at hsq

/- ### Geometric sums -/

lemma profile_aux_geom_norm (w : ℂ) (J : ℕ) (c : ℝ) (hc : 0 < c) (hw : c ≤ ‖w - 1‖) :
    ‖∑ j ∈ Finset.range J, w ^ j‖ ≤ (‖w‖ ^ J + 1) / c := by
  have h := geom_sum_mul w J
  have h1 : ‖∑ j ∈ Finset.range J, w ^ j‖ * ‖w - 1‖ = ‖w ^ J - 1‖ := by
    rw [← norm_mul, h]
  have h2 : ‖w ^ J - 1‖ ≤ ‖w‖ ^ J + 1 := by
    calc ‖w ^ J - 1‖ ≤ ‖w ^ J‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = ‖w‖ ^ J + 1 := by rw [norm_pow, norm_one]
  rw [le_div_iff₀ hc]
  calc ‖∑ j ∈ Finset.range J, w ^ j‖ * c ≤ ‖∑ j ∈ Finset.range J, w ^ j‖ * ‖w - 1‖ := by
        gcongr
    _ = ‖w ^ J - 1‖ := h1
    _ ≤ ‖w‖ ^ J + 1 := h2

lemma profile_aux_norm_sq_sub_one (a φ : ℝ) :
    ‖Complex.exp ((a : ℂ) + (φ : ℂ) * I) - 1‖ ^ 2 =
      (Real.exp a - 1) ^ 2 + 4 * Real.exp a * Real.sin (φ / 2) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.exp_re,
    Complex.exp_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hcos : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ 2 := by
    have h1 := Real.cos_two_mul (φ / 2)
    have h2 := Real.sin_sq_add_cos_sq (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h1
    linarith
  have hsc := Real.sin_sq_add_cos_sq φ
  simp only [mul_zero, sub_zero, mul_one, add_zero, zero_add]
  linear_combination (Real.exp a) ^ 2 * hsc - 2 * Real.exp a * hcos

/-- Partial sums of `ρ_j² e^{-2ijθ}`. -/
theorem P_bound {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) (θ : ℝ)
    (hθ : Real.sin θ ≠ 0) {J : ℕ} (hJ : J ≤ n + 1) :
    ‖∑ j ∈ Finset.range J,
        ((rho (n + 1) s j ^ 2 : ℝ) : ℂ) * Complex.exp (((-(2 * (j : ℝ) * θ)) : ℝ) * I)‖ ≤
      20 / ((n + 1) * |Real.sin θ|) := by
  have hσ := sig2_pos (N := n + 1) (by omega) s
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsinpos : 0 < |Real.sin θ| := abs_pos.mpr hθ
  rcases Nat.eq_zero_or_pos J with hJ0 | hJ0
  · subst hJ0
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  have hterm : ∀ j : ℕ, ((rho (n + 1) s j ^ 2 : ℝ) : ℂ) *
      Complex.exp (((-(2 * (j : ℝ) * θ)) : ℝ) * I) =
      (((sig2 (n + 1) s)⁻¹ : ℝ) : ℂ) *
        Complex.exp (((2 * s : ℝ) : ℂ) + ((-(2 * θ) : ℝ) : ℂ) * I) ^ j := by
    intro j
    rw [profile_aux_rho_sq (by omega), ← Complex.exp_nat_mul]
    rw [show (j : ℂ) * (((2 * s : ℝ) : ℂ) + ((-(2 * θ) : ℝ) : ℂ) * I) =
      ((2 * j * s : ℝ) : ℂ) + ((-(2 * (j : ℝ) * θ)) : ℝ) * I by push_cast; ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, norm_mul,
    Complex.norm_of_nonneg (by positivity)]
  set w : ℂ := Complex.exp (((2 * s : ℝ) : ℂ) + ((-(2 * θ) : ℝ) : ℂ) * I) with hw
  have hw1 : 2 * Real.exp s * |Real.sin θ| ≤ ‖w - 1‖ := by
    have h := profile_aux_norm_sq_sub_one (2 * s) (-(2 * θ))
    have h' : (2 * Real.exp s * |Real.sin θ|) ^ 2 ≤ ‖w - 1‖ ^ 2 := by
      rw [hw, h]
      have e1 : Real.exp (2 * s) = Real.exp s ^ 2 := by
        rw [sq, ← Real.exp_add]
        ring_nf
      have e2 : Real.sin (-(2 * θ) / 2) ^ 2 = Real.sin θ ^ 2 := by
        rw [show -(2 * θ) / 2 = -θ by ring, Real.sin_neg, neg_sq]
      rw [e2, e1, mul_pow, mul_pow, sq_abs]
      nlinarith [sq_nonneg (Real.exp s ^ 2 - 1)]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h'
  have hgeom := profile_aux_geom_norm w (J' + 1) (2 * Real.exp s * |Real.sin θ|) (by positivity) hw1
  have hwnorm : ‖w‖ = Real.exp (2 * s) := by
    rw [hw, Complex.norm_exp]
    simp
  rw [hwnorm] at hgeom
  -- numerics
  have hs1 : |s| ≤ 1 / 2 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc |s| ≤ 1 / (2 * n) := hs
      _ ≤ 1 / (2 * 1) := by gcongr
      _ = 1 / 2 := by norm_num
  have hsa := abs_le.mp hs1
  have he := profile_aux_e_lt
  have hes : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have hes' : 1 ≤ Real.exp 1 * Real.exp s := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hespos : 0 < Real.exp s := Real.exp_pos s
  have hk0 := profile_aux_sig2_ge hn hs (k := 0) (by omega)
  have hkJ := profile_aux_sig2_ge hn hs (k := J') (by omega)
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] at hk0
  have hpow : Real.exp (2 * s) ^ (J' + 1) = Real.exp (2 * J' * s) * (Real.exp s * Real.exp s) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hpow] at hgeom
  have hA : ((n : ℝ) + 1) * (Real.exp (2 * J' * s) * (Real.exp s * Real.exp s) + 1) ≤
      40 * Real.exp s * sig2 (n + 1) s := by
    have hE : 0 < Real.exp 1 := Real.exp_pos 1
    have hss : 0 ≤ Real.exp s * Real.exp s := by positivity
    have step1 : ((n : ℝ) + 1) * (Real.exp (2 * J' * s) * (Real.exp s * Real.exp s) + 1) ≤
        Real.exp 1 * sig2 (n + 1) s * (Real.exp s * Real.exp s) + Real.exp 1 * sig2 (n + 1) s := by
      have := mul_le_mul_of_nonneg_right hkJ hss
      linarith
    have step2 : Real.exp s * Real.exp s ≤ Real.exp 1 * Real.exp s :=
      mul_le_mul_of_nonneg_right hes hespos.le
    have hEσ : 0 ≤ Real.exp 1 * sig2 (n + 1) s := by positivity
    have step3 : Real.exp 1 * sig2 (n + 1) s * (Real.exp s * Real.exp s) +
          Real.exp 1 * sig2 (n + 1) s ≤
        2 * (Real.exp 1 * Real.exp 1) * (Real.exp s * sig2 (n + 1) s) := by
      have h1 := mul_le_mul_of_nonneg_left step2 hEσ
      have h2 := mul_le_mul_of_nonneg_left hes' hEσ
      linarith
    have he3 : Real.exp 1 ≤ 3 := by linarith
    have step5 : 2 * (Real.exp 1 * Real.exp 1) ≤ 40 := by
      have := mul_le_mul he3 he3 hE.le (by norm_num)
      linarith
    have hpos : 0 ≤ Real.exp s * sig2 (n + 1) s := by positivity
    have := mul_le_mul_of_nonneg_right step5 hpos
    linarith
  calc (sig2 (n + 1) s)⁻¹ * ‖∑ j ∈ Finset.range (J' + 1), w ^ j‖
      ≤ (sig2 (n + 1) s)⁻¹ * ((Real.exp (2 * J' * s) * (Real.exp s * Real.exp s) + 1) /
          (2 * Real.exp s * |Real.sin θ|)) := by gcongr
    _ ≤ 20 / ((n + 1) * |Real.sin θ|) := by
        rw [inv_mul_eq_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have := mul_le_mul_of_nonneg_right hA hsinpos.le
        linarith


/-- The deterministic mean part is small away from `θ ∈ 2πℤ`. -/
theorem m_bound {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) (θ : ℝ)
    (hθ : Real.sin (θ / 2) ≠ 0) :
    ‖mfun (n + 1) (rho (n + 1) s) θ‖ ≤ 10 / (Real.sqrt (n + 1) * |Real.sin (θ / 2)|) := by
  have hσ := sig2_pos (N := n + 1) (by omega) s
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsinpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hθ
  have hterm : ∀ k : ℕ, ((rho (n + 1) s k : ℝ) : ℂ) * ex k θ =
      (((Real.sqrt (sig2 (n + 1) s))⁻¹ : ℝ) : ℂ) * Complex.exp ((s : ℂ) + (θ : ℂ) * I) ^ k := by
    intro k
    rw [rho, ex, ← Complex.exp_nat_mul]
    rw [show (k : ℂ) * ((s : ℂ) + (θ : ℂ) * I) = ((k * s : ℝ) : ℂ) + ((k * θ : ℝ) : ℂ) * I by
      push_cast; ring]
    rw [Complex.exp_add, ← Complex.ofReal_exp]
    push_cast
    ring
  have hm : mfun (n + 1) (rho (n + 1) s) θ = (((Real.sqrt (sig2 (n + 1) s))⁻¹ : ℝ) : ℂ) *
      ∑ k ∈ Finset.range (n + 1), Complex.exp ((s : ℂ) + (θ : ℂ) * I) ^ k := by
    unfold mfun
    rw [Fin.sum_univ_eq_sum_range (fun k => ((rho (n + 1) s k : ℝ) : ℂ) * ex k θ) (n + 1),
      Finset.sum_congr rfl (fun k _ => hterm k), Finset.mul_sum]
  rw [hm, norm_mul, Complex.norm_of_nonneg (by positivity)]
  set w : ℂ := Complex.exp ((s : ℂ) + (θ : ℂ) * I) with hw
  set T := ‖∑ k ∈ Finset.range (n + 1), w ^ k‖ with hT
  have hw1sq : 4 * Real.exp s * Real.sin (θ / 2) ^ 2 ≤ ‖w - 1‖ ^ 2 := by
    rw [hw, profile_aux_norm_sq_sub_one s θ]
    nlinarith [sq_nonneg (Real.exp s - 1)]
  have hwnorm : ‖w‖ = Real.exp s := by
    rw [hw, Complex.norm_exp]
    simp
  have hTw : T * ‖w - 1‖ ≤ Real.exp s ^ (n + 1) + 1 := by
    have h := geom_sum_mul w (n + 1)
    calc T * ‖w - 1‖ = ‖w ^ (n + 1) - 1‖ := by rw [hT, ← norm_mul, h]
      _ ≤ ‖w ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp s ^ (n + 1) + 1 := by rw [norm_pow, norm_one, hwnorm]
  set B := Real.exp s ^ (n + 1) + 1 with hB
  have hT0 : 0 ≤ T := norm_nonneg _
  have hTB : T ^ 2 * (4 * Real.exp s * Real.sin (θ / 2) ^ 2) ≤ B ^ 2 := by
    calc T ^ 2 * (4 * Real.exp s * Real.sin (θ / 2) ^ 2) ≤ T ^ 2 * ‖w - 1‖ ^ 2 := by gcongr
      _ = (T * ‖w - 1‖) ^ 2 := by ring
      _ ≤ B ^ 2 := by
          have : 0 ≤ T * ‖w - 1‖ := by positivity
          gcongr
  -- numerics
  have hs1 : |s| ≤ 1 / 2 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc |s| ≤ 1 / (2 * n) := hs
      _ ≤ 1 / (2 * 1) := by gcongr
      _ = 1 / 2 := by norm_num
  have hsa := abs_le.mp hs1
  have he := profile_aux_e_lt
  have hE : 0 < Real.exp 1 := Real.exp_pos 1
  have hespos : 0 < Real.exp s := Real.exp_pos s
  have hes : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  have hes' : 1 ≤ Real.exp 1 * Real.exp s := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have hk0 := profile_aux_sig2_ge hn hs (k := 0) (by omega)
  have hkn := profile_aux_sig2_ge hn hs (k := n) le_rfl
  simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] at hk0
  have hpow : (Real.exp s ^ (n + 1)) ^ 2 = Real.exp (2 * n * s) * (Real.exp s * Real.exp s) := by
    rw [← pow_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hB2 : B ^ 2 * ((n : ℝ) + 1) ≤ 400 * Real.exp s * sig2 (n + 1) s := by
    have hBle : B ^ 2 ≤ 2 * (Real.exp s ^ (n + 1)) ^ 2 + 2 := by
      rw [hB]
      have := sq_nonneg (Real.exp s ^ (n + 1) - 1)
      linarith
    rw [hpow] at hBle
    have step1 : B ^ 2 * ((n : ℝ) + 1) ≤
        2 * (((n : ℝ) + 1) * Real.exp (2 * n * s)) * (Real.exp s * Real.exp s) +
          2 * ((n : ℝ) + 1) := by
      have := mul_le_mul_of_nonneg_right hBle hn1.le
      linarith
    have hss : 0 ≤ Real.exp s * Real.exp s := by positivity
    have step2 : 2 * (((n : ℝ) + 1) * Real.exp (2 * n * s)) * (Real.exp s * Real.exp s) +
          2 * ((n : ℝ) + 1) ≤
        2 * (Real.exp 1 * sig2 (n + 1) s) * (Real.exp s * Real.exp s) +
          2 * (Real.exp 1 * sig2 (n + 1) s) := by
      have := mul_le_mul_of_nonneg_right hkn hss
      linarith
    have step3 : Real.exp s * Real.exp s ≤ Real.exp 1 * Real.exp s :=
      mul_le_mul_of_nonneg_right hes hespos.le
    have hEσ : 0 ≤ Real.exp 1 * sig2 (n + 1) s := by positivity
    have step4 : 2 * (Real.exp 1 * sig2 (n + 1) s) * (Real.exp s * Real.exp s) +
          2 * (Real.exp 1 * sig2 (n + 1) s) ≤
        4 * (Real.exp 1 * Real.exp 1) * (Real.exp s * sig2 (n + 1) s) := by
      have h1 := mul_le_mul_of_nonneg_left step3 hEσ
      have h2 := mul_le_mul_of_nonneg_left hes' hEσ
      linarith
    have he3 : Real.exp 1 ≤ 3 := by linarith
    have step5 : 4 * (Real.exp 1 * Real.exp 1) ≤ 400 := by
      have := mul_le_mul he3 he3 hE.le (by norm_num)
      linarith
    have hpos : 0 ≤ Real.exp s * sig2 (n + 1) s := by positivity
    have := mul_le_mul_of_nonneg_right step5 hpos
    linarith
  have hA : 0 ≤ (Real.sqrt (sig2 (n + 1) s))⁻¹ * T := by positivity
  have hC : 0 ≤ 10 / (Real.sqrt (n + 1) * |Real.sin (θ / 2)|) := by positivity
  rw [← sq_le_sq₀ hA hC, mul_pow, inv_pow, Real.sq_sqrt hσ.le, div_pow, mul_pow,
    Real.sq_sqrt hn1.le, sq_abs, inv_mul_eq_div, div_le_div_iff₀ hσ (by positivity)]
  have h1 : T ^ 2 * (4 * Real.exp s * Real.sin (θ / 2) ^ 2) * ((n : ℝ) + 1) ≤
      B ^ 2 * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hTB hn1.le
  have h2 : (4 * Real.exp s) * (T ^ 2 * (((n : ℝ) + 1) * Real.sin (θ / 2) ^ 2)) ≤
      (4 * Real.exp s) * (10 ^ 2 * sig2 (n + 1) s) := by
    calc (4 * Real.exp s) * (T ^ 2 * (((n : ℝ) + 1) * Real.sin (θ / 2) ^ 2))
        = T ^ 2 * (4 * Real.exp s * Real.sin (θ / 2) ^ 2) * ((n : ℝ) + 1) := by ring
      _ ≤ B ^ 2 * ((n : ℝ) + 1) := h1
      _ ≤ 400 * Real.exp s * sig2 (n + 1) s := hB2
      _ = (4 * Real.exp s) * (10 ^ 2 * sig2 (n + 1) s) := by ring
  exact le_of_mul_le_mul_left h2 (by positivity)

/- ### Parseval -/

lemma profile_aux_ex_continuous (k : ℕ) : Continuous (ex k) := by
  unfold ex
  fun_prop

lemma profile_aux_ex_mul_conj (j k : ℕ) (θ : ℝ) :
    ex j θ * (starRingEnd ℂ) (ex k θ) = Complex.exp ((((j : ℂ) - k) * I) * θ) := by
  simp only [ex]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma profile_aux_integral_ex (j k : ℕ) :
    ∫ θ in (0 : ℝ)..(2 * π), ex j θ * (starRingEnd ℂ) (ex k θ) =
      if j = k then ((2 * π : ℝ) : ℂ) else 0 := by
  simp_rw [profile_aux_ex_mul_conj]
  split_ifs with h
  · subst h
    simp
  · have hc : ((j : ℂ) - k) * I ≠ 0 := by
      apply mul_ne_zero _ Complex.I_ne_zero
      rw [sub_ne_zero]
      exact_mod_cast h
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (((j : ℂ) - k) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I ((j : ℤ) - k)
      rw [← this]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

/-- Parseval for trigonometric polynomials. -/
theorem cav_norm_sq_trig {N : ℕ} (c : ℕ → ℂ) :
    cav (fun θ => ‖∑ k : Fin N, c k * ex k θ‖ ^ 2) = ∑ k : Fin N, ‖c k‖ ^ 2 := by
  have hcont : ∀ j k : ℕ, Continuous (fun θ => ex j θ * (starRingEnd ℂ) (ex k θ)) := by
    intro j k
    exact (profile_aux_ex_continuous j).mul
      (Complex.continuous_conj.comp (profile_aux_ex_continuous k))
  have hpt : ∀ θ : ℝ, (((‖∑ k : Fin N, c k * ex k θ‖ ^ 2 : ℝ)) : ℂ) =
      ∑ j : Fin N, ∑ k : Fin N, (c j * (starRingEnd ℂ) (c k)) *
        (ex j θ * (starRingEnd ℂ) (ex k θ)) := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [map_mul]
    ring
  have hj : ∀ j : Fin N, ∫ θ in (0 : ℝ)..(2 * π), ∑ k : Fin N,
      (c j * (starRingEnd ℂ) (c k)) * (ex j θ * (starRingEnd ℂ) (ex k θ)) =
      (c j * (starRingEnd ℂ) (c j)) * ((2 * π : ℝ) : ℂ) := by
    intro j
    have hint : ∀ k ∈ (Finset.univ : Finset (Fin N)), IntervalIntegrable
        (fun θ => (c j * (starRingEnd ℂ) (c k)) * (ex j θ * (starRingEnd ℂ) (ex k θ)))
        MeasureTheory.volume 0 (2 * π) :=
      fun k _ => (continuous_const.mul (hcont j k)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hint]
    simp_rw [intervalIntegral.integral_const_mul, profile_aux_integral_ex]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have : (j : ℕ) ≠ (k : ℕ) := fun h => hk (Fin.ext h).symm
      simp [this]
    · simp
  have hC : ((∫ θ in (0 : ℝ)..(2 * π), ‖∑ k : Fin N, c k * ex k θ‖ ^ 2 : ℝ) : ℂ) =
      (((2 * π) * ∑ k : Fin N, ‖c k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hpt]
    have hint : ∀ j ∈ (Finset.univ : Finset (Fin N)), IntervalIntegrable
        (fun θ => ∑ k : Fin N, (c j * (starRingEnd ℂ) (c k)) *
          (ex j θ * (starRingEnd ℂ) (ex k θ))) MeasureTheory.volume 0 (2 * π) :=
      fun j _ => by
        apply Continuous.intervalIntegrable
        apply continuous_finsetSum
        intro k _
        exact continuous_const.mul (hcont j k)
    rw [intervalIntegral.integral_finsetSum hint]
    simp_rw [hj]
    simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hR := Complex.ofReal_injective hC
  unfold cav
  rw [hR]
  have hπ : (2 * π : ℝ) ≠ 0 := by positivity
  field_simp

theorem cav_norm_sq_mfun {N : ℕ} (hN : 1 ≤ N) (s : ℝ) :
    cav (fun θ => ‖mfun N (rho N s) θ‖ ^ 2) = 1 := by
  have h := cav_norm_sq_trig (N := N) (fun k => ((rho N s k : ℝ) : ℂ))
  simp only [mfun]
  rw [h]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Fin.sum_univ_eq_sum_range (fun k => rho N s k ^ 2) N]
  exact sum_rho_sq hN s

/- ### Measure of the bad set -/

theorem cav_bad_theta {ε : ℝ} (hε : 0 < ε) :
    cav (fun θ => if |Real.sin θ| < ε then 1 else 0) ≤ 2 * ε := by
  have hpi := Real.pi_pos
  set a := π * ε / 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hSmeas : MeasurableSet {θ : ℝ | |Real.sin θ| < ε} :=
    (isOpen_lt (continuous_abs.comp Real.continuous_sin) continuous_const).measurableSet
  have hfun : (fun θ => if |Real.sin θ| < ε then (1 : ℝ) else 0) =
      Set.indicator {θ : ℝ | |Real.sin θ| < ε} 1 := by
    funext θ
    simp [Set.indicator_apply]
  have hint : ∫ θ in (0 : ℝ)..(2 * π), (if |Real.sin θ| < ε then (1 : ℝ) else 0) =
      MeasureTheory.volume.real ({θ : ℝ | |Real.sin θ| < ε} ∩ Set.Ioc 0 (2 * π)) := by
    rw [intervalIntegral.integral_of_le (by positivity), hfun,
      MeasureTheory.integral_indicator_one hSmeas, MeasureTheory.measureReal_restrict_apply hSmeas]
  have key : ∀ u : ℝ, 0 ≤ u → u ≤ π / 2 → |Real.sin u| < ε → u ≤ a := by
    intro u hu0 hu1 hu
    have h1 := Real.mul_le_sin hu0 hu1
    have h2 : Real.sin u ≤ |Real.sin u| := le_abs_self _
    have h3 : 2 / π * u ≤ ε := by linarith
    calc u = π / 2 * (2 / π * u) := by field_simp
      _ ≤ π / 2 * ε := by gcongr
      _ = a := by rw [ha]; ring
  have hsub : {θ : ℝ | |Real.sin θ| < ε} ∩ Set.Ioc 0 (2 * π) ⊆
      Set.Icc 0 a ∪ Set.Icc (π - a) (π + a) ∪ Set.Icc (2 * π - a) (2 * π) := by
    rintro θ ⟨hθS, hθ0, hθ2⟩
    change |Real.sin θ| < ε at hθS
    by_cases h1 : θ ≤ π / 2
    · left; left
      exact ⟨hθ0.le, key θ hθ0.le h1 hθS⟩
    by_cases h2 : θ ≤ π
    · left; right
      have := key (π - θ) (by linarith) (by linarith) (by rwa [Real.sin_pi_sub])
      constructor <;> linarith
    by_cases h3 : θ ≤ 3 * π / 2
    · left; right
      have := key (θ - π) (by linarith) (by linarith) (by rwa [Real.sin_sub_pi, abs_neg])
      constructor <;> linarith
    · right
      have := key (2 * π - θ) (by linarith) (by linarith)
        (by rwa [Real.sin_two_pi_sub, abs_neg])
      constructor <;> linarith
  have hfin : MeasureTheory.volume
      (Set.Icc 0 a ∪ Set.Icc (π - a) (π + a) ∪ Set.Icc (2 * π - a) (2 * π)) ≠ ⊤ :=
    (MeasureTheory.measure_union_lt_top (MeasureTheory.measure_union_lt_top measure_Icc_lt_top
      measure_Icc_lt_top) measure_Icc_lt_top).ne
  have hmeas_le : MeasureTheory.volume.real ({θ : ℝ | |Real.sin θ| < ε} ∩ Set.Ioc 0 (2 * π)) ≤
      4 * a := by
    calc MeasureTheory.volume.real ({θ : ℝ | |Real.sin θ| < ε} ∩ Set.Ioc 0 (2 * π))
        ≤ MeasureTheory.volume.real
            (Set.Icc 0 a ∪ Set.Icc (π - a) (π + a) ∪ Set.Icc (2 * π - a) (2 * π)) :=
          MeasureTheory.measureReal_mono hsub hfin
      _ ≤ MeasureTheory.volume.real (Set.Icc 0 a ∪ Set.Icc (π - a) (π + a)) +
            MeasureTheory.volume.real (Set.Icc (2 * π - a) (2 * π)) :=
          MeasureTheory.measureReal_union_le _ _
      _ ≤ MeasureTheory.volume.real (Set.Icc 0 a) +
            MeasureTheory.volume.real (Set.Icc (π - a) (π + a)) +
            MeasureTheory.volume.real (Set.Icc (2 * π - a) (2 * π)) := by
          gcongr
          exact MeasureTheory.measureReal_union_le _ _
      _ = a + 2 * a + a := by
          rw [Real.volume_real_Icc_of_le ha0, Real.volume_real_Icc_of_le (by linarith),
            Real.volume_real_Icc_of_le (by linarith)]
          ring
      _ = 4 * a := by ring
  unfold cav
  rw [hint]
  calc (2 * π)⁻¹ * MeasureTheory.volume.real ({θ : ℝ | |Real.sin θ| < ε} ∩ Set.Ioc 0 (2 * π))
      ≤ (2 * π)⁻¹ * (4 * a) := by gcongr
    _ = ε := by
        rw [ha]
        field_simp
        ring
    _ ≤ 2 * ε := by linarith

theorem abs_sin_half_ge {θ : ℝ} : |Real.sin θ| / 2 ≤ |Real.sin (θ / 2)| := by
  have h : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]
    congr 1
    ring
  rw [h, abs_mul, abs_mul, abs_two]
  have hc : |Real.cos (θ / 2)| ≤ 1 := Real.abs_cos_le_one _
  have hs : 0 ≤ |Real.sin (θ / 2)| := abs_nonneg _
  nlinarith

theorem Wfun_continuous {N : ℕ} (ρ : ℕ → ℝ) (x : Fin N → Bool) : Continuous (Wfun ρ x) := by
  unfold Wfun
  exact continuous_finsetSum _ (fun k _ => continuous_const.mul (profile_aux_ex_continuous k))

theorem mfun_continuous (N : ℕ) (ρ : ℕ → ℝ) : Continuous (mfun N ρ) := by
  unfold mfun
  exact continuous_finsetSum _ (fun k _ => continuous_const.mul (profile_aux_ex_continuous k))

/- ### Second moment of the Rademacher sum -/

lemma profile_aux_flip_invol {N : ℕ} (k : Fin N) :
    Function.Involutive (fun x : Fin N → Bool => Function.update x k (!x k)) := by
  intro x
  simp

lemma profile_aux_sum_flip {N : ℕ} (k : Fin N) (f : (Fin N → Bool) → ℝ) :
    ∑ x, f (Function.update x k (!x k)) = ∑ x, f x :=
  Equiv.sum_comp ((profile_aux_flip_invol k).toPerm _) f

lemma profile_aux_sgn_not (c : Bool) : sgn (!c) = - sgn c := by
  cases c <;> simp [sgn]

lemma profile_aux_avg_sum {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → (Fin N → Bool) → ℝ) :
    cubeAvg N (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeAvg N (f i) := by
  unfold cubeAvg
  rw [Finset.sum_comm, Finset.sum_div]

lemma profile_aux_avg_smul {N : ℕ} (c : ℝ) (F : (Fin N → Bool) → ℝ) :
    cubeAvg N (fun x => c * F x) = c * cubeAvg N F := by
  unfold cubeAvg
  rw [← Finset.mul_sum, mul_div_assoc]

lemma profile_aux_avg_add {N : ℕ} (F G : (Fin N → Bool) → ℝ) :
    cubeAvg N (fun x => F x + G x) = cubeAvg N F + cubeAvg N G := by
  unfold cubeAvg
  rw [Finset.sum_add_distrib, add_div]

lemma profile_aux_avg_sgn_mul {N : ℕ} (j k : Fin N) :
    cubeAvg N (fun x => sgn (x j) * sgn (x k)) = if j = k then 1 else 0 := by
  split_ifs with h
  · subst h
    simp only [← sq, sgn_sq]
    unfold cubeAvg
    simp
  · unfold cubeAvg
    have h1 := profile_aux_sum_flip j (fun x => sgn (x j) * sgn (x k))
    simp only [Function.update_self, Function.update_of_ne (Ne.symm h)] at h1
    have h2 : ∀ x : Fin N → Bool, sgn (!x j) * sgn (x k) = -(sgn (x j) * sgn (x k)) := by
      intro x
      rw [profile_aux_sgn_not]
      ring
    simp only [h2, Finset.sum_neg_distrib] at h1
    have : ∑ x : Fin N → Bool, sgn (x j) * sgn (x k) = 0 := by linarith
    rw [this, zero_div]

lemma profile_aux_avg_rademacher_sq {N : ℕ} (a : Fin N → ℝ) :
    cubeAvg N (fun x => (∑ k, sgn (x k) * a k) ^ 2) = ∑ k, a k ^ 2 := by
  have h : ∀ x : Fin N → Bool, (∑ k, sgn (x k) * a k) ^ 2 =
      ∑ j, ∑ k, (a j * a k) * (sgn (x j) * sgn (x k)) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [h]
  rw [profile_aux_avg_sum]
  simp_rw [profile_aux_avg_sum, profile_aux_avg_smul, profile_aux_avg_sgn_mul]
  simp [sq]

/-- `E_x |W|² = ∑ ρ_k²`: the second moment of the Rademacher sum. -/
theorem cubeAvg_norm_sq_Wfun {N : ℕ} (ρ : ℕ → ℝ) (θ : ℝ) :
    cubeAvg N (fun x => ‖Wfun ρ x θ‖ ^ 2) = ∑ k : Fin N, ρ k ^ 2 := by
  have hpt : ∀ x : Fin N → Bool, ‖Wfun ρ x θ‖ ^ 2 =
      (∑ k : Fin N, sgn (x k) * (ρ k * Real.cos ((k : ℕ) * θ))) ^ 2 +
        (∑ k : Fin N, sgn (x k) * (ρ k * Real.sin ((k : ℕ) * θ))) ^ 2 := by
    intro x
    have hre : (Wfun ρ x θ).re = ∑ k : Fin N, sgn (x k) * (ρ k * Real.cos ((k : ℕ) * θ)) := by
      simp only [Wfun, Complex.re_sum, Complex.re_ofReal_mul, ex, Complex.exp_ofReal_mul_I_re]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have him : (Wfun ρ x θ).im = ∑ k : Fin N, sgn (x k) * (ρ k * Real.sin ((k : ℕ) * θ)) := by
      simp only [Wfun, Complex.im_sum, Complex.im_ofReal_mul, ex, Complex.exp_ofReal_mul_I_im]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  simp_rw [hpt]
  rw [profile_aux_avg_add, profile_aux_avg_rademacher_sq, profile_aux_avg_rademacher_sq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]

end E522

end

/- ## Section: `CavLemmas` -/

section

/-
# Elementary facts about `cav` and the normalised polynomial `Zfun`
-/

open Real Complex MeasureTheory Filter Topology intervalIntegral

namespace E522

noncomputable section

lemma two_pi_pos : (0 : ℝ) < 2 * π := by positivity

lemma cav_add {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π))
    (hG : IntervalIntegrable G volume 0 (2 * π)) :
    cav (fun θ => F θ + G θ) = cav F + cav G := by
  unfold cav; rw [intervalIntegral.integral_add hF hG]; ring

lemma cav_sub {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π))
    (hG : IntervalIntegrable G volume 0 (2 * π)) :
    cav (fun θ => F θ - G θ) = cav F - cav G := by
  unfold cav; rw [intervalIntegral.integral_sub hF hG]; ring

lemma cav_const_mul (c : ℝ) (F : ℝ → ℝ) : cav (fun θ => c * F θ) = c * cav F := by
  unfold cav; rw [intervalIntegral.integral_const_mul]; ring

lemma cav_const (c : ℝ) : cav (fun _ => c) = c := by
  unfold cav
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  field_simp

lemma cav_mono {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π))
    (hG : IntervalIntegrable G volume 0 (2 * π)) (h : ∀ θ, F θ ≤ G θ) : cav F ≤ cav G := by
  unfold cav
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.integral_mono_on two_pi_pos.le hF hG (fun θ _ => h θ)

lemma cav_mono_ae {F G : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π))
    (hG : IntervalIntegrable G volume 0 (2 * π))
    (h : ∀ᵐ θ ∂(volume.restrict (Set.uIoc 0 (2 * π))), F θ ≤ G θ) : cav F ≤ cav G := by
  unfold cav
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Set.uIoc_of_le two_pi_pos.le] at h
  apply intervalIntegral.integral_mono_ae_restrict two_pi_pos.le hF hG
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
  exact h

lemma cav_nonneg {F : ℝ → ℝ} (h : ∀ θ, 0 ≤ F θ) : 0 ≤ cav F := by
  unfold cav
  apply mul_nonneg (by positivity)
  exact intervalIntegral.integral_nonneg two_pi_pos.le (fun θ _ => h θ)

lemma abs_cav_le (F : ℝ → ℝ) : |cav F| ≤ cav (fun θ => |F θ|) := by
  unfold cav
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact intervalIntegral.abs_integral_le_integral_abs two_pi_pos.le

lemma cav_le_of_le_const {F : ℝ → ℝ} (hF : IntervalIntegrable F volume 0 (2 * π)) {c : ℝ}
    (h : ∀ θ, F θ ≤ c) : cav F ≤ c := by
  calc cav F ≤ cav (fun _ => c) :=
        cav_mono hF intervalIntegrable_const h
    _ = c := cav_const c

/-- `cubeAvg` commutes with `cav` (finite sums). -/
lemma cubeAvg_cav {N : ℕ} (F : (Fin N → Bool) → ℝ → ℝ)
    (hF : ∀ x, IntervalIntegrable (F x) volume 0 (2 * π)) :
    cubeAvg N (fun x => cav (F x)) = cav (fun θ => cubeAvg N (fun x => F x θ)) := by
  unfold cubeAvg cav
  rw [← Finset.mul_sum, intervalIntegral.integral_div, intervalIntegral.integral_finsetSum
    (fun x _ => hF x)]
  ring

lemma circleMap_zero_eq (R θ : ℝ) : circleMap 0 R θ = (R : ℂ) * Complex.exp ((θ : ℂ) * I) := by
  simp [circleMap]

lemma ex_eq (k : ℕ) (θ : ℝ) : ex k θ = Complex.exp ((θ : ℂ) * I) ^ k := by
  rw [ex, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

end

end E522

end

/- ## Section: `Transfer` -/

section

/-
# From the Formal Conjectures statement to finite cube probabilities

The FC statement quantifies over an arbitrary probability space `Ω` carrying independent
coefficients `c i : Ω → ℂ`, each with law `count[|{0,1}]` (uniform on `{0,1}`), and the
events concern all degrees of the SAME infinite sequence. We push the whole sequence forward
to `ν = infinitePi (fun _ => count[|{0,1}])` (`iIndepFun.map_fun_eq_infinitePi_map₀`),
compute the law of the first `N` bits under `ν` (uniform on `Bool^N`), and apply the first
Borel–Cantelli lemma (`ae_eventually_notMem`) for each tolerance `1/(m+1)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace E522

noncomputable section

/-- The law of one coefficient: uniform on `{0,1}` with respect to counting measure. -/
abbrev coinLaw : Measure ℂ := Measure.count[|({0, 1} : Set ℂ)]

lemma measurableSet_01 : MeasurableSet ({0, 1} : Set ℂ) :=
  (Set.toFinite _).measurableSet

lemma count_01 : Measure.count ({0, 1} : Set ℂ) = 2 := by
  rw [Measure.count_apply_finite _ (Set.toFinite _)]
  have : (Set.toFinite ({0, 1} : Set ℂ)).toFinset = {0, 1} := by
    ext z; simp
  rw [this]
  simp

instance coinLaw_isProb : IsProbabilityMeasure coinLaw :=
  cond_isProbabilityMeasure_of_finite (by rw [count_01]; norm_num) (by rw [count_01]; norm_num)

lemma coinLaw_apply (t : Set ℂ) :
    coinLaw t = (1 / 2 : ENNReal) * Measure.count (({0, 1} : Set ℂ) ∩ t) := by
  rw [coinLaw, cond_apply measurableSet_01, count_01]
  simp

lemma coinLaw_compl : coinLaw ({0, 1} : Set ℂ)ᶜ = 0 := by
  rw [coinLaw_apply]; simp

lemma coinLaw_eq_one : coinLaw {z : ℂ | decide (z = 1) = true} = 1 / 2 := by
  rw [coinLaw_apply]
  have : ({0, 1} : Set ℂ) ∩ {z : ℂ | decide (z = 1) = true} = {1} := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; exact ⟨Or.inr rfl, rfl⟩
  rw [this, Measure.count_singleton]
  simp

lemma coinLaw_eq_zero : coinLaw {z : ℂ | decide (z = 1) = false} = 1 / 2 := by
  rw [coinLaw_apply]
  have : ({0, 1} : Set ℂ) ∩ {z : ℂ | decide (z = 1) = false} = {0} := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · rintro rfl; exact ⟨Or.inl rfl, zero_ne_one⟩
  rw [this, Measure.count_singleton]
  simp

lemma coinLaw_bit (b : Bool) : coinLaw {z : ℂ | decide (z = 1) = b} = 1 / 2 := by
  cases b
  · exact coinLaw_eq_zero
  · exact coinLaw_eq_one

lemma measurableSet_decide_eq (b : Bool) : MeasurableSet {z : ℂ | decide (z = 1) = b} := by
  cases b
  · convert (measurableSet_singleton (1 : ℂ)).compl using 1
    ext z; simp
  · convert measurableSet_singleton (1 : ℂ) using 1
    ext z; simp

/-- The product law of the coefficient sequence. -/
abbrev nuLaw : Measure (ℕ → ℂ) := Measure.infinitePi (fun _ : ℕ => coinLaw)

/-- The first `N` bits of a coefficient sequence. -/
def bitsOf (N : ℕ) (x : ℕ → ℂ) : Fin N → Bool := fun k => decide (x k = 1)

lemma measurable_bitsOf (N : ℕ) : Measurable (bitsOf N) := by
  rw [measurable_pi_iff]
  intro k
  have : (fun x : ℕ → ℂ => bitsOf N x k) = (fun z : ℂ => decide (z = 1)) ∘ (fun x => x (k : ℕ)) :=
    rfl
  rw [this]
  exact (measurable_to_countable' (fun b => measurableSet_decide_eq b)).comp
    (measurable_pi_apply (k : ℕ))

lemma nuLaw_bitsOf_eq (N : ℕ) (a : Fin N → Bool) :
    nuLaw {x | bitsOf N x = a} = (1 / 2 : ENNReal) ^ N := by
  classical
  let t : ℕ → Set ℂ := fun k => if h : k < N then {z : ℂ | decide (z = 1) = a ⟨k, h⟩} else Set.univ
  have hset : {x : ℕ → ℂ | bitsOf N x = a} = ((Finset.range N : Finset ℕ) : Set ℕ).pi t := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio, t]
    constructor
    · intro h k hk
      rw [dif_pos hk]
      have := congrFun h ⟨k, hk⟩
      simpa [bitsOf] using this
    · intro h
      funext k
      have := h k k.2
      rw [dif_pos k.2] at this
      simpa [bitsOf] using this
  rw [hset, Measure.infinitePi_pi]
  · rw [Finset.prod_congr rfl (g := fun _ => (1 / 2 : ENNReal))]
    · simp
    · intro k hk
      have hk' : k < N := Finset.mem_range.mp hk
      simp only [t, dif_pos hk']
      exact coinLaw_bit _
  · intro k _
    simp only [t]
    split_ifs with hk
    · exact measurableSet_decide_eq _
    · exact MeasurableSet.univ

lemma nuLaw_bitsOf_mem (N : ℕ) (P : (Fin N → Bool) → Prop) :
    nuLaw {x | P (bitsOf N x)} = ENNReal.ofReal (cubeProb N P) := by
  classical
  have hset : {x : ℕ → ℂ | P (bitsOf N x)} =
      ⋃ a ∈ (Finset.univ.filter P : Finset (Fin N → Bool)), {x | bitsOf N x = a} := by
    ext x; simp
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun a _ => nuLaw_bitsOf_eq N a)]
    rw [Finset.sum_const, nsmul_eq_mul, cubeProb]
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    rw [ENNReal.ofReal_natCast]
    rw [div_eq_mul_inv]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    rw [one_mul, ENNReal.inv_pow]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hab (hx.symm.trans hx')
  · intro a _
    exact measurable_bitsOf N (measurableSet_singleton a)

open scoped Classical in
/-- The FC root count of the degree-`n` polynomial built from a coefficient sequence. -/
def rawCount (x : ℕ → ℂ) (n : ℕ) : ℕ :=
  (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (x i)).roots.countP
    (· ∈ Metric.closedBall (0 : ℂ) 1)

lemma poly_bitsOf (x : ℕ → ℂ) (hx : ∀ i, x i = 0 ∨ x i = 1) (n : ℕ) :
    poly (bitsOf (n + 1) x) = ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (x i) := by
  rw [poly, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (x i))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  rcases hx k with h | h <;> simp [bitsOf, bit, h]

lemma rawCount_eq (x : ℕ → ℂ) (hx : ∀ i, x i = 0 ∨ x i = 1) (n : ℕ) :
    rawCount x n = rootCount (bitsOf (n + 1) x) := by
  rw [rawCount, rootCount, poly_bitsOf x hx n]

/-- Main transfer theorem: complete convergence on the cube implies the almost sure
statement for any FC-style coefficient sequence. -/
theorem transfer {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (c : ℕ → Ω → ℂ) (h_indep : iIndepFun c ℙ)
    (h_unif : ∀ i, MeasureTheory.pdf.IsUniform (c i) ({0, 1} : Set ℂ) ℙ Measure.count)
    (hsum : ∀ m : ℕ, Summable (fun n : ℕ =>
      cubeProb (n + 1) (fun x => (1 : ℝ) / (m + 1) < |(2 * rootCount x : ℝ) / n - 1|))) :
    ℙ {ω | Tendsto (fun n : ℕ => (2 * rawCount (fun i => c i ω) n : ℝ) / n) atTop (𝓝 1)} = 1 := by
  -- each coefficient is a.e.-measurable with law `coinLaw`
  have hlaw : ∀ i, Measure.map (c i) ℙ = coinLaw := fun i => (h_unif i).map_eq
  have hmeas : ∀ i, AEMeasurable (c i) ℙ := fun i => (h_unif i).aemeasurable
  set X : Ω → ℕ → ℂ := fun ω i => c i ω with hX
  have hXm : AEMeasurable X ℙ := AEMeasurable.of_eval hmeas
  have hmap : Measure.map X ℙ = nuLaw := by
    rw [h_indep.map_fun_eq_infinitePi_map₀ hXm]
    congr 1
    funext i
    exact hlaw i
  -- almost every sequence is `{0,1}`-valued
  have h01 : ∀ᵐ x ∂nuLaw, ∀ i, x i = 0 ∨ x i = 1 := by
    rw [ae_all_iff]
    intro i
    have hev : Measure.map (fun x : ℕ → ℂ => x i) nuLaw = coinLaw :=
      Measure.infinitePi_map_eval _ i
    have : ∀ᵐ z ∂coinLaw, z = 0 ∨ z = 1 := by
      rw [ae_iff]
      have hs : {z : ℂ | ¬(z = 0 ∨ z = 1)} = ({0, 1} : Set ℂ)ᶜ := by
        ext z; simp
      rw [hs]; exact coinLaw_compl
    rw [← hev] at this
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable this
  -- Borel–Cantelli for each tolerance
  have hBC : ∀ m : ℕ, ∀ᵐ x ∂nuLaw, ∀ᶠ n in atTop,
      x ∉ {y : ℕ → ℂ | (1 : ℝ) / (m + 1) <
        |(2 * rootCount (bitsOf (n + 1) y) : ℝ) / n - 1|} := by
    intro m
    apply ae_eventually_notMem
    have hterm : ∀ n : ℕ, nuLaw {y : ℕ → ℂ | (1 : ℝ) / (m + 1) <
        |(2 * rootCount (bitsOf (n + 1) y) : ℝ) / n - 1|} =
        ENNReal.ofReal (cubeProb (n + 1)
          (fun x => (1 : ℝ) / (m + 1) < |(2 * rootCount x : ℝ) / n - 1|)) := fun n =>
      nuLaw_bitsOf_mem (n + 1) (fun x => (1 : ℝ) / (m + 1) < |(2 * rootCount x : ℝ) / n - 1|)
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => cubeProb_nonneg _ _) (hsum m)]
    exact ENNReal.ofReal_ne_top
  have hgood : ∀ᵐ x ∂nuLaw, Tendsto (fun n : ℕ => (2 * rawCount x n : ℝ) / n) atTop (𝓝 1) := by
    have hall : ∀ᵐ x ∂nuLaw, ∀ m : ℕ, ∀ᶠ n in atTop,
        x ∉ {y : ℕ → ℂ | (1 : ℝ) / (m + 1) <
          |(2 * rootCount (bitsOf (n + 1) y) : ℝ) / n - 1|} := ae_all_iff.mpr hBC
    filter_upwards [h01, hall] with x hx hm
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm'⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := (hm m).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    simp only [not_lt] at h1
    rw [Real.dist_eq, rawCount_eq x hx n]
    exact lt_of_le_of_lt h1 hm'
  have hae : ∀ᵐ ω ∂(ℙ : Measure Ω),
      Tendsto (fun n : ℕ => (2 * rawCount (fun i => c i ω) n : ℝ) / n) atTop (𝓝 1) := by
    rw [← hmap] at hgood
    exact ae_of_ae_map hXm hgood
  -- an a.e. true (possibly non-measurable) event has probability one
  set S := {ω | Tendsto (fun n : ℕ => (2 * rawCount (fun i => c i ω) n : ℝ) / n) atTop (𝓝 1)}
  have hc : (ℙ : Measure Ω) Sᶜ = 0 := by
    rw [ae_iff] at hae
    exact hae
  apply le_antisymm prob_le_one
  have := measure_union_le (μ := (ℙ : Measure Ω)) S Sᶜ
  rw [Set.union_compl_self, measure_univ, hc, add_zero] at this
  exact this

end

end E522

end

/- ## Section: `Bridge` -/

section

/-
# Bridge: from the module lemmas to bounds on `Λ_x(s)`

* `lam_le_cav_phiD`: `Λ_x(s) ≤ cav(φ_δ(Z)) − log 2`.
* `lam_zero_ge`: lower bound for `Λ_x(0)` through `cav(φ_δ(Z))`, `cav(ψ_β(Z))` and the measure
  `μ` of the super-polynomially small values of `f_x` on the unit circle.
* `EF_bound`: `E_x cav(φ_δ(Z)) = κ_δ + o(1)` uniformly for `|s| ≤ 1/(2n)` (Lindeberg).
* `EK_bound`: `E_x cav(ψ_β(Z)) ≤ 2β₂ + 2/√N + β²/β₂²` (Littlewood–Offord).
* `F_conc`, `K_conc`: exponential concentration (martingale + square-root decomposition).
-/

open Real Complex MeasureTheory Filter Topology

namespace E522

noncomputable section

/- ### `Z = 2 f / σ` and integrability -/

lemma Zfun_eq_eval {N : ℕ} (x : Fin N → Bool) (s θ : ℝ) :
    Zfun x s θ =
      ((2 / Real.sqrt (sig2 N s) : ℝ) : ℂ) * (poly x).eval (circleMap 0 (Real.exp s) θ) := by
  rw [poly_eval, circleMap_zero_eq, Finset.mul_sum]
  unfold Zfun Wfun mfun
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h : ((sgn (x k) : ℝ) : ℂ) + 1 = 2 * ((bit (x k) : ℝ) : ℂ) := by
    exact_mod_cast sgn_add_one (x k)
  rw [ex_eq, mul_pow, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  unfold rho
  push_cast
  linear_combination
    ((Complex.exp ((k : ℂ) * (s : ℂ)) / ((Real.sqrt (sig2 N s) : ℝ) : ℂ)) *
      Complex.exp ((θ : ℂ) * I) ^ (k : ℕ)) * h

lemma Zfun_continuous {N : ℕ} (x : Fin N → Bool) (s : ℝ) : Continuous (Zfun x s) :=
  (Wfun_continuous _ x).add (mfun_continuous N _)

lemma log_norm_Zfun_ii {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (hx : poly x ≠ 0) (s : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖Zfun x s θ‖) volume 0 (2 * π) := by
  have hmero : MeromorphicOn (fun z => (poly x).eval z) (Metric.sphere (0 : ℂ) |Real.exp s|) :=
    AnalyticOnNhd.meromorphicOn (fun z _ => (Polynomial.differentiable (poly x)).analyticAt z)
  have h1 : CircleIntegrable (fun z => Real.log ‖(poly x).eval z‖) 0 (Real.exp s) :=
    hmero.circleIntegrable_log_norm
  have h2 : IntervalIntegrable (fun θ => Real.log (2 / Real.sqrt (sig2 N s)) +
      Real.log ‖(poly x).eval (circleMap 0 (Real.exp s) θ)‖) volume 0 (2 * π) :=
    intervalIntegrable_const.add h1
  refine h2.congr_ae ?_
  filter_upwards [Zfun_ne_zero_ae hN x hx s] with θ hθ
  rw [Zfun_eq_eval] at hθ ⊢
  have hσ : 0 < 2 / Real.sqrt (sig2 N s) := by
    have := sig2_pos hN s
    positivity
  have hev : (poly x).eval (circleMap 0 (Real.exp s) θ) ≠ 0 := by
    intro h; apply hθ; rw [h, mul_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le,
    Real.log_mul hσ.ne' (norm_ne_zero_iff.mpr hev)]

lemma phiD_Zfun_ii {N : ℕ} (x : Fin N → Bool) (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IntervalIntegrable (fun θ => phiD δ (Zfun x s θ)) volume 0 (2 * π) :=
  ((phiD_continuous hδ).comp (Zfun_continuous x s)).intervalIntegrable _ _

lemma psiB_Zfun_ii {N : ℕ} (x : Fin N → Bool) (s : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (fun θ => psiB β (Zfun x s θ)) volume 0 (2 * π) :=
  ((psiB_continuous hβ).comp (Zfun_continuous x s)).intervalIntegrable _ _

/- ### Upper bound for `Λ` -/

lemma lam_le_cav_phiD {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (hx : poly x ≠ 0) (s : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    Lam x s ≤ cav (fun θ => phiD δ (Zfun x s θ)) - Real.log 2 := by
  rw [lam_eq_cav hN x hx s]
  gcongr
  apply cav_mono_ae (log_norm_Zfun_ii hN x hx s) (phiD_Zfun_ii x s hδ)
  filter_upwards [Zfun_ne_zero_ae hN x hx s] with θ hθ
  exact log_norm_le_phiD hδ hθ

/- ### Lower bound for `Λ` at radius `1` -/

/-- Indicator of the super-polynomially small values of `f_x` on the unit circle. -/
def smallInd {N : ℕ} (x : Fin N → Bool) (ε' : ℝ) (θ : ℝ) : ℝ :=
  if ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < ε' then 1 else 0

lemma smallInd_nonneg {N : ℕ} (x : Fin N → Bool) (ε' θ : ℝ) : 0 ≤ smallInd x ε' θ := by
  unfold smallInd; split_ifs <;> norm_num

lemma smallInd_le_one {N : ℕ} (x : Fin N → Bool) (ε' θ : ℝ) : smallInd x ε' θ ≤ 1 := by
  unfold smallInd; split_ifs <;> norm_num

lemma evalCircle_continuous {N : ℕ} (x : Fin N → Bool) :
    Continuous (fun θ : ℝ => (poly x).eval (Complex.exp ((θ : ℂ) * I))) :=
  (Polynomial.continuous _).comp (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const))

lemma smallInd_measurable {N : ℕ} (x : Fin N → Bool) (ε' : ℝ) :
    Measurable (smallInd x ε') := by
  unfold smallInd
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt ((evalCircle_continuous x).norm.measurable) measurable_const

lemma smallInd_ii {N : ℕ} (x : Fin N → Bool) (ε' : ℝ) :
    IntervalIntegrable (smallInd x ε') volume 0 (2 * π) := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (smallInd_measurable x ε').aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun θ => ?_)
  simp only [Real.norm_eq_abs, abs_one]
  rw [abs_of_nonneg (smallInd_nonneg x ε' θ)]
  exact smallInd_le_one x ε' θ

lemma log_norm_evalCircle_ii {N : ℕ} (x : Fin N → Bool) (hx : poly x ≠ 0) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖)
      volume 0 (2 * π) := by
  have hmero : MeromorphicOn (fun z => (poly x).eval z) (Metric.sphere (0 : ℂ) |(1 : ℝ)|) :=
    AnalyticOnNhd.meromorphicOn (fun z _ => (Polynomial.differentiable (poly x)).analyticAt z)
  have h1 : CircleIntegrable (fun z => Real.log ‖(poly x).eval z‖) 0 1 :=
    hmero.circleIntegrable_log_norm
  unfold CircleIntegrable at h1
  convert h1 using 3 with θ
  rw [circleMap_zero_eq]; simp

lemma lam_zero_ge {N : ℕ} (hN : 4 ≤ N) (x : Fin N → Bool) (hx : poly x ≠ 0)
    {ε' δ β : ℝ} (hε' : 0 < ε') (hηδ : 2 * ε' / Real.sqrt N ≤ δ) (hδ1 : δ ≤ 1) (hβ : 0 < β) :
    cav (fun θ => phiD δ (Zfun x 0 θ)) - δ ^ 2 / (2 * β ^ 2)
      - 2 * Real.log (2 * δ / (2 * ε' / Real.sqrt N)) * cav (fun θ => psiB β (Zfun x 0 θ))
      - ((1 + Real.log N) * cav (smallInd x ε')
          + Real.sqrt (cav (smallInd x ε')) * Real.sqrt (400 * N ^ 2)) - Real.log 2
      ≤ Lam x 0 := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  set η := 2 * ε' / Real.sqrt N with hη
  have hηpos : 0 < η := by positivity
  have hδ : 0 < δ := lt_of_lt_of_le hηpos hηδ
  set Λ := Real.log (2 * δ / η) with hΛ
  set Z := fun θ => Zfun x 0 θ with hZ
  -- the pointwise inequality integrand
  set Tint : ℝ → ℝ := fun θ => if ‖Z θ‖ < η then 1 + Real.log (1 / ‖Z θ‖) else 0 with hTint
  set f := fun θ : ℝ => (poly x).eval (Complex.exp ((θ : ℂ) * I)) with hf
  have hZf : ∀ θ, Z θ = ((2 / Real.sqrt N : ℝ) : ℂ) * f θ := fun θ => Zfun_zero_eq hN1 x θ
  have hlogN : 0 ≤ Real.log (Real.sqrt N / 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), one_mul]
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  set Tb : ℝ → ℝ := fun θ => smallInd x ε' θ * (1 + Real.log (Real.sqrt N / 2) + |Real.log ‖f θ‖|)
    with hTb
  have hTb_nonneg : ∀ θ, 0 ≤ Tb θ := fun θ =>
    mul_nonneg (smallInd_nonneg x ε' θ) (by positivity)
  have hnormZ : ∀ θ, ‖Z θ‖ = 2 / Real.sqrt N * ‖f θ‖ := by
    intro θ
    rw [hZf θ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hTint_nonneg : ∀ θ, 0 ≤ Tint θ := by
    intro θ
    simp only [hTint]
    split_ifs with h
    · by_cases hz : ‖Z θ‖ = 0
      · rw [hz]; simp
      · have hz' : 0 < ‖Z θ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have : 0 ≤ Real.log (1 / ‖Z θ‖) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ hz', one_mul]
          exact le_trans h.le (le_trans hηδ hδ1)
        linarith
    · exact le_refl 0
  have hTint_le : ∀ θ, Tint θ ≤ Tb θ := by
    intro θ
    simp only [hTint, hTb]
    split_ifs with h
    · have hsmall : ‖f θ‖ < ε' := by
        rw [hnormZ θ] at h
        rw [hη] at h
        have h2 : 0 < 2 / Real.sqrt N := by positivity
        calc ‖f θ‖ = (2 / Real.sqrt N * ‖f θ‖) / (2 / Real.sqrt N) := by field_simp
          _ < (2 * ε' / Real.sqrt N) / (2 / Real.sqrt N) := by
            exact div_lt_div_of_pos_right h h2
          _ = ε' := by field_simp
      have hind : smallInd x ε' θ = 1 := by
        unfold smallInd; rw [if_pos hsmall]
      rw [hind, one_mul]
      by_cases hf0 : f θ = 0
      · have : ‖Z θ‖ = 0 := by rw [hnormZ θ, hf0, norm_zero, mul_zero]
        rw [this, hf0]; simp; linarith
      · have hfpos : 0 < ‖f θ‖ := norm_pos_iff.mpr hf0
        rw [hnormZ θ, one_div, Real.log_inv, Real.log_mul (by positivity) hfpos.ne']
        have : -(Real.log (2 / Real.sqrt N)) = Real.log (Real.sqrt N / 2) := by
          rw [← Real.log_inv, inv_div]
        have habs : -Real.log ‖f θ‖ ≤ |Real.log ‖f θ‖| := neg_le_abs _
        linarith
    · exact hTb_nonneg θ
  -- integrability
  have hlogf := log_norm_evalCircle_ii x hx
  have hTb_ii : IntervalIntegrable Tb volume 0 (2 * π) := by
    have hdom : IntervalIntegrable (fun θ => (1 + Real.log (Real.sqrt N / 2)) + |Real.log ‖f θ‖|)
        volume 0 (2 * π) := intervalIntegrable_const.add hlogf.abs
    refine hdom.mono_fun ?_ ?_
    · exact ((smallInd_measurable x ε').mul (measurable_const.add
        ((evalCircle_continuous x).norm.measurable.log.abs))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      simp only [hTb, Real.norm_eq_abs]
      rw [abs_of_nonneg (hTb_nonneg θ), abs_of_nonneg (by positivity)]
      calc smallInd x ε' θ * (1 + Real.log (Real.sqrt N / 2) + |Real.log ‖f θ‖|)
          ≤ 1 * (1 + Real.log (Real.sqrt N / 2) + |Real.log ‖f θ‖|) := by
            apply mul_le_mul_of_nonneg_right (smallInd_le_one x ε' θ) (by positivity)
        _ = _ := by ring
  have hTint_meas : Measurable Tint := by
    simp only [hTint]
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt ((Zfun_continuous x 0).norm.measurable) measurable_const
    · exact measurable_const.add (measurable_const.div
        (Zfun_continuous x 0).norm.measurable).log
  have hTint_ii : IntervalIntegrable Tint volume 0 (2 * π) := by
    refine hTb_ii.mono_fun hTint_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun θ => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (hTint_nonneg θ), abs_of_nonneg (hTb_nonneg θ)]
    exact hTint_le θ
  -- main chain
  rw [lam_eq_cav hN1 x hx 0]
  have hphi := phiD_Zfun_ii x 0 hδ
  have hpsi := psiB_Zfun_ii x 0 hβ
  have hlogZ := log_norm_Zfun_ii hN1 x hx 0
  have hRHS_ii : IntervalIntegrable (fun θ => phiD δ (Z θ) - δ ^ 2 / (2 * β ^ 2)
      - 2 * Λ * psiB β (Z θ) - Tint θ) volume 0 (2 * π) :=
    ((hphi.sub intervalIntegrable_const).sub (hpsi.const_mul _)).sub hTint_ii
  have hpt : cav (fun θ => phiD δ (Z θ) - δ ^ 2 / (2 * β ^ 2) - 2 * Λ * psiB β (Z θ) - Tint θ)
      ≤ cav (fun θ => Real.log ‖Z θ‖) := by
    apply cav_mono_ae hRHS_ii hlogZ
    filter_upwards [Zfun_ne_zero_ae hN1 x hx 0] with θ hθ
    have := phiD_sub_log_le hηpos hηδ hδ1 hβ hθ
    simp only [hTint]
    linarith
  have hcav_split : cav (fun θ => phiD δ (Z θ) - δ ^ 2 / (2 * β ^ 2) - 2 * Λ * psiB β (Z θ)
      - Tint θ) = cav (fun θ => phiD δ (Z θ)) - δ ^ 2 / (2 * β ^ 2)
        - 2 * Λ * cav (fun θ => psiB β (Z θ)) - cav Tint := by
    rw [cav_sub ((hphi.sub intervalIntegrable_const).sub (hpsi.const_mul _)) hTint_ii,
      cav_sub (hphi.sub intervalIntegrable_const) (hpsi.const_mul _),
      cav_sub hphi intervalIntegrable_const, cav_const, cav_const_mul]
  -- bound on cav Tint
  have hTbound : cav Tint ≤ (1 + Real.log N) * cav (smallInd x ε')
      + Real.sqrt (cav (smallInd x ε')) * Real.sqrt (400 * N ^ 2) := by
    have h1 : cav Tint ≤ cav Tb := cav_mono hTint_ii hTb_ii hTint_le
    have h2 : cav Tb = (1 + Real.log (Real.sqrt N / 2)) * cav (smallInd x ε')
        + cav (fun θ => |smallInd x ε' θ * Real.log ‖f θ‖|) := by
      have hsplit : Tb = fun θ => (1 + Real.log (Real.sqrt N / 2)) * smallInd x ε' θ
          + |smallInd x ε' θ * Real.log ‖f θ‖| := by
        funext θ
        simp only [hTb]
        rw [abs_mul, abs_of_nonneg (smallInd_nonneg x ε' θ)]
        ring
      have hA : IntervalIntegrable (fun θ => |smallInd x ε' θ * Real.log ‖f θ‖|) volume 0 (2 * π) := by
        refine hlogf.abs.mono_fun ?_ ?_
        · exact ((smallInd_measurable x ε').mul
            ((evalCircle_continuous x).norm.measurable.log)).abs.aestronglyMeasurable
        · refine Filter.Eventually.of_forall (fun θ => ?_)
          simp only [Real.norm_eq_abs, abs_abs]
          rw [abs_mul, abs_of_nonneg (smallInd_nonneg x ε' θ)]
          calc smallInd x ε' θ * |Real.log ‖f θ‖| ≤ 1 * |Real.log ‖f θ‖| :=
                mul_le_mul_of_nonneg_right (smallInd_le_one x ε' θ) (abs_nonneg _)
            _ = |Real.log ‖f θ‖| := one_mul _
      rw [hsplit, cav_add ((smallInd_ii x ε').const_mul _) hA, cav_const_mul]
    have h3 : cav (fun θ => |smallInd x ε' θ * Real.log ‖f θ‖|)
        ≤ Real.sqrt (cav (smallInd x ε')) * Real.sqrt (400 * N ^ 2) := by
      have hCS := cav_mul_le_sqrt (F := smallInd x ε') (G := fun θ => Real.log ‖f θ‖)
        (by
          have : (fun θ => smallInd x ε' θ ^ 2) = smallInd x ε' := by
            funext θ; unfold smallInd; split_ifs <;> norm_num
          rw [this]; exact smallInd_ii x ε')
        (log_sq_intervalIntegrable x hx)
      have hsq : (fun θ => smallInd x ε' θ ^ 2) = smallInd x ε' := by
        funext θ; unfold smallInd; split_ifs <;> norm_num
      rw [hsq] at hCS
      refine le_trans hCS ?_
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact Real.sqrt_le_sqrt (log_sq_bound x hx)
    have h4 : Real.log (Real.sqrt N / 2) ≤ Real.log N := by
      apply Real.log_le_log (by positivity)
      have : Real.sqrt N ≤ N := by
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [show (1:ℝ) ≤ N by exact_mod_cast hN1]
      linarith
    have hμ : 0 ≤ cav (smallInd x ε') := cav_nonneg (smallInd_nonneg x ε')
    nlinarith [h1, h2, h3, h4, hμ, mul_le_mul_of_nonneg_right (add_le_add_left h4 1) hμ]
  rw [hcav_split] at hpt
  have hΛnn : 0 ≤ Λ := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hηpos, one_mul]
    linarith
  linarith

/- ### Expected smoothed log-average (Lindeberg) -/

/-- The error in `EF_bound`. -/
def eBound (n : ℕ) (δ εb : ℝ) : ℝ :=
  (Real.sqrt (2 * εb) + 20 / (Real.sqrt (n + 1) * εb)) / (2 * δ)
    + 2 * εb * (2 * (|Real.log δ| + 1))
    + (10 * (2 / Real.sqrt (n + 1)) / δ ^ 3
      + 20 / ((n + 1) * εb) * (1 / δ ^ 2 + 10 * (n + 1) * (2 / Real.sqrt (n + 1)) / δ ^ 3))

lemma cubeAvg_phiD_W_abs_le {N : ℕ} (hN : 1 ≤ N) (s θ : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    |cubeAvg N (fun x => phiD δ (Wfun (rho N s) x θ)) - kappa δ| ≤ 2 * (|Real.log δ| + 1) := by
  have hW : |cubeAvg N (fun x => phiD δ (Wfun (rho N s) x θ))| ≤ |Real.log δ| + 1 / 2 := by
    have hpt : ∀ x : Fin N → Bool, |phiD δ (Wfun (rho N s) x θ)|
        ≤ |Real.log δ| + ‖Wfun (rho N s) x θ‖ ^ 2 / 2 := by
      intro x
      obtain ⟨h1, h2⟩ := phiD_bounds hδ hδ1 (Wfun (rho N s) x θ)
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log δ)
        have : 0 ≤ ‖Wfun (rho N s) x θ‖ ^ 2 / 2 := by positivity
        linarith
      · have := le_abs_self (Real.log δ)
        linarith [abs_nonneg (Real.log δ)]
    calc |cubeAvg N (fun x => phiD δ (Wfun (rho N s) x θ))|
        ≤ cubeAvg N (fun x => |phiD δ (Wfun (rho N s) x θ)|) := abs_cubeAvg_le _
      _ ≤ cubeAvg N (fun x => |Real.log δ| + ‖Wfun (rho N s) x θ‖ ^ 2 / 2) := cubeAvg_mono hpt
      _ = |Real.log δ| + 1 / 2 := by
        rw [cubeAvg_add, cubeAvg_const]
        have h := cubeAvg_norm_sq_Wfun (N := N) (rho N s) θ
        have hsum : ∑ k : Fin N, rho N s k ^ 2 = 1 := by
          rw [Fin.sum_univ_eq_sum_range (fun k => rho N s k ^ 2)]
          exact sum_rho_sq hN s
        have : cubeAvg N (fun x => ‖Wfun (rho N s) x θ‖ ^ 2 / 2)
            = cubeAvg N (fun x => (1 / 2) * ‖Wfun (rho N s) x θ‖ ^ 2) := by
          congr 1; funext x; ring
        rw [this, cubeAvg_smul, h, hsum]; ring
  have hk := kappa_abs_le hδ hδ1
  calc |cubeAvg N (fun x => phiD δ (Wfun (rho N s) x θ)) - kappa δ|
      ≤ |cubeAvg N (fun x => phiD δ (Wfun (rho N s) x θ))| + |kappa δ| := abs_sub _ _
    _ ≤ (|Real.log δ| + 1 / 2) + (|Real.log δ| + 1) := add_le_add hW hk
    _ ≤ 2 * (|Real.log δ| + 1) := by linarith [abs_nonneg (Real.log δ)]

lemma EF_bound {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {δ εb : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hεb : 0 < εb) :
    |cubeAvg (n + 1) (fun x => cav (fun θ => phiD δ (Zfun x s θ))) - kappa δ| ≤ eBound n δ εb := by
  set N := n + 1 with hNdef
  have hN : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  set ρ := rho N s with hρ
  set m := mfun N ρ with hm
  -- swap the cube average and the circle average
  have hswap := cubeAvg_cav (N := N) (fun x θ => phiD δ (Zfun x s θ)) (fun x => phiD_Zfun_ii x s hδ)
  rw [hswap]
  set g : ℝ → ℝ := fun θ => cubeAvg N (fun x => phiD δ (Zfun x s θ)) with hg
  have hg_cont : Continuous g := by
    simp only [hg, cubeAvg]
    refine Continuous.div_const ?_ _
    refine continuous_finsetSum _ (fun x _ => ?_)
    exact (phiD_continuous hδ).comp (Zfun_continuous x s)
  have hsub : cav g - kappa δ = cav (fun θ => g θ - kappa δ) := by
    rw [cav_sub (hg_cont.intervalIntegrable _ _) intervalIntegrable_const, cav_const]
  rw [hsub]
  refine le_trans (abs_cav_le _) ?_
  -- pointwise bound
  set bad : ℝ → ℝ := fun θ => if |Real.sin θ| < εb then 1 else 0 with hbad
  set cap : ℝ := 2 * (|Real.log δ| + 1) with hcap
  set lind : ℝ := 10 * (2 / Real.sqrt (n + 1)) / δ ^ 3
      + 20 / ((n + 1) * εb) * (1 / δ ^ 2 + 10 * (n + 1) * (2 / Real.sqrt (n + 1)) / δ ^ 3)
    with hlind
  have hlind_nn : 0 ≤ lind := by positivity
  have hcap_nn : 0 ≤ cap := by positivity
  have hpt : ∀ θ, |g θ - kappa δ| ≤ ‖m θ‖ / (2 * δ) + (bad θ * cap + lind) := by
    intro θ
    have hlip : |g θ - cubeAvg N (fun x => phiD δ (Wfun ρ x θ))| ≤ ‖m θ‖ / (2 * δ) := by
      simp only [hg]
      rw [← cubeAvg_sub]
      refine le_trans (abs_cubeAvg_le _) ?_
      refine le_trans (cubeAvg_mono (fun x => ?_)) (le_of_eq (cubeAvg_const N _))
      have := phiD_lipschitz hδ (Zfun x s θ) (Wfun ρ x θ)
      simp only [Zfun] at this ⊢
      rw [add_sub_cancel_left] at this
      exact this
    have hmain : |cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) - kappa δ| ≤ bad θ * cap + lind := by
      by_cases hθ : |Real.sin θ| < εb
      · have hb : bad θ = 1 := by simp only [hbad]; rw [if_pos hθ]
        rw [hb, one_mul]
        have := cubeAvg_phiD_W_abs_le hN s θ hδ hδ1
        linarith
      · have hb : bad θ = 0 := by simp only [hbad]; rw [if_neg hθ]
        rw [hb, zero_mul, zero_add]
        push_neg at hθ
        have hsin : Real.sin θ ≠ 0 := by
          intro h; rw [h, abs_zero] at hθ; linarith
        have hsinpos : 0 < |Real.sin θ| := abs_pos.mpr hsin
        have hL := lindeberg ρ (fun k => rho_nonneg N s k) (sum_rho_sq hN s)
          (2 / Real.sqrt (n + 1)) (fun k hk => by
            have := rho_le (n := n) hn hs (k := k) (by omega)
            simpa [hρ, hNdef] using this)
          θ δ hδ hδ1 (20 / ((n + 1) * εb)) (fun J hJ => by
            have := P_bound hn hs θ hsin (J := J) (by omega)
            refine le_trans this ?_
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact mul_le_mul_of_nonneg_left hθ (by positivity))
        have hcast : ((N : ℕ) : ℝ) = (n : ℝ) + 1 := by simp [hNdef]
        rw [hcast] at hL
        simpa [hlind] using hL
    calc |g θ - kappa δ|
        = |(g θ - cubeAvg N (fun x => phiD δ (Wfun ρ x θ)))
            + (cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) - kappa δ)| := by ring_nf
      _ ≤ |g θ - cubeAvg N (fun x => phiD δ (Wfun ρ x θ))|
            + |cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) - kappa δ| := abs_add_le _ _
      _ ≤ ‖m θ‖ / (2 * δ) + (bad θ * cap + lind) := add_le_add hlip hmain
  -- integrate
  have hm_cont : Continuous m := mfun_continuous N ρ
  have hbad_meas : Measurable bad := by
    simp only [hbad]
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (Real.continuous_sin.abs.measurable) measurable_const
  have hbad_nn : ∀ θ, 0 ≤ bad θ := fun θ => by simp only [hbad]; split_ifs <;> norm_num
  have hbad_le : ∀ θ, bad θ ≤ 1 := fun θ => by simp only [hbad]; split_ifs <;> norm_num
  have hbad_ii : IntervalIntegrable bad volume 0 (2 * π) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun hbad_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun θ => ?_)
    simp only [Real.norm_eq_abs, abs_one]
    rw [abs_of_nonneg (hbad_nn θ)]; exact hbad_le θ
  have hmnorm_ii : IntervalIntegrable (fun θ => ‖m θ‖) volume 0 (2 * π) :=
    hm_cont.norm.intervalIntegrable _ _
  have hA_ii : IntervalIntegrable (fun θ => |g θ - kappa δ|) volume 0 (2 * π) :=
    ((hg_cont.sub continuous_const).abs).intervalIntegrable _ _
  have hB_ii : IntervalIntegrable (fun θ => ‖m θ‖ / (2 * δ) + (bad θ * cap + lind))
      volume 0 (2 * π) :=
    (hmnorm_ii.div_const _).add ((hbad_ii.mul_const _).add intervalIntegrable_const)
  refine le_trans (cav_mono hA_ii hB_ii hpt) ?_
  rw [cav_add (hmnorm_ii.div_const _) ((hbad_ii.mul_const _).add intervalIntegrable_const),
    cav_add (hbad_ii.mul_const _) intervalIntegrable_const, cav_const]
  -- the three averages
  have hcav_div : cav (fun θ => ‖m θ‖ / (2 * δ)) = cav (fun θ => ‖m θ‖) / (2 * δ) := by
    have : (fun θ => ‖m θ‖ / (2 * δ)) = fun θ => (1 / (2 * δ)) * ‖m θ‖ := by
      funext θ; ring
    rw [this, cav_const_mul]; ring
  have hcav_bad : cav (fun θ => bad θ * cap) = cap * cav bad := by
    have : (fun θ => bad θ * cap) = fun θ => cap * bad θ := by funext θ; ring
    rw [this, cav_const_mul]
  rw [hcav_div, hcav_bad]
  have hbadcav : cav bad ≤ 2 * εb := cav_bad_theta hεb
  -- cav ‖m‖ ≤ √(2 εb) + 20/(√(n+1) εb)
  have hmcav : cav (fun θ => ‖m θ‖) ≤ Real.sqrt (2 * εb) + 20 / (Real.sqrt (n + 1) * εb) := by
    have hsplit : ∀ θ, ‖m θ‖ ≤ |bad θ * ‖m θ‖| + 20 / (Real.sqrt (n + 1) * εb) := by
      intro θ
      by_cases hθ : |Real.sin θ| < εb
      · have hb : bad θ = 1 := by simp only [hbad]; rw [if_pos hθ]
        rw [hb, one_mul, abs_of_nonneg (norm_nonneg _)]
        have : 0 ≤ 20 / (Real.sqrt (n + 1) * εb) := by positivity
        linarith
      · push_neg at hθ
        have hsin2 : Real.sin (θ / 2) ≠ 0 := by
          intro h
          have := abs_sin_half_ge (θ := θ)
          rw [h, abs_zero] at this
          linarith
        have hmb := m_bound hn hs θ hsin2
        have hhalf : εb / 2 ≤ |Real.sin (θ / 2)| := by
          have := abs_sin_half_ge (θ := θ); linarith
        have : 10 / (Real.sqrt (n + 1) * |Real.sin (θ / 2)|) ≤ 20 / (Real.sqrt (n + 1) * εb) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have hsq : 0 < Real.sqrt (n + 1) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hhalf hsq.le]
        have hmb' : ‖m θ‖ ≤ 20 / (Real.sqrt (n + 1) * εb) := by
          simp only [hm, hρ, hNdef] at hmb ⊢
          push_cast at hmb ⊢
          linarith
        linarith [abs_nonneg (bad θ * ‖m θ‖)]
    have hbm_ii : IntervalIntegrable (fun θ => |bad θ * ‖m θ‖|) volume 0 (2 * π) :=
      (hbad_ii.mul_continuousOn hm_cont.norm.continuousOn).abs
    have h1 : cav (fun θ => ‖m θ‖) ≤ cav (fun θ => |bad θ * ‖m θ‖| + 20 / (Real.sqrt (n + 1) * εb)) :=
      cav_mono hmnorm_ii (hbm_ii.add intervalIntegrable_const) hsplit
    rw [cav_add hbm_ii intervalIntegrable_const, cav_const] at h1
    have hCS := cav_mul_le_sqrt (F := bad) (G := fun θ => ‖m θ‖)
      (by
        have : (fun θ => bad θ ^ 2) = bad := by
          funext θ; simp only [hbad]; split_ifs <;> norm_num
        rw [this]; exact hbad_ii)
      ((hm_cont.norm.pow 2).intervalIntegrable _ _)
    have hsq : (fun θ => bad θ ^ 2) = bad := by
      funext θ; simp only [hbad]; split_ifs <;> norm_num
    rw [hsq] at hCS
    have hm2 : cav (fun θ => ‖m θ‖ ^ 2) = 1 := cav_norm_sq_mfun hN s
    rw [hm2, Real.sqrt_one, mul_one] at hCS
    have : Real.sqrt (cav bad) ≤ Real.sqrt (2 * εb) := Real.sqrt_le_sqrt hbadcav
    linarith
  have h2δ : 0 < 2 * δ := by positivity
  unfold eBound
  have e1 : cav (fun θ => ‖m θ‖) / (2 * δ) ≤
      (Real.sqrt (2 * εb) + 20 / (Real.sqrt (n + 1) * εb)) / (2 * δ) :=
    div_le_div_of_nonneg_right hmcav h2δ.le
  have e2 : cap * cav bad ≤ 2 * εb * cap := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hbadcav hcap_nn
  simp only [hcap] at e2
  linarith

/- ### Expected smoothing proxy (Littlewood–Offord) -/

lemma EK_bound {N : ℕ} (hN : 1 ≤ N) {β β₂ : ℝ} (hβ : 0 < β) (hβ₂ : 0 < β₂) :
    cubeAvg N (fun x => cav (fun θ => psiB β (Zfun x 0 θ))) ≤
      2 * β₂ + 2 / Real.sqrt N + β ^ 2 / β₂ ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  rw [cubeAvg_cav (N := N) (fun x θ => psiB β (Zfun x 0 θ)) (fun x => psiB_Zfun_ii x 0 hβ)]
  apply cav_le_of_le_const
  · refine Continuous.intervalIntegrable ?_ _ _
    simp only [cubeAvg]
    refine Continuous.div_const ?_ _
    exact continuous_finsetSum _ (fun x _ => (psiB_continuous hβ).comp (Zfun_continuous x 0))
  · intro θ
    classical
    have hpt : ∀ x : Fin N → Bool, psiB β (Zfun x 0 θ) ≤
        (if ‖Zfun x 0 θ‖ < β₂ then 1 else 0) + β ^ 2 / β₂ ^ 2 :=
      fun x => psiB_le_indicator hβ hβ₂ _
    refine le_trans (cubeAvg_mono hpt) ?_
    rw [cubeAvg_add, cubeAvg_const, ← cubeProb_eq_cubeAvg]
    gcongr
    -- ‖Z‖ < β₂ ↔ ‖∑ sgn e + ∑ e‖ < β₂ √N
    have hZ : ∀ x : Fin N → Bool, Zfun x 0 θ =
        ((1 / Real.sqrt N : ℝ) : ℂ) * (∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ
          + ∑ k : Fin N, ex k θ) := by
      intro x
      unfold Zfun Wfun mfun
      simp only [rho_zero]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> push_cast <;> ring
    have hev : ∀ x : Fin N → Bool, ‖Zfun x 0 θ‖ < β₂ →
        ‖∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + ∑ k : Fin N, ex k θ‖ < β₂ * Real.sqrt N := by
      intro x hx
      rw [hZ x, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hx
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hsqN] at hx
      linarith
    refine le_trans (cubeProb_mono hev) ?_
    refine le_trans (lo_bound hN θ _ (β₂ * Real.sqrt N) (by positivity)) (le_of_eq ?_)
    field_simp

/- ### Concentration -/

/-- Variance proxy for `F_δ` (from `sum_mgDiff_sq_le` with `L₁ = 1/(2δ)`, `L₂ = 3/δ²`). -/
def vF (n : ℕ) (δ : ℝ) : ℝ :=
  3 * (1 / (2 * δ)) ^ 2 * (2 / Real.sqrt (n + 1)) ^ 2 * (((n + 1 : ℕ) : ℝ) / (Nat.sqrt (n + 1)) + 1)
    + 12 * (3 / δ ^ 2) ^ 2 * (2 / Real.sqrt (n + 1)) ^ 4 * (Nat.sqrt (n + 1)) * ((n + 1 : ℕ) : ℝ)
    + (3 / δ ^ 2) ^ 2 * (2 / Real.sqrt (n + 1)) ^ 4 * ((n + 1 : ℕ) : ℝ)

/-- Variance proxy for `K_β` (with `L₁ = 1/β`, `L₂ = 10/β²`). -/
def vK (n : ℕ) (β : ℝ) : ℝ :=
  3 * (1 / β) ^ 2 * (2 / Real.sqrt (n + 1)) ^ 2 * (((n + 1 : ℕ) : ℝ) / (Nat.sqrt (n + 1)) + 1)
    + 12 * (10 / β ^ 2) ^ 2 * (2 / Real.sqrt (n + 1)) ^ 4 * (Nat.sqrt (n + 1)) * ((n + 1 : ℕ) : ℝ)
    + (10 / β ^ 2) ^ 2 * (2 / Real.sqrt (n + 1)) ^ 4 * ((n + 1 : ℕ) : ℝ)

lemma vF_pos (n : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < vF n δ := by
  unfold vF
  have : 0 < (Nat.sqrt (n + 1) : ℝ) := by exact_mod_cast Nat.sqrt_pos.mpr (by omega)
  positivity

lemma vK_pos (n : ℕ) {β : ℝ} (hβ : 0 < β) : 0 < vK n β := by
  unfold vK
  have : 0 < (Nat.sqrt (n + 1) : ℝ) := by exact_mod_cast Nat.sqrt_pos.mpr (by omega)
  positivity

lemma F_conc {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    cubeProb (n + 1) (fun x => t ≤ |cav (fun θ => phiD δ (Zfun x s θ))
        - cubeAvg (n + 1) (fun y => cav (fun θ => phiD δ (Zfun y s θ)))|)
      ≤ 2 * Real.exp (-t ^ 2 / (2 * vF n δ)) := by
  apply cube_tail _ _ _ (vF_pos n hδ) ht
  intro x
  have hL : 0 < Nat.sqrt (n + 1) := Nat.sqrt_pos.mpr (by omega)
  have h := sum_mgDiff_sq_le (N := n + 1) hL (rho (n + 1) s) (2 / Real.sqrt (n + 1))
    (fun k => rho_nonneg _ s k) (fun k hk => by
      have := rho_le (n := n) hn hs (k := k) hk
      simpa using this)
    (mfun (n + 1) (rho (n + 1) s)) (mfun_continuous _ _) (phiD δ) (gphiD δ) (1 / (2 * δ))
    (3 / δ ^ 2) (phiD_continuous hδ) (gphiD_continuous hδ) (fun z w => phiD_taylor2 hδ z w)
    (fun z => gphiD_norm_le hδ z) (fun z w => gphiD_lip hδ z w) x
  simpa [vF, Zfun] using h

lemma K_conc {n : ℕ} (hn : 1 ≤ n) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    cubeProb (n + 1) (fun x => t ≤ |cav (fun θ => psiB β (Zfun x 0 θ))
        - cubeAvg (n + 1) (fun y => cav (fun θ => psiB β (Zfun y 0 θ)))|)
      ≤ 2 * Real.exp (-t ^ 2 / (2 * vK n β)) := by
  apply cube_tail _ _ _ (vK_pos n hβ) ht
  intro x
  have hL : 0 < Nat.sqrt (n + 1) := Nat.sqrt_pos.mpr (by omega)
  have hs : |(0 : ℝ)| ≤ 1 / (2 * n) := by rw [abs_zero]; positivity
  have h := sum_mgDiff_sq_le (N := n + 1) hL (rho (n + 1) 0) (2 / Real.sqrt (n + 1))
    (fun k => rho_nonneg _ 0 k) (fun k hk => by
      have := rho_le (n := n) hn hs (k := k) hk
      simpa using this)
    (mfun (n + 1) (rho (n + 1) 0)) (mfun_continuous _ _) (psiB β) (gpsiB β) (1 / β)
    (10 / β ^ 2) (psiB_continuous hβ) (gpsiB_continuous hβ) (fun z w => psiB_taylor2 hβ z w)
    (fun z => gpsiB_norm_le hβ z) (fun z w => gpsiB_lip hβ z w) x
  simpa [vK, Zfun] using h

end

end E522

end

/- ## Section: `Main` -/

section

/-
# Assembly: complete convergence of `2 R_n / n` on the cube

Parameters (with `N = n + 1`): `δ = N^{-1/20}`, `β = N^{-1/40}`, `β₂ = N^{-1/80}`,
`t = εb = N^{-1/8}`, `K = 10 (⌊log₂ N⌋ + 1)`, `ε' = N^{-40K}/2`.
On the good event (nonzero polynomial, the smoothed functionals are within `t` of their means,
and the small-value set of `f` on the unit circle has measure `≤ N^{-4}`) the deterministic
lemma `det_main` at radii `e^{±c/n}, 1` gives `|2R/n − 1| ≤ c/2 + 4 Err_n / c` with
`Err_n → 0`; the bad event has summable probability.
-/

open Real Complex MeasureTheory Filter Topology

namespace E522

noncomputable section

/- ### Parameters -/

/-- `N = n + 1` as a real number. -/
abbrev NN (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

def pδ (n : ℕ) : ℝ := NN n ^ (-(1 / 20 : ℝ))
def pβ (n : ℕ) : ℝ := NN n ^ (-(1 / 40 : ℝ))
def pβ₂ (n : ℕ) : ℝ := NN n ^ (-(1 / 80 : ℝ))
def pt (n : ℕ) : ℝ := NN n ^ (-(1 / 8 : ℝ))
def pK (n : ℕ) : ℕ := 10 * (Nat.log 2 (n + 1) + 1)
def pε' (n : ℕ) : ℝ := NN n ^ (-(40 * (pK n : ℝ))) / 2

lemma NN_pos (n : ℕ) : 0 < NN n := by unfold NN; positivity
lemma one_le_NN (n : ℕ) : 1 ≤ NN n := by unfold NN; exact_mod_cast Nat.succ_pos n
lemma NN_eq (n : ℕ) : NN n = (n : ℝ) + 1 := by unfold NN; push_cast; ring

lemma pδ_pos (n : ℕ) : 0 < pδ n := Real.rpow_pos_of_pos (NN_pos n) _
lemma pβ_pos (n : ℕ) : 0 < pβ n := Real.rpow_pos_of_pos (NN_pos n) _
lemma pβ₂_pos (n : ℕ) : 0 < pβ₂ n := Real.rpow_pos_of_pos (NN_pos n) _
lemma pt_pos (n : ℕ) : 0 < pt n := Real.rpow_pos_of_pos (NN_pos n) _
lemma pε'_pos (n : ℕ) : 0 < pε' n := by
  unfold pε'; exact div_pos (Real.rpow_pos_of_pos (NN_pos n) _) (by norm_num)

lemma rpow_neg_le_one (n : ℕ) {a : ℝ} (ha : 0 ≤ a) : NN n ^ (-a) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_NN n) (by linarith)

lemma pδ_le_one (n : ℕ) : pδ n ≤ 1 := rpow_neg_le_one n (by norm_num)

lemma sqrt_NN (n : ℕ) : Real.sqrt (NN n) = Real.sqrt ((n : ℝ) + 1) := by rw [NN_eq]

/-- `η = 2ε'/√N ≤ δ`. -/
lemma eta_le_delta (n : ℕ) : 2 * pε' n / Real.sqrt (NN n) ≤ pδ n := by
  have hN := one_le_NN n
  have hsq : 1 ≤ Real.sqrt (NN n) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hN
  unfold pε' pδ
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  calc NN n ^ (-(40 * (pK n : ℝ))) / Real.sqrt (NN n) ≤ NN n ^ (-(40 * (pK n : ℝ))) :=
        div_le_self (Real.rpow_nonneg (NN_pos n).le _) hsq
    _ ≤ NN n ^ (-(1 / 20 : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hN
        have : (1 : ℝ) ≤ pK n := by unfold pK; exact_mod_cast (by omega : 1 ≤ 10 * (Nat.log 2 (n + 1) + 1))
        linarith

/- ### The error term and the good event -/

/-- The total error `E_n`. -/
def Err (n : ℕ) : ℝ :=
  eBound n (pδ n) (pt n) + pt n + pδ n ^ 2 / (2 * pβ n ^ 2)
    + 2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
        * (2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n)
    + ((1 + Real.log (NN n)) * NN n ^ (-(4 : ℝ))
        + Real.sqrt (NN n ^ (-(4 : ℝ))) * Real.sqrt (400 * NN n ^ 2))

/-- Smoothed log-average at radius `e^s`. -/
def Fs (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) : ℝ := cav (fun θ => phiD (pδ n) (Zfun x s θ))

/-- Smoothing proxy at radius `1`. -/
def Ks (n : ℕ) (x : Fin (n + 1) → Bool) : ℝ := cav (fun θ => psiB (pβ n) (Zfun x 0 θ))

/-- The good event at radius parameter `c` (radii `e^{±c/n}` and `1`). -/
def Good (n : ℕ) (c : ℝ) (x : Fin (n + 1) → Bool) : Prop :=
  poly x ≠ 0 ∧
  |Fs n (c / n) x - cubeAvg (n + 1) (Fs n (c / n))| < pt n ∧
  |Fs n (-(c / n)) x - cubeAvg (n + 1) (Fs n (-(c / n)))| < pt n ∧
  |Fs n 0 x - cubeAvg (n + 1) (Fs n 0)| < pt n ∧
  |Ks n x - cubeAvg (n + 1) (Ks n)| < pt n ∧
  cav (smallInd x (pε' n)) ≤ NN n ^ (-(4 : ℝ))

lemma Err_nonneg_parts (n : ℕ) :
    0 ≤ Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n))) := by
  apply Real.log_nonneg
  have hη : 0 < 2 * pε' n / Real.sqrt (NN n) := by
    have := pε'_pos n; have := Real.sqrt_pos.mpr (NN_pos n); positivity
  rw [le_div_iff₀ hη, one_mul]
  have := eta_le_delta n
  have := pδ_pos n
  linarith

/-- Deterministic consequence of the good event. -/
lemma good_bound {n : ℕ} (hn : 3 ≤ n) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (x : Fin (n + 1) → Bool) (hG : Good n c x) :
    |(2 * rootCount x : ℝ) / n - 1| ≤ c / 2 + 4 * Err n / c := by
  obtain ⟨hx, hFp, hFm, hF0, hK, hμ⟩ := hG
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN1 : 1 ≤ n + 1 := by omega
  have hN4 : 4 ≤ n + 1 := by omega
  have hδ := pδ_pos n
  have hδ1 := pδ_le_one n
  have hβ := pβ_pos n
  have hβ₂ := pβ₂_pos n
  have ht := pt_pos n
  have hh : 0 < c / n := div_pos hc hnpos
  have hsh : |c / n| ≤ 1 / (2 * n) := by
    rw [abs_of_pos hh, div_le_div_iff₀ hnpos (by positivity)]
    nlinarith
  have hsmh : |-(c / n)| ≤ 1 / (2 * n) := by rwa [abs_neg]
  have hs0 : |(0 : ℝ)| ≤ 1 / (2 * n) := by rw [abs_zero]; positivity
  -- nonnegativity of the parts of `Err`
  have hΛ := Err_nonneg_parts n
  have hC : 0 ≤ 2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n := by
    have := Real.sqrt_nonneg (NN n); positivity
  have hD : 0 ≤ (1 + Real.log (NN n)) * NN n ^ (-(4 : ℝ))
      + Real.sqrt (NN n ^ (-(4 : ℝ))) * Real.sqrt (400 * NN n ^ 2) := by
    have := Real.log_nonneg (one_le_NN n)
    have := Real.rpow_nonneg (NN_pos n).le (-(4 : ℝ))
    positivity
  have hA : 0 ≤ pδ n ^ 2 / (2 * pβ n ^ 2) := by positivity
  have hΛC : 0 ≤ 2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
      * (2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n) := by positivity
  -- expected values
  have hE : ∀ s : ℝ, |s| ≤ 1 / (2 * n) →
      |cubeAvg (n + 1) (Fs n s) - kappa (pδ n)| ≤ eBound n (pδ n) (pt n) := fun s hs =>
    EF_bound hn1 hs hδ hδ1 ht
  -- upper bounds at ±h
  have hup : ∀ s : ℝ, |s| ≤ 1 / (2 * n) →
      |Fs n s x - cubeAvg (n + 1) (Fs n s)| < pt n →
        Lam x s ≤ (kappa (pδ n) - Real.log 2) + Err n := by
    intro s hs hdev
    have h1 : Lam x s ≤ Fs n s x - Real.log 2 := lam_le_cav_phiD hN1 x hx s hδ
    have h3 := (abs_lt.mp hdev).2
    have h4 := (abs_le.mp (hE s hs)).2
    unfold Err
    linarith
  have hUp := hup (c / n) hsh hFp
  have hDn := hup (-(c / n)) hsmh hFm
  -- lower bound at 0
  have hLo : (kappa (pδ n) - Real.log 2) - Err n ≤ Lam x 0 := by
    have hlow := lam_zero_ge (N := n + 1) hN4 x hx (pε'_pos n)
      (by simpa [NN] using eta_le_delta n) hδ1 hβ
    have hK_le : Ks n x ≤ 2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n := by
      have hEK := EK_bound (N := n + 1) hN1 hβ hβ₂
      have := (abs_lt.mp hK).2
      have hKs : cubeAvg (n + 1) (Ks n) = cubeAvg (n + 1)
          (fun x => cav (fun θ => psiB (pβ n) (Zfun x 0 θ))) := rfl
      rw [hKs] at this
      simp only [NN] at hEK ⊢
      linarith
    have hμ0 : 0 ≤ cav (smallInd x (pε' n)) := cav_nonneg (smallInd_nonneg x _)
    have hT : (1 + Real.log (((n + 1 : ℕ) : ℝ))) * cav (smallInd x (pε' n))
        + Real.sqrt (cav (smallInd x (pε' n))) * Real.sqrt (400 * ((n + 1 : ℕ) : ℝ) ^ 2)
        ≤ (1 + Real.log (NN n)) * NN n ^ (-(4 : ℝ))
          + Real.sqrt (NN n ^ (-(4 : ℝ))) * Real.sqrt (400 * NN n ^ 2) := by
      have hlog : 0 ≤ 1 + Real.log (NN n) := by
        have := Real.log_nonneg (one_le_NN n); linarith
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hμ hlog
      · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hμ) (Real.sqrt_nonneg _)
    have hΛK : 2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n))) * Ks n x ≤
        2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
          * (2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n) :=
      mul_le_mul_of_nonneg_left hK_le (by positivity)
    have h3 := (abs_lt.mp hF0).1
    have h4 := (abs_le.mp (hE 0 hs0)).1
    have hF0v : Fs n 0 x = cav (fun θ => phiD (pδ n) (Zfun x 0 θ)) := rfl
    have hKv : Ks n x = cav (fun θ => psiB (pβ n) (Zfun x 0 θ)) := rfl
    rw [← hF0v, ← hKv] at hlow
    unfold Err
    simp only [NN] at hT hΛK hlow ⊢
    linarith
  -- deterministic main lemma
  have hdet := det_main x hx (c / n) (kappa (pδ n) - Real.log 2) (Err n) hh hUp hDn hLo
  have hR : |(2 * rootCount x : ℝ) / n - 1| = 2 / n * |(rootCount x : ℝ) - n / 2| := by
    rw [show (2 * rootCount x : ℝ) / n - 1 = 2 / n * ((rootCount x : ℝ) - n / 2) by
      field_simp]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / n)]
  rw [hR]
  calc 2 / n * |(rootCount x : ℝ) - n / 2|
      ≤ 2 / n * ((n : ℝ) ^ 2 * (c / n) / 4 + 2 * Err n / (c / n)) :=
        mul_le_mul_of_nonneg_left hdet (by positivity)
    _ = c / 2 + 4 * Err n / c := by
        field_simp; ring

/- ### Probability of the bad event -/

/-- Bound on the probability of the bad event. -/
def Bnd (n : ℕ) : ℝ :=
  (1 / 2) ^ (n + 1) + 3 * (2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))))
    + 2 * Real.exp (-(pt n) ^ 2 / (2 * vK n (pβ n)))
    + NN n ^ (4 : ℝ) * ((1 / 2) ^ pK n + 3 ^ pK n * pK n * (2 * pε' n) ^ ((1 : ℝ) / pK n))

lemma two_pε'_lt_one {n : ℕ} (hn : 1 ≤ n) : 2 * pε' n < 1 := by
  unfold pε'
  rw [mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · unfold NN; push_cast; have : (1:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  · have : (1 : ℝ) ≤ pK n := by
      unfold pK; exact_mod_cast (by omega : 1 ≤ 10 * (Nat.log 2 (n + 1) + 1))
    linarith

lemma prob_bad {n : ℕ} (hn : 1 ≤ n) (hK : pK n ≤ n + 1) {c : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) :
    cubeProb (n + 1) (fun x => ¬ Good n c x) ≤ Bnd n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh : 0 < c / n := div_pos hc hnpos
  have hsh : |c / n| ≤ 1 / (2 * n) := by
    rw [abs_of_pos hh, div_le_div_iff₀ hnpos (by positivity)]
    nlinarith
  have hsmh : |-(c / n)| ≤ 1 / (2 * n) := by rwa [abs_neg]
  have hs0 : |(0 : ℝ)| ≤ 1 / (2 * n) := by rw [abs_zero]; positivity
  -- decompose the bad event
  have hsub : ∀ x : Fin (n + 1) → Bool, ¬ Good n c x →
      ((∀ k, x k = false) ∨ pt n ≤ |Fs n (c / n) x - cubeAvg (n + 1) (Fs n (c / n))|) ∨
      (pt n ≤ |Fs n (-(c / n)) x - cubeAvg (n + 1) (Fs n (-(c / n)))| ∨
        pt n ≤ |Fs n 0 x - cubeAvg (n + 1) (Fs n 0)|) ∨
      (pt n ≤ |Ks n x - cubeAvg (n + 1) (Ks n)| ∨
        NN n ^ (-(4 : ℝ)) < cav (smallInd x (pε' n))) := by
    intro x hx
    unfold Good at hx
    by_cases h0 : poly x = 0
    · left; left
      intro k
      by_contra hk
      exact poly_ne_zero_of x k (by simpa using hk) h0
    · simp only [not_and_or, not_lt, not_le] at hx
      rcases hx with h | h | h | h | h | h
      · exact absurd h0 (by simpa using h)
      · left; right; exact h
      · right; left; left; exact h
      · right; left; right; exact h
      · right; right; left; exact h
      · right; right; right; exact h
  refine le_trans (cubeProb_mono hsub) ?_
  refine le_trans (cubeProb_or_le _ _) ?_
  have e1 := cubeProb_or_le (N := n + 1) (fun x => ∀ k, x k = false)
    (fun x => pt n ≤ |Fs n (c / n) x - cubeAvg (n + 1) (Fs n (c / n))|)
  have e2 := cubeProb_or_le (N := n + 1)
    (fun x => (pt n ≤ |Fs n (-(c / n)) x - cubeAvg (n + 1) (Fs n (-(c / n)))| ∨
        pt n ≤ |Fs n 0 x - cubeAvg (n + 1) (Fs n 0)|))
    (fun x => (pt n ≤ |Ks n x - cubeAvg (n + 1) (Ks n)| ∨
        NN n ^ (-(4 : ℝ)) < cav (smallInd x (pε' n))))
  have e3 := cubeProb_or_le (N := n + 1)
    (fun x => pt n ≤ |Fs n (-(c / n)) x - cubeAvg (n + 1) (Fs n (-(c / n)))|)
    (fun x => pt n ≤ |Fs n 0 x - cubeAvg (n + 1) (Fs n 0)|)
  have e4 := cubeProb_or_le (N := n + 1)
    (fun x => pt n ≤ |Ks n x - cubeAvg (n + 1) (Ks n)|)
    (fun x => NN n ^ (-(4 : ℝ)) < cav (smallInd x (pε' n)))
  have p0 : cubeProb (n + 1) (fun x => ∀ k, x k = false) = (1 / 2) ^ (n + 1) :=
    cubeProb_all_false (n + 1)
  have p1 := F_conc hn hsh (pδ_pos n) (pt_pos n).le
  have p2 := F_conc hn hsmh (pδ_pos n) (pt_pos n).le
  have p3 := F_conc hn hs0 (pδ_pos n) (pt_pos n).le
  have p4 := K_conc hn (pβ_pos n) (pt_pos n).le
  -- small values: Markov + separation
  have p5 : cubeProb (n + 1) (fun x => NN n ^ (-(4 : ℝ)) < cav (smallInd x (pε' n))) ≤
      NN n ^ (4 : ℝ) * ((1 / 2) ^ pK n + 3 ^ pK n * pK n * (2 * pε' n) ^ ((1 : ℝ) / pK n)) := by
    have hK1 : 1 ≤ pK n := by unfold pK; omega
    have hm := cube_markov (N := n + 1) (fun x => cav (smallInd x (pε' n)))
      (fun x => cav_nonneg (smallInd_nonneg x _)) (NN n ^ (-(4 : ℝ)))
      (Real.rpow_pos_of_pos (NN_pos n) _)
    refine le_trans hm ?_
    have hswap := cav_cubeProb_eq (N := n + 1) (pε' n)
    have hsb := small_ball_sep (N := n + 1) hK1 hK (pε' n) (pε'_pos n) (two_pε'_lt_one hn)
    have hsI : (fun x : Fin (n + 1) → Bool => cav (smallInd x (pε' n))) =
        (fun x => cav (fun θ =>
          if ‖(poly x).eval (Complex.exp ((θ : ℂ) * I))‖ < pε' n then 1 else 0)) := rfl
    rw [hsI, ← hswap]
    rw [div_eq_mul_inv, ← Real.rpow_neg (NN_pos n).le, neg_neg, mul_comm]
    exact mul_le_mul_of_nonneg_left hsb (Real.rpow_nonneg (NN_pos n).le _)
  have p1' : cubeProb (n + 1) (fun x => pt n ≤ |Fs n (c / n) x - cubeAvg (n + 1) (Fs n (c / n))|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))) := p1
  have p2' : cubeProb (n + 1)
      (fun x => pt n ≤ |Fs n (-(c / n)) x - cubeAvg (n + 1) (Fs n (-(c / n)))|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))) := p2
  have p3' : cubeProb (n + 1) (fun x => pt n ≤ |Fs n 0 x - cubeAvg (n + 1) (Fs n 0)|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))) := p3
  have p4' : cubeProb (n + 1) (fun x => pt n ≤ |Ks n x - cubeAvg (n + 1) (Ks n)|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vK n (pβ n))) := p4
  unfold Bnd
  linarith

end

end E522

end

/- ## Section: `Asymp` -/

section

/-
# Asymptotics of the parameters

With `w = N^{1/80}` every parameter is an integer power of `w`:
`δ = w⁻⁴, β = w⁻², β₂ = w⁻¹, t = w⁻¹⁰, √N = w⁴⁰, N = w⁸⁰`.
-/

open Real Filter Topology

namespace E522

noncomputable section

def ww (n : ℕ) : ℝ := NN n ^ ((1 : ℝ) / 80)

lemma ww_pos (n : ℕ) : 0 < ww n := Real.rpow_pos_of_pos (NN_pos n) _

lemma one_le_ww (n : ℕ) : 1 ≤ ww n := Real.one_le_rpow (one_le_NN n) (by norm_num)

lemma ww_pow (n : ℕ) (k : ℕ) : ww n ^ k = NN n ^ ((k : ℝ) / 80) := by
  unfold ww
  rw [← Real.rpow_natCast, ← Real.rpow_mul (NN_pos n).le]
  congr 1; ring

lemma NN_eq_ww (n : ℕ) : NN n = ww n ^ 80 := by
  rw [ww_pow]; norm_num

lemma rpow_neg_eq_ww (n : ℕ) (k : ℕ) : NN n ^ (-((k : ℝ) / 80)) = (ww n ^ k)⁻¹ := by
  rw [Real.rpow_neg (NN_pos n).le, ww_pow]

lemma pδ_eq (n : ℕ) : pδ n = (ww n ^ 4)⁻¹ := by
  rw [← rpow_neg_eq_ww]; unfold pδ; norm_num

lemma pβ_eq (n : ℕ) : pβ n = (ww n ^ 2)⁻¹ := by
  rw [← rpow_neg_eq_ww]; unfold pβ; norm_num

lemma pβ₂_eq (n : ℕ) : pβ₂ n = (ww n ^ 1)⁻¹ := by
  rw [← rpow_neg_eq_ww]; unfold pβ₂; norm_num

lemma pt_eq (n : ℕ) : pt n = (ww n ^ 10)⁻¹ := by
  rw [← rpow_neg_eq_ww]; unfold pt; norm_num

lemma sqrt_NN_eq (n : ℕ) : Real.sqrt (NN n) = ww n ^ 40 := by
  rw [Real.sqrt_eq_rpow, ww_pow]; norm_num

lemma sqrt_natsucc_eq (n : ℕ) : Real.sqrt ((n : ℝ) + 1) = ww n ^ 40 := by
  rw [← NN_eq, sqrt_NN_eq]

lemma natsucc_eq (n : ℕ) : (n : ℝ) + 1 = ww n ^ 80 := by
  rw [← NN_eq, NN_eq_ww]

lemma NN_rpow_neg_four (n : ℕ) : NN n ^ (-(4 : ℝ)) = (ww n ^ 320)⁻¹ := by
  rw [← rpow_neg_eq_ww]; norm_num

lemma NN_rpow_four (n : ℕ) : NN n ^ (4 : ℝ) = ww n ^ 320 := by
  rw [ww_pow]; norm_num

lemma log_NN_eq (n : ℕ) : Real.log (NN n) = 80 * Real.log (ww n) := by
  rw [NN_eq_ww, Real.log_pow]; norm_num

lemma log_ww_nonneg (n : ℕ) : 0 ≤ Real.log (ww n) := Real.log_nonneg (one_le_ww n)

/-- `w^{-k} ≤ w^{-1}` for `k ≥ 1`. -/
lemma inv_pow_le_inv (n : ℕ) {k : ℕ} (hk : 1 ≤ k) : (ww n ^ k)⁻¹ ≤ (ww n)⁻¹ := by
  have h1 := one_le_ww n
  have : ww n ≤ ww n ^ k := by
    calc ww n = ww n ^ 1 := (pow_one _).symm
      _ ≤ ww n ^ k := pow_le_pow_right₀ h1 hk
  exact inv_anti₀ (ww_pos n) this

/- ### `K ≤ 20 log N + 10` and `Λ ≤ 801 (1 + log N)²` -/

lemma natLog_le_two_log (n : ℕ) : (Nat.log 2 (n + 1) : ℝ) ≤ 2 * Real.log (NN n) := by
  have h1 : (2 : ℝ) ^ (Nat.log 2 (n + 1)) ≤ NN n := by
    unfold NN; exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : (Nat.log 2 (n + 1) : ℝ) * Real.log 2 ≤ Real.log (NN n) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) h1
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hL : 0 ≤ (Nat.log 2 (n + 1) : ℝ) := by positivity
  nlinarith

lemma pK_le (n : ℕ) : (pK n : ℝ) ≤ 20 * Real.log (NN n) + 10 := by
  have h := natLog_le_two_log n
  have e : (pK n : ℝ) = 10 * ((Nat.log 2 (n + 1) : ℕ) : ℝ) + 10 := by
    unfold pK; push_cast; ring
  rw [e]; linarith

lemma Lam_eq (n : ℕ) : Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
    = Real.log 2 - Real.log (NN n) / 20 + Real.log (NN n) / 2 + 40 * pK n * Real.log (NN n) := by
  have hN := NN_pos n
  have hsq : 0 < Real.sqrt (NN n) := Real.sqrt_pos.mpr hN
  have hε : 2 * pε' n = NN n ^ (-(40 * (pK n : ℝ))) := by
    unfold pε'; ring
  rw [hε]
  have e : 2 * pδ n / (NN n ^ (-(40 * (pK n : ℝ))) / Real.sqrt (NN n)) =
      2 * pδ n * Real.sqrt (NN n) * NN n ^ (40 * (pK n : ℝ)) := by
    rw [Real.rpow_neg hN.le]
    field_simp
  rw [e]
  have hδ := pδ_pos n
  have hr : 0 < NN n ^ (40 * (pK n : ℝ)) := Real.rpow_pos_of_pos hN _
  rw [Real.log_mul (by positivity) hr.ne', Real.log_mul (by positivity) hsq.ne',
    Real.log_mul (by norm_num) hδ.ne', Real.log_rpow hN, Real.log_sqrt hN.le]
  unfold pδ
  rw [Real.log_rpow hN]
  ring

lemma Lam_le (n : ℕ) : Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
    ≤ 801 * (1 + Real.log (NN n)) ^ 2 := by
  rw [Lam_eq]
  have hL := Real.log_nonneg (one_le_NN n)
  have hK := pK_le n
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have : 40 * (pK n : ℝ) * Real.log (NN n) ≤ 40 * (20 * Real.log (NN n) + 10) * Real.log (NN n) :=
    mul_le_mul_of_nonneg_right (by linarith) hL
  nlinarith

/- ### `Err n ≤ C (1 + log N)² / w` -/

lemma eBound_le (n : ℕ) : eBound n (pδ n) (pt n) ≤ 455 * (1 + Real.log (NN n)) / ww n := by
  have hw := ww_pos n
  have hw1 := one_le_ww n
  have hL := log_ww_nonneg n
  unfold eBound
  rw [pδ_eq, pt_eq, sqrt_natsucc_eq, natsucc_eq]
  have hsq : Real.sqrt (2 * (ww n ^ 10)⁻¹) = Real.sqrt 2 * (ww n ^ 5)⁻¹ := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_inv, show ww n ^ 10 = (ww n ^ 5) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  have habs : |Real.log (ww n ^ 4)⁻¹| = 4 * Real.log (ww n) := by
    rw [Real.log_inv, Real.log_pow, abs_neg, abs_of_nonneg (by positivity)]; norm_num
  rw [habs, log_NN_eq]
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq]; norm_num]
    · exact Real.sqrt_le_sqrt (by norm_num)
  -- normalise everything to powers of w
  have key : (Real.sqrt 2 * (ww n ^ 5)⁻¹ + 20 / (ww n ^ 40 * (ww n ^ 10)⁻¹)) / (2 * (ww n ^ 4)⁻¹)
      + 2 * (ww n ^ 10)⁻¹ * (2 * (4 * Real.log (ww n) + 1))
      + (10 * (2 / ww n ^ 40) / ((ww n ^ 4)⁻¹) ^ 3
        + 20 / (ww n ^ 80 * (ww n ^ 10)⁻¹) * (1 / ((ww n ^ 4)⁻¹) ^ 2
          + 10 * ww n ^ 80 * (2 / ww n ^ 40) / ((ww n ^ 4)⁻¹) ^ 3))
      = Real.sqrt 2 / 2 * (ww n)⁻¹ + 10 * (ww n ^ 26)⁻¹
        + (16 * Real.log (ww n) + 4) * (ww n ^ 10)⁻¹
        + 20 * (ww n ^ 28)⁻¹ + 20 * (ww n ^ 62)⁻¹ + 400 * (ww n ^ 18)⁻¹ := by
    field_simp
    ring
  rw [key]
  have i26 := inv_pow_le_inv n (k := 26) (by norm_num)
  have i10 := inv_pow_le_inv n (k := 10) (by norm_num)
  have i28 := inv_pow_le_inv n (k := 28) (by norm_num)
  have i62 := inv_pow_le_inv n (k := 62) (by norm_num)
  have i18 := inv_pow_le_inv n (k := 18) (by norm_num)
  have hwinv : 0 < (ww n)⁻¹ := inv_pos.mpr hw
  have hlog10 : (16 * Real.log (ww n) + 4) * (ww n ^ 10)⁻¹ ≤ (16 * Real.log (ww n) + 4) * (ww n)⁻¹ :=
    mul_le_mul_of_nonneg_left i10 (by positivity)
  rw [div_eq_mul_inv (455 * (1 + 80 * Real.log (ww n)))]
  nlinarith [mul_nonneg hL hwinv.le]

lemma Err_le (n : ℕ) : Err n ≤ 10100 * (1 + Real.log (NN n)) ^ 2 / ww n := by
  have hw := ww_pos n
  have hw1 := one_le_ww n
  have hLw := log_ww_nonneg n
  have hL := Real.log_nonneg (one_le_NN n)
  have hwinv : 0 < (ww n)⁻¹ := inv_pos.mpr hw
  unfold Err
  have h1 := eBound_le n
  have h2 : pt n ≤ (ww n)⁻¹ := by rw [pt_eq]; exact inv_pow_le_inv n (by norm_num)
  have h3 : pδ n ^ 2 / (2 * pβ n ^ 2) ≤ (ww n)⁻¹ := by
    rw [pδ_eq, pβ_eq]
    have : ((ww n ^ 4)⁻¹) ^ 2 / (2 * ((ww n ^ 2)⁻¹) ^ 2) = (ww n ^ 4)⁻¹ / 2 := by
      field_simp; try ring
    rw [this]
    have := inv_pow_le_inv n (k := 4) (by norm_num)
    have : 0 ≤ (ww n ^ 4)⁻¹ := by positivity
    linarith
  have h4 : 2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n ≤ 6 * (ww n)⁻¹ := by
    rw [pβ₂_eq, sqrt_NN_eq, pβ_eq, pt_eq]
    have e : ((ww n ^ 2)⁻¹) ^ 2 / ((ww n ^ 1)⁻¹) ^ 2 = (ww n ^ 2)⁻¹ := by
      field_simp; try ring
    rw [e, pow_one, div_eq_mul_inv]
    have := inv_pow_le_inv n (k := 40) (by norm_num)
    have := inv_pow_le_inv n (k := 2) (by norm_num)
    have := inv_pow_le_inv n (k := 10) (by norm_num)
    linarith
  have h4nn : 0 ≤ 2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n := by
    have := pβ₂_pos n; have := pβ_pos n; have := pt_pos n
    have := Real.sqrt_nonneg (NN n); positivity
  have h5 := Lam_le n
  have h5nn := Err_nonneg_parts n
  have h6 : 2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
      * (2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n)
      ≤ 2 * (801 * (1 + Real.log (NN n)) ^ 2) * (6 * (ww n)⁻¹) := by
    apply mul_le_mul (by linarith) h4 h4nn (by positivity)
  have h7 : (1 + Real.log (NN n)) * NN n ^ (-(4 : ℝ))
      + Real.sqrt (NN n ^ (-(4 : ℝ))) * Real.sqrt (400 * NN n ^ 2)
      ≤ (21 + Real.log (NN n)) * (ww n)⁻¹ := by
    rw [NN_rpow_neg_four]
    have hs1 : Real.sqrt ((ww n ^ 320)⁻¹) = (ww n ^ 160)⁻¹ := by
      rw [Real.sqrt_inv, show ww n ^ 320 = (ww n ^ 160) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have hs2 : Real.sqrt (400 * NN n ^ 2) = 20 * ww n ^ 80 := by
      rw [NN_eq_ww, show 400 * (ww n ^ 80) ^ 2 = (20 * ww n ^ 80) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [hs1, hs2]
    have e : (ww n ^ 160)⁻¹ * (20 * ww n ^ 80) = 20 * (ww n ^ 80)⁻¹ := by
      field_simp; try ring
    rw [e]
    have := inv_pow_le_inv n (k := 320) (by norm_num)
    have := inv_pow_le_inv n (k := 80) (by norm_num)
    have : (1 + Real.log (NN n)) * (ww n ^ 320)⁻¹ ≤ (1 + Real.log (NN n)) * (ww n)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_pow_le_inv n (by norm_num)) (by positivity)
    nlinarith
  have h1' : eBound n (pδ n) (pt n) ≤ 455 * (1 + Real.log (NN n)) * (ww n)⁻¹ := by
    rw [div_eq_mul_inv] at h1; exact h1
  have hR : 10100 * (1 + Real.log (NN n)) ^ 2 / ww n =
      10100 * (1 + Real.log (NN n)) ^ 2 * (ww n)⁻¹ := div_eq_mul_inv _ _
  rw [hR]
  have hsq : (1 + Real.log (NN n)) ≤ (1 + Real.log (NN n)) ^ 2 := by nlinarith
  have hone : (1 : ℝ) ≤ (1 + Real.log (NN n)) ^ 2 := by nlinarith
  have a1 : 455 * (1 + Real.log (NN n)) * (ww n)⁻¹ ≤ 455 * (1 + Real.log (NN n)) ^ 2 * (ww n)⁻¹ := by
    have := mul_le_mul_of_nonneg_right hsq hwinv.le; nlinarith
  have a2 : (21 + Real.log (NN n)) * (ww n)⁻¹ ≤ 22 * (1 + Real.log (NN n)) ^ 2 * (ww n)⁻¹ := by
    apply mul_le_mul_of_nonneg_right _ hwinv.le; nlinarith
  have a3 : 2 * (ww n)⁻¹ ≤ 2 * (1 + Real.log (NN n)) ^ 2 * (ww n)⁻¹ := by
    have := mul_le_mul_of_nonneg_right hone hwinv.le; nlinarith
  linarith

lemma ww_tendsto : Tendsto ww atTop atTop := by
  unfold ww
  have h1 : Tendsto (fun n : ℕ => NN n) atTop atTop := by
    unfold NN
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  exact (tendsto_rpow_atTop (by norm_num)).comp h1

lemma Err_eventually_le (ε : ℝ) (hε : 0 < ε) : ∀ᶠ n in atTop, Err n ≤ ε := by
  -- the bound as a function of `w`
  set G : ℝ → ℝ := fun w => 10100 * (1 + 80 * Real.log w) ^ 2 / w with hG
  have hGt : Tendsto G atTop (𝓝 0) := by
    have t0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
    have t1 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have t2 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    have hsum := ((t0.const_mul 10100).add (t1.const_mul 1616000)).add (t2.const_mul 64640000)
    simp only [mul_zero, add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with w hw
    simp only [hG, pow_zero, one_mul, add_zero, pow_one]
    field_simp
    ring
  have hev : ∀ᶠ n in atTop, G (ww n) < ε :=
    (hGt.comp ww_tendsto).eventually (gt_mem_nhds hε)
  filter_upwards [hev] with n hn
  refine le_trans (Err_le n) (le_of_lt ?_)
  simp only [hG] at hn
  rw [log_NN_eq]
  exact hn

end

end E522

end

/- ## Section: `Final` -/

section

/-
# Summability of the bad-event bounds and complete convergence
-/

open Real Filter Topology

namespace E522

noncomputable section

/- ### Variance proxies in terms of `w = N^{1/80}` -/

lemma natSqrt_bounds {n : ℕ} (hn : 3 ≤ n) :
    ww n ^ 40 / 2 ≤ (Nat.sqrt (n + 1) : ℝ) ∧ (Nat.sqrt (n + 1) : ℝ) ≤ ww n ^ 40 := by
  have h1 : (Nat.sqrt (n + 1) : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
  have h2 : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (Nat.sqrt (n + 1) : ℝ) + 1 :=
    Real.real_sqrt_le_nat_sqrt_succ
  have hs : Real.sqrt ((n + 1 : ℕ) : ℝ) = ww n ^ 40 := sqrt_NN_eq n
  rw [hs] at h1 h2
  have h4 : (2 : ℝ) ≤ ww n ^ 40 := by
    rw [← hs]
    rw [show (2:ℝ) = Real.sqrt 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    have : (4 : ℝ) ≤ n + 1 := by exact_mod_cast (by omega : 4 ≤ n + 1)
    push_cast; linarith
  constructor <;> linarith

lemma vF_le {n : ℕ} (hn : 3 ≤ n) : vF n (pδ n) ≤ 21000 * (ww n ^ 24)⁻¹ := by
  obtain ⟨hS1, hS2⟩ := natSqrt_bounds hn
  have hw := ww_pos n
  have hw1 := one_le_ww n
  set S := (Nat.sqrt (n + 1) : ℝ) with hSdef
  have hSpos : 0 < S := by
    have : 0 < ww n ^ 40 / 2 := by positivity
    linarith
  unfold vF
  rw [pδ_eq, sqrt_natsucc_eq]
  have hN : ((n + 1 : ℕ) : ℝ) = ww n ^ 80 := NN_eq_ww n
  rw [hN]
  have t1 : 3 * (1 / (2 * (ww n ^ 4)⁻¹)) ^ 2 * (2 / ww n ^ 40) ^ 2 * (ww n ^ 80 / S + 1)
      = 3 * ww n ^ 8 / S + 3 * (ww n ^ 72)⁻¹ := by
    field_simp; try ring
  have t2 : 12 * (3 / ((ww n ^ 4)⁻¹) ^ 2) ^ 2 * (2 / ww n ^ 40) ^ 4 * S * ww n ^ 80
      = 1728 * S * (ww n ^ 64)⁻¹ := by
    field_simp; try ring
  have t3 : (3 / ((ww n ^ 4)⁻¹) ^ 2) ^ 2 * (2 / ww n ^ 40) ^ 4 * ww n ^ 80
      = 144 * (ww n ^ 64)⁻¹ := by
    field_simp; try ring
  rw [t1, t2, t3]
  -- bound each term by a multiple of w^{-24}
  have b1 : 3 * ww n ^ 8 / S ≤ 6 * (ww n ^ 32)⁻¹ := by
    rw [div_le_iff₀ hSpos]
    have e : 6 * (ww n ^ 32)⁻¹ * S ≥ 6 * (ww n ^ 32)⁻¹ * (ww n ^ 40 / 2) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have e2 : 6 * (ww n ^ 32)⁻¹ * (ww n ^ 40 / 2) = 3 * ww n ^ 8 := by
      field_simp; try ring
    linarith
  have b2 : 1728 * S * (ww n ^ 64)⁻¹ ≤ 1728 * (ww n ^ 24)⁻¹ := by
    have e : 1728 * S * (ww n ^ 64)⁻¹ ≤ 1728 * ww n ^ 40 * (ww n ^ 64)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    have e2 : 1728 * ww n ^ 40 * (ww n ^ 64)⁻¹ = 1728 * (ww n ^ 24)⁻¹ := by
      field_simp; try ring
    linarith
  have m32 : (ww n ^ 32)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have m72 : (ww n ^ 72)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have m64 : (ww n ^ 64)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have hnn : 0 ≤ (ww n ^ 24)⁻¹ := by positivity
  linarith

lemma vK_le {n : ℕ} (hn : 3 ≤ n) : vK n (pβ n) ≤ 21000 * (ww n ^ 24)⁻¹ := by
  obtain ⟨hS1, hS2⟩ := natSqrt_bounds hn
  have hw := ww_pos n
  have hw1 := one_le_ww n
  set S := (Nat.sqrt (n + 1) : ℝ) with hSdef
  have hSpos : 0 < S := by
    have : 0 < ww n ^ 40 / 2 := by positivity
    linarith
  unfold vK
  rw [pβ_eq, sqrt_natsucc_eq]
  have hN : ((n + 1 : ℕ) : ℝ) = ww n ^ 80 := NN_eq_ww n
  rw [hN]
  have t1 : 3 * (1 / (ww n ^ 2)⁻¹) ^ 2 * (2 / ww n ^ 40) ^ 2 * (ww n ^ 80 / S + 1)
      = 12 * ww n ^ 4 / S + 12 * (ww n ^ 76)⁻¹ := by
    field_simp; try ring
  have t2 : 12 * (10 / ((ww n ^ 2)⁻¹) ^ 2) ^ 2 * (2 / ww n ^ 40) ^ 4 * S * ww n ^ 80
      = 19200 * S * (ww n ^ 72)⁻¹ := by
    field_simp; try ring
  have t3 : (10 / ((ww n ^ 2)⁻¹) ^ 2) ^ 2 * (2 / ww n ^ 40) ^ 4 * ww n ^ 80
      = 1600 * (ww n ^ 72)⁻¹ := by
    field_simp; try ring
  rw [t1, t2, t3]
  have b1 : 12 * ww n ^ 4 / S ≤ 24 * (ww n ^ 36)⁻¹ := by
    rw [div_le_iff₀ hSpos]
    have e : 24 * (ww n ^ 36)⁻¹ * S ≥ 24 * (ww n ^ 36)⁻¹ * (ww n ^ 40 / 2) :=
      mul_le_mul_of_nonneg_left hS1 (by positivity)
    have e2 : 24 * (ww n ^ 36)⁻¹ * (ww n ^ 40 / 2) = 12 * ww n ^ 4 := by
      field_simp; try ring
    linarith
  have b2 : 19200 * S * (ww n ^ 72)⁻¹ ≤ 19200 * (ww n ^ 32)⁻¹ := by
    have e : 19200 * S * (ww n ^ 72)⁻¹ ≤ 19200 * ww n ^ 40 * (ww n ^ 72)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    have e2 : 19200 * ww n ^ 40 * (ww n ^ 72)⁻¹ = 19200 * (ww n ^ 32)⁻¹ := by
      field_simp; try ring
    linarith
  have m36 : (ww n ^ 36)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have m76 : (ww n ^ 76)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have m72 : (ww n ^ 72)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have m32 : (ww n ^ 32)⁻¹ ≤ (ww n ^ 24)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hw1 (by norm_num))
  have hnn : 0 ≤ (ww n ^ 24)⁻¹ := by positivity
  linarith

/-- `exp(-t²/(2v)) ≤ C / N²` once `v ≤ 21000 w^{-24}`. -/
lemma exp_tail_le {n : ℕ} {v : ℝ} (hv : 0 < v) (hvle : v ≤ 21000 * (ww n ^ 24)⁻¹) :
    Real.exp (-(pt n) ^ 2 / (2 * v)) ≤
      (Nat.factorial 40 : ℝ) * 42000 ^ 40 * (NN n ^ 2)⁻¹ := by
  have hw := ww_pos n
  have hw1 := one_le_ww n
  set x := ww n ^ 4 / 42000 with hx
  have hxpos : 0 ≤ x := by positivity
  have h1 : x ≤ (pt n) ^ 2 / (2 * v) := by
    rw [pt_eq, le_div_iff₀ (by positivity)]
    have : ww n ^ 4 / 42000 * (2 * v) ≤ ww n ^ 4 / 42000 * (2 * (21000 * (ww n ^ 24)⁻¹)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : ww n ^ 4 / 42000 * (2 * (21000 * (ww n ^ 24)⁻¹)) = ((ww n ^ 10)⁻¹) ^ 2 := by
      field_simp; try ring
    rw [hx]; linarith
  have h2 : Real.exp (-(pt n) ^ 2 / (2 * v)) ≤ Real.exp (-x) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]; linarith
  refine le_trans h2 ?_
  have h3 := Real.pow_div_factorial_le_exp x hxpos 40
  have hxp : 0 < x := by positivity
  have hexp : 0 < Real.exp x := Real.exp_pos x
  rw [Real.exp_neg]
  have hfac : (0 : ℝ) < (Nat.factorial 40 : ℝ) := by exact_mod_cast Nat.factorial_pos 40
  rw [inv_le_iff_one_le_mul₀ hexp]
  have hN2 : NN n ^ 2 = ww n ^ 160 := by rw [NN_eq_ww]; ring
  rw [hN2]
  have hxe : x ^ 40 = ww n ^ 160 / 42000 ^ 40 := by rw [hx]; ring
  rw [hxe, div_div, div_le_iff₀ (by positivity)] at h3
  have : (Nat.factorial 40 : ℝ) * 42000 ^ 40 * (ww n ^ 160)⁻¹ * Real.exp x
      = (ww n ^ 160)⁻¹ * (Real.exp x * (42000 ^ 40 * (Nat.factorial 40 : ℝ))) := by ring
  rw [this]
  calc (1 : ℝ) = (ww n ^ 160)⁻¹ * ww n ^ 160 := by field_simp
    _ ≤ (ww n ^ 160)⁻¹ * (Real.exp x * (42000 ^ 40 * (Nat.factorial 40 : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- The small-ball term. -/
lemma sb_term_le {n : ℕ} (hn : 1 ≤ n) :
    NN n ^ (4 : ℝ) * ((1 / 2) ^ pK n + 3 ^ pK n * pK n * (2 * pε' n) ^ ((1 : ℝ) / pK n))
      ≤ (1 + 20 * 3 ^ 10) * (NN n ^ 2)⁻¹ := by
  have hN := NN_pos n
  have hN1 := one_le_NN n
  set ℓ := Nat.log 2 (n + 1) with hℓ
  have hK : pK n = 10 * (ℓ + 1) := rfl
  have hKpos : (0 : ℝ) < pK n := by rw [hK]; positivity
  -- (1/2)^K ≤ N^{-10}
  have h2K : NN n ^ 10 ≤ (2 : ℝ) ^ pK n := by
    have hlt : n + 1 < 2 ^ (ℓ + 1) := Nat.lt_pow_succ_log_self (by norm_num) (n + 1)
    have hNle : (NN n) ≤ (2 : ℝ) ^ (ℓ + 1) := by
      unfold NN; exact_mod_cast hlt.le
    have e : (2 : ℝ) ^ pK n = ((2 : ℝ) ^ (ℓ + 1)) ^ 10 := by
      rw [hK, ← pow_mul, mul_comm]
    rw [e]
    exact pow_le_pow_left₀ hN.le hNle 10
  have hhalf : ((1 : ℝ) / 2) ^ pK n ≤ (NN n ^ 10)⁻¹ := by
    rw [one_div, inv_pow]
    exact inv_anti₀ (by positivity) h2K
  -- (2ε')^{1/K} = N^{-40}
  have hroot : (2 * pε' n) ^ ((1 : ℝ) / pK n) = (NN n ^ 40)⁻¹ := by
    have e : 2 * pε' n = NN n ^ (-(40 * (pK n : ℝ))) := by unfold pε'; ring
    rw [e, ← Real.rpow_mul hN.le]
    rw [show -(40 * (pK n : ℝ)) * (1 / pK n) = -(40 : ℝ) by field_simp]
    rw [Real.rpow_neg hN.le]
    norm_num
  -- 3^K ≤ 3^10 N^20
  have h3K : (3 : ℝ) ^ pK n ≤ 3 ^ 10 * NN n ^ 20 := by
    have h2l : (2 : ℝ) ^ ℓ ≤ NN n := by
      unfold NN; exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h3l : (3 : ℝ) ^ ℓ ≤ NN n ^ 2 := by
      calc (3 : ℝ) ^ ℓ ≤ 4 ^ ℓ := pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ
        _ = ((2 : ℝ) ^ ℓ) ^ 2 := by rw [← pow_mul, show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
            mul_comm]
        _ ≤ NN n ^ 2 := pow_le_pow_left₀ (by positivity) h2l 2
    rw [hK]
    calc (3 : ℝ) ^ (10 * (ℓ + 1)) = 3 ^ 10 * ((3 : ℝ) ^ ℓ) ^ 10 := by ring
      _ ≤ 3 ^ 10 * (NN n ^ 2) ^ 10 := by gcongr
      _ = 3 ^ 10 * NN n ^ 20 := by ring
  -- K ≤ 20 N
  have hKN : (pK n : ℝ) ≤ 20 * NN n := by
    have hl : ℓ ≤ n + 1 := Nat.log_le_self 2 (n + 1)
    have : (pK n : ℝ) ≤ 10 * ((n + 1 : ℕ) : ℝ) + 10 := by
      rw [hK]; push_cast; have : (ℓ : ℝ) ≤ n + 1 := by exact_mod_cast hl
      linarith
    unfold NN at hN1 ⊢; linarith
  rw [hroot]
  have hN4 : NN n ^ (4 : ℝ) = NN n ^ 4 := by rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast]
  rw [hN4]
  have hA : NN n ^ 4 * (1 / 2) ^ pK n ≤ (NN n ^ 2)⁻¹ := by
    calc NN n ^ 4 * (1 / 2) ^ pK n ≤ NN n ^ 4 * (NN n ^ 10)⁻¹ :=
          mul_le_mul_of_nonneg_left hhalf (by positivity)
      _ = (NN n ^ 6)⁻¹ := by field_simp; try ring
      _ ≤ (NN n ^ 2)⁻¹ := inv_anti₀ (by positivity : (0:ℝ) < NN n ^ 2)
          (pow_le_pow_right₀ hN1 (by norm_num : 2 ≤ 6))
  have hB : NN n ^ 4 * (3 ^ pK n * pK n * (NN n ^ 40)⁻¹) ≤ 20 * 3 ^ 10 * (NN n ^ 2)⁻¹ := by
    calc NN n ^ 4 * (3 ^ pK n * pK n * (NN n ^ 40)⁻¹)
        ≤ NN n ^ 4 * ((3 ^ 10 * NN n ^ 20) * (20 * NN n) * (NN n ^ 40)⁻¹) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul h3K hKN (by positivity) (by positivity)
      _ = 20 * 3 ^ 10 * (NN n ^ 15)⁻¹ := by field_simp; try ring
      _ ≤ 20 * 3 ^ 10 * (NN n ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact inv_anti₀ (by positivity : (0:ℝ) < NN n ^ 2)
            (pow_le_pow_right₀ hN1 (by norm_num : 2 ≤ 15))
  nlinarith [hA, hB]

/-- The constant in the summable bound. -/
def Cbnd : ℝ := 8 * ((Nat.factorial 40 : ℝ) * 42000 ^ 40) + (1 + 20 * 3 ^ 10)

lemma Bnd_le {n : ℕ} (hn : 3 ≤ n) : Bnd n ≤ (1 / 2) ^ (n + 1) + Cbnd * (NN n ^ 2)⁻¹ := by
  have hn1 : 1 ≤ n := by omega
  unfold Bnd Cbnd
  have e1 := exp_tail_le (vF_pos n (pδ_pos n)) (vF_le hn)
  have e2 := exp_tail_le (vK_pos n (pβ_pos n)) (vK_le hn)
  have e3 := sb_term_le hn1
  nlinarith [e1, e2, e3]

lemma summable_bound : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) + Cbnd * (NN n ^ 2)⁻¹) := by
  apply Summable.add
  · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
      (add_left_injective 1)
  · apply Summable.mul_left
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr (fun n => ?_)
    unfold NN; push_cast; ring

/- ### `K ≤ N` eventually -/

lemma ten_mul_le_two_pow (ℓ : ℕ) (hℓ : 7 ≤ ℓ) : 10 * (ℓ + 1) ≤ 2 ^ ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

lemma pK_le_N_eventually : ∀ᶠ n in atTop, pK n ≤ n + 1 := by
  filter_upwards [eventually_ge_atTop 127] with n hn
  have hℓ : 7 ≤ Nat.log 2 (n + 1) := by
    rw [Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    norm_num; omega
  have h1 := ten_mul_le_two_pow _ hℓ
  have h2 := Nat.pow_log_le_self 2 (show n + 1 ≠ 0 by omega)
  unfold pK
  omega

/- ### Complete convergence -/

theorem complete_convergence (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℕ => cubeProb (n + 1) (fun x => ε < |(2 * rootCount x : ℝ) / n - 1|)) := by
  set ε₁ := min ε 1 with hε₁
  have hε₁pos : 0 < ε₁ := lt_min hε one_pos
  have hε₁le : ε₁ ≤ ε := min_le_left _ _
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set c := ε₁ / 2 with hc
  have hcpos : 0 < c := by positivity
  have hc2 : c ≤ 1 / 2 := by rw [hc]; linarith
  apply Summable.of_norm_bounded_eventually_nat summable_bound
  have hErr := Err_eventually_le (ε₁ ^ 2 / 16) (by positivity)
  filter_upwards [hErr, pK_le_N_eventually, eventually_ge_atTop 3] with n hE hK hn
  rw [Real.norm_of_nonneg (cubeProb_nonneg _ _)]
  refine le_trans ?_ (Bnd_le hn)
  refine le_trans (cubeProb_mono (fun x hx => ?_)) (prob_bad (by omega) hK hcpos hc2)
  intro hG
  have hb := good_bound hn hcpos hc2 x hG
  have h4 : 4 * Err n / c ≤ ε₁ / 2 := by
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith
  have : |(2 * rootCount x : ℝ) / n - 1| < ε := by
    have : c / 2 = ε₁ / 4 := by rw [hc]; ring
    linarith
  linarith

end

end E522

end

/- ## Section: `DefsPM` -/

section

/-
# The `±1` (Littlewood) polynomial: definitions

For `x : Fin N → Bool`, `polyPM x = ∑_{k<N} sgn(x_k) z^k`. On the circle of radius `e^s`,
`f(e^{s+iθ}) = σ_N(s) · W(θ)` with `W = Wfun (rho N s) x` (no mean term).
-/

open Real Complex

namespace E522

noncomputable section

/-- The `±1` polynomial `∑_{k<N} sgn(x_k) z^k`. -/
def polyPM {N : ℕ} (x : Fin N → Bool) : Polynomial ℂ :=
  ∑ k : Fin N, Polynomial.monomial (k : ℕ) ((sgn (x k) : ℝ) : ℂ)

open scoped Classical in
/-- Number of roots (with multiplicity) of `polyPM x` in the closed unit disc. -/
def rootCountPM {N : ℕ} (x : Fin N → Bool) : ℕ :=
  (polyPM x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1)

/-- `Λ_x(s)` for the `±1` polynomial. -/
def LamPM {N : ℕ} (x : Fin N → Bool) (s : ℝ) : ℝ :=
  Real.circleAverage (fun z => Real.log ‖(polyPM x).eval z‖) 0 (Real.exp s) -
    Real.log (sig2 N s) / 2

/-- Indicator of the small values `|f(e^{iθ})| < 2ε'` of the `±1` polynomial. -/
def smallIndPM {N : ℕ} (x : Fin N → Bool) (ε' : ℝ) (θ : ℝ) : ℝ :=
  if ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε' then 1 else 0

end

end E522

end

/- ## Section: `JensenPM` -/

section

/-
# Jensen's formula and the deterministic main lemma for `±1` polynomials

Adapt `Erdos522/Jensen.lean` (0/1 case). Differences: `polyPM x ≠ 0` always (for `N ≥ 1` the
constant coefficient is `±1`), `‖leadingCoeff‖ = 1` (not `= 1`), so Jensen gives
`circleAverage(log|f|) 0 (e^s) = log‖lead‖ + ∑_α log max(e^s,|α|) = ∑_α log max(e^s,|α|)`,
and `f(e^{s+iθ}) = σ_N(s) · Wfun (rho N s) x θ` (no factor 2, no mean term), so
`Λ_x(s) = cav(log |W|)`.
-/

open Real Complex

namespace E522

theorem polyPM_eval {N : ℕ} (x : Fin N → Bool) (z : ℂ) :
    (polyPM x).eval z = ∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * z ^ (k : ℕ) := by
  simp [polyPM, Polynomial.eval_finsetSum]

/-- Explicit coefficients of `polyPM x`. -/
theorem jpm_aux_coeff {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (polyPM x).coeff m = if h : m < N then ((sgn (x ⟨m, h⟩) : ℝ) : ℂ) else 0 := by
  simp only [polyPM, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (Fin.ext hbm)
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbm
    exact h (hbm ▸ b.2)

/-- Every coefficient of `polyPM x` is `0` or has norm `1`. -/
theorem jpm_aux_coeff_mem {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (polyPM x).coeff m = 0 ∨ ‖(polyPM x).coeff m‖ = 1 := by
  rw [jpm_aux_coeff]
  split_ifs with h
  · right
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sgn]
  · left
    rfl

theorem polyPM_ne_zero {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) : polyPM x ≠ 0 := by
  intro h0
  have h := jpm_aux_coeff x 0
  rw [h0, dif_pos (by omega : 0 < N), Polynomial.coeff_zero] at h
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zero, Complex.norm_real, Real.norm_eq_abs, abs_sgn] at h2
  exact zero_ne_one h2

theorem polyPM_norm_leadingCoeff {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    ‖(polyPM x).leadingCoeff‖ = 1 := by
  rcases jpm_aux_coeff_mem x (polyPM x).natDegree with h | h
  · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr (polyPM_ne_zero hN x))
  · exact h

/-- `log` of the norm of a product of linear factors is the sum of the logs. -/
theorem jpm_aux_log_norm_prod (S : Multiset ℂ) (z : ℂ) (hz : (S.map (z - ·)).prod ≠ 0) :
    Real.log ‖(S.map (z - ·)).prod‖ = (S.map (fun α => Real.log ‖z - α‖)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons] at hz ⊢
    have h1 : z - a ≠ 0 := left_ne_zero_of_mul hz
    have h2 : (S.map (z - ·)).prod ≠ 0 := right_ne_zero_of_mul hz
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2), ih h2]

/-- Off the zeros, `log |f(z)| = log ‖lead‖ + ∑_{α ∈ roots} log |z − α| = ∑_α log |z − α|`. -/
theorem jpm_aux_log_eval {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (z : ℂ)
    (hz : (polyPM x).eval z ≠ 0) :
    Real.log ‖(polyPM x).eval z‖ = ((polyPM x).roots.map (fun α => Real.log ‖z - α‖)).sum := by
  have h := (IsAlgClosed.splits (polyPM x)).eval_eq_prod_roots z
  rw [h] at hz ⊢
  have hp : ((polyPM x).roots.map (z - ·)).prod ≠ 0 := right_ne_zero_of_mul hz
  rw [norm_mul, polyPM_norm_leadingCoeff hN x, one_mul]
  exact jpm_aux_log_norm_prod _ z hp

/-- Circle averages commute with the finite (multiset) sum of `log |· − α|`. -/
theorem jpm_aux_circleAverage_sum (S : Multiset ℂ) (R : ℝ) :
    CircleIntegrable (fun z => (S.map (fun α => Real.log ‖z - α‖)).sum) 0 R ∧
    Real.circleAverage (fun z => (S.map (fun α => Real.log ‖z - α‖)).sum) 0 R =
      (S.map (fun α => Real.circleAverage (fun z => Real.log ‖z - α‖) 0 R)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp [Real.circleAverage_const]
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have ha : CircleIntegrable (fun z => Real.log ‖z - a‖) 0 R :=
      circleIntegrable_log_norm_sub_const R
    refine ⟨ha.fun_add ih.1, ?_⟩
    rw [Real.circleAverage_fun_add ha ih.1, ih.2]

/-- `f` does not vanish at almost every point of a circle of nonzero radius. -/
theorem jpm_aux_ae_ne_zero {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) {R : ℝ} (hR : R ≠ 0) :
    ∀ᵐ θ ∂MeasureTheory.volume, (polyPM x).eval (circleMap 0 R θ) ≠ 0 := by
  have hx := polyPM_ne_zero hN x
  have hc : (circleMap 0 R ⁻¹' {z | (polyPM x).IsRoot z}).Countable := by
    apply Set.Countable.preimage_circleMap _ 0 hR
    exact ((polyPM x).roots.finite_toSet.subset
      (fun z hz => (Polynomial.mem_roots hx).mpr hz)).countable
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (hc.measure_zero _)
  intro θ hθ
  simpa using hθ

theorem jensen_polyPM {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (s : ℝ) :
    Real.circleAverage (fun z => Real.log ‖(polyPM x).eval z‖) 0 (Real.exp s) =
      ((polyPM x).roots.map (fun α => Real.log (max (Real.exp s) ‖α‖))).sum := by
  have hR : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have h1 : Real.circleAverage (fun z => Real.log ‖(polyPM x).eval z‖) 0 (Real.exp s) =
      Real.circleAverage (fun z => ((polyPM x).roots.map (fun α => Real.log ‖z - α‖)).sum) 0
        (Real.exp s) := by
    unfold Real.circleAverage
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards [jpm_aux_ae_ne_zero hN x hR] with θ hθ _
    exact jpm_aux_log_eval hN x _ hθ
  rw [h1, (jpm_aux_circleAverage_sum _ _).2]
  congr 1
  apply Multiset.map_congr rfl
  intro α _
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR, zero_sub, norm_neg,
    Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hR (by positivity),
    mul_max_of_nonneg _ _ (Real.exp_pos s).le, mul_one, mul_inv_cancel_left₀ hR]

/-- Secant bounds for `s ↦ ∑_α log max(e^s, |α|)` at `s = h, 0, -h`. -/
theorem jpm_aux_secant (S : Multiset ℂ) {h : ℝ} (hh : 0 < h)
    [DecidablePred (· ∈ Metric.closedBall (0 : ℂ) 1)] :
    h * (S.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) ≤
      (S.map (fun α => Real.log (max (Real.exp h) ‖α‖))).sum -
        (S.map (fun α => Real.log (max (Real.exp 0) ‖α‖))).sum ∧
    (S.map (fun α => Real.log (max (Real.exp 0) ‖α‖))).sum -
        (S.map (fun α => Real.log (max (Real.exp (-h)) ‖α‖))).sum ≤
      h * (S.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.countP_cons, Multiset.map_cons, Multiset.sum_cons]
    push_cast
    by_cases ha : a ∈ Metric.closedBall (0 : ℂ) 1
    · rw [if_pos ha]
      have ha' : ‖a‖ ≤ 1 := by simpa using ha
      have e1 : Real.log (max (Real.exp h) ‖a‖) = h := by
        rw [max_eq_left (by linarith [Real.add_one_le_exp h] : ‖a‖ ≤ Real.exp h), Real.log_exp]
      have e2 : Real.log (max (Real.exp 0) ‖a‖) = 0 := by
        rw [Real.exp_zero, max_eq_left ha', Real.log_one]
      have e3 : -h ≤ Real.log (max (Real.exp (-h)) ‖a‖) := by
        have := Real.log_le_log (Real.exp_pos (-h)) (le_max_left (Real.exp (-h)) ‖a‖)
        rwa [Real.log_exp] at this
      constructor <;> linarith [ih.1, ih.2]
    · rw [if_neg ha]
      have ha' : 1 < ‖a‖ := by simpa using ha
      have e2 : Real.log (max (Real.exp 0) ‖a‖) = Real.log ‖a‖ := by
        rw [Real.exp_zero, max_eq_right ha'.le]
      have e1 : Real.log ‖a‖ ≤ Real.log (max (Real.exp h) ‖a‖) :=
        Real.log_le_log (by linarith) (le_max_right _ _)
      have e3 : Real.log (max (Real.exp (-h)) ‖a‖) = Real.log ‖a‖ := by
        rw [max_eq_right]
        have : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        linarith
      constructor <;> linarith [ih.1, ih.2]

/-- `σ²_{n+1}(s) ≤ (n+1) e^{ns + n²s²/2}` (pair `k ↔ n − k` and use `cosh u ≤ e^{u²/2}`). -/
theorem jpm_aux_sig2_le (n : ℕ) (s : ℝ) :
    sig2 (n + 1) s ≤ (n + 1) * Real.exp (n * s + n ^ 2 * s ^ 2 / 2) := by
  have hsplit : sig2 (n + 1) s =
      Real.exp (n * s) * ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) := by
    rw [sig2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Real.exp_add]
    ring_nf
  have hrefl : ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) =
      ∑ k ∈ Finset.range (n + 1), Real.exp (-((2 * k - n) * s)) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    congr 1
    rw [show n + 1 - 1 - k = n - k by omega, Nat.cast_sub hk']
    ring
  have hcosh : ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) =
      ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s) := by
    have : 2 * ∑ k ∈ Finset.range (n + 1), Real.exp ((2 * k - n) * s) =
        2 * ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s) := by
      rw [two_mul]
      nth_rewrite 2 [hrefl]
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Real.cosh_eq]; ring
    linarith
  have hbound : ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s) ≤
      (n + 1) * Real.exp (n ^ 2 * s ^ 2 / 2) := by
    calc ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s)
        ≤ ∑ k ∈ Finset.range (n + 1), Real.exp (n ^ 2 * s ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk' : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          refine (Real.cosh_le_exp_half_sq _).trans (Real.exp_le_exp.mpr ?_)
          have : ((2 * k - n) * s) ^ 2 ≤ n ^ 2 * s ^ 2 := by
            rw [mul_pow]
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg s)
            nlinarith
          linarith
      _ = (n + 1) * Real.exp (n ^ 2 * s ^ 2 / 2) := by simp
  rw [hsplit, hcosh, Real.exp_add]
  calc Real.exp (n * s) * ∑ k ∈ Finset.range (n + 1), Real.cosh ((2 * k - n) * s)
      ≤ Real.exp (n * s) * ((n + 1) * Real.exp (n ^ 2 * s ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (n + 1) * (Real.exp (n * s) * Real.exp (n ^ 2 * s ^ 2 / 2)) := by ring

theorem jpm_aux_sig2_pos {N : ℕ} (hN : 1 ≤ N) (s : ℝ) : 0 < sig2 N s := by
  rw [sig2]
  exact Finset.sum_pos (fun k _ => Real.exp_pos _) (Finset.nonempty_range_iff.mpr (by omega))

theorem jpm_aux_sig2_zero (N : ℕ) : sig2 N 0 = N := by simp [sig2]

/-- `A(s) − A(0) ≤ ns/2 + n²s²/4` for `A(s) = ½ log σ²_{n+1}(s)`. -/
theorem jpm_aux_A_le (n : ℕ) (s : ℝ) :
    Real.log (sig2 (n + 1) s) / 2 - Real.log (sig2 (n + 1) 0) / 2 ≤
      n * s / 2 + n ^ 2 * s ^ 2 / 4 := by
  have h2 : Real.log (sig2 (n + 1) s) ≤
      Real.log ((n + 1) * Real.exp (n * s + n ^ 2 * s ^ 2 / 2)) :=
    Real.log_le_log (jpm_aux_sig2_pos (by omega) s) (jpm_aux_sig2_le n s)
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h2
  rw [jpm_aux_sig2_zero]
  push_cast
  linarith

/-- Deterministic main lemma, `±1` case. -/
theorem det_mainPM {n : ℕ} (x : Fin (n + 1) → Bool) (h κ E : ℝ) (hh : 0 < h)
    (hup : LamPM x h ≤ κ + E) (hdn : LamPM x (-h) ≤ κ + E) (hlo : κ - E ≤ LamPM x 0) :
    |(rootCountPM x : ℝ) - n / 2| ≤ n ^ 2 * h / 4 + 2 * E / h := by
  classical
  have hL : ∀ s, LamPM x s =
      ((polyPM x).roots.map (fun α => Real.log (max (Real.exp s) ‖α‖))).sum -
        Real.log (sig2 (n + 1) s) / 2 := by
    intro s
    rw [LamPM, jensen_polyPM (by omega) x s]
  obtain ⟨hs1, hs2⟩ := jpm_aux_secant (polyPM x).roots hh
  have hA1 := jpm_aux_A_le n h
  have hA2 := jpm_aux_A_le n (-h)
  rw [hL] at hup hdn hlo
  have hR : (rootCountPM x : ℝ) =
      ((polyPM x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) := by
    rfl
  rw [hR]
  have hB : h * (n ^ 2 * h / 4 + 2 * E / h) = n ^ 2 * h ^ 2 / 4 + 2 * E := by
    field_simp
  rw [abs_le]
  constructor
  · have : h * (-(n ^ 2 * h / 4 + 2 * E / h)) ≤
        h * (((polyPM x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) - n / 2) := by
      rw [mul_neg, hB]
      nlinarith
    exact le_of_mul_le_mul_left this hh
  · have : h * (((polyPM x).roots.countP (· ∈ Metric.closedBall (0 : ℂ) 1) : ℝ) - n / 2) ≤
        h * (n ^ 2 * h / 4 + 2 * E / h) := by
      rw [hB]
      nlinarith
    exact le_of_mul_le_mul_left this hh

theorem Wfun_eq_evalPM {N : ℕ} (x : Fin N → Bool) (s θ : ℝ) :
    Wfun (rho N s) x θ =
      ((1 / Real.sqrt (sig2 N s) : ℝ) : ℂ) * (polyPM x).eval (circleMap 0 (Real.exp s) θ) := by
  rw [polyPM_eval, Finset.mul_sum, Wfun]
  apply Finset.sum_congr rfl
  intro k _
  simp only [rho, ex, circleMap, zero_add]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
  push_cast
  ring_nf

theorem jpm_aux_circleIntegrable {N : ℕ} (x : Fin N → Bool) (R : ℝ) :
    CircleIntegrable (fun z => Real.log ‖(polyPM x).eval z‖) 0 R :=
  (analyticOnNhd_id.aeval_polynomial (polyPM x)).meromorphicOn.circleIntegrable_log_norm

theorem lam_eq_cavPM {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (s : ℝ) :
    LamPM x s = cav (fun θ => Real.log ‖Wfun (rho N s) x θ‖) := by
  have hsig : 0 < sig2 N s := jpm_aux_sig2_pos hN s
  have hR : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
  have hc : (0:ℝ) < 1 / Real.sqrt (sig2 N s) := by positivity
  have hae : ∀ᵐ θ ∂MeasureTheory.volume, θ ∈ Set.uIoc 0 (2 * π) →
      Real.log ‖Wfun (rho N s) x θ‖ = (-(Real.log (sig2 N s) / 2)) +
        Real.log ‖(polyPM x).eval (circleMap 0 (Real.exp s) θ)‖ := by
    filter_upwards [jpm_aux_ae_ne_zero hN x hR] with θ hθ _
    rw [Wfun_eq_evalPM, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le,
      Real.log_mul hc.ne' (norm_ne_zero_iff.mpr hθ), one_div, Real.log_inv,
      Real.log_sqrt hsig.le]
  have hint : IntervalIntegrable
      (fun θ => Real.log ‖(polyPM x).eval (circleMap 0 (Real.exp s) θ)‖)
      MeasureTheory.volume 0 (2 * π) := jpm_aux_circleIntegrable x _
  rw [cav, intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add intervalIntegrable_const hint, intervalIntegral.integral_const,
    LamPM, Real.circleAverage_def, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

theorem WPM_ne_zero_ae {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (s : ℝ) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.uIoc 0 (2 * π))), Wfun (rho N s) x θ ≠ 0 := by
  have hsig : 0 < sig2 N s := jpm_aux_sig2_pos hN s
  have hc : (0:ℝ) < 1 / Real.sqrt (sig2 N s) := by positivity
  apply MeasureTheory.ae_restrict_of_ae
  filter_upwards [jpm_aux_ae_ne_zero hN x (Real.exp_pos s).ne'] with θ hθ
  rw [Wfun_eq_evalPM]
  exact mul_ne_zero (by exact_mod_cast hc.ne') hθ

theorem Wfun_zero_evalPM {N : ℕ} (x : Fin N → Bool) (θ : ℝ) :
    Wfun (rho N 0) x θ = ((1 / Real.sqrt N : ℝ) : ℂ) * (polyPM x).eval (Complex.exp ((θ : ℂ) * I)) := by
  rw [Wfun_eq_evalPM, jpm_aux_sig2_zero, Real.exp_zero]
  congr 2
  simp [circleMap]

end E522

end

/- ## Section: `LogL2PM` -/

section

/-
# Deterministic `L²` bound for `log |f(e^{iθ})|`, `±1` polynomials

Adapt `Erdos522/LogL2.lean`: all roots satisfy `|α| < 2` (Cauchy bound: coefficients `±1`,
`‖lead‖ = 1`), and `log|f(e^{iθ})| = log‖lead‖ + ∑_α log|e^{iθ} − α| = ∑_α log|e^{iθ} − α|` a.e.
-/

/-
## Implementation notes

As in `Erdos522/LogL2.lean`: for every `0 ≤ ρ ≤ 2` one has `|e^{it} − ρ| ≥ |sin(t/2)|`
(`l2pm_aux_sin_le`), which gives `(log|e^{it} − ρ|)² ≤ 4 + 16 √π t^{-1/2}` on `(0, π]`
(`l2pm_aux_pt`), hence `∫_{-π}^{π} (log|e^{it} − ρ|)² ≤ 72π` (`l2pm_aux_sym`); rotation by
`arg α` and `2π`-periodicity transfer this to `∫_0^{2π} (log|e^{iθ} − α|)² ≤ 72π`
(`l2pm_aux_root`) for every root `α` (all satisfy `|α| ≤ 2`), so
`cav((log|f|)²) ≤ 36 d² ≤ 400 N²`.
-/

open Real Complex

namespace E522

/-- `‖e^{it} − ρ‖² = 1 − 2ρ cos t + ρ²`. -/
theorem l2pm_aux_norm_sq (ρ t : ℝ) :
    ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 = 1 - 2 * ρ * Real.cos t + ρ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero]
  linear_combination Real.sin_sq_add_cos_sq t

theorem l2pm_aux_sin_le {ρ : ℝ} (hρ : 0 ≤ ρ) (t : ℝ) :
    |Real.sin (t / 2)| ≤ ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ := by
  have h1 : Real.sin (t / 2) ^ 2 = 1 / 2 - Real.cos t / 2 := by
    rw [Real.sin_sq, Real.cos_sq, show 2 * (t / 2) = t by ring]; ring
  have h2 := l2pm_aux_norm_sq ρ t
  have hc1 := Real.neg_one_le_cos t
  have hc2 := Real.cos_le_one t
  have h3 : Real.sin (t / 2) ^ 2 ≤ ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 := by
    rw [h1, h2]
    rcases le_or_gt (Real.cos t) 0 with hc | hc
    · nlinarith [mul_nonneg hρ (neg_nonneg.mpr hc), sq_nonneg ρ]
    · nlinarith [sq_nonneg (ρ - Real.cos t),
        mul_nonneg (sub_nonneg.mpr hc2) (by linarith : (0:ℝ) ≤ 1 + 2 * Real.cos t)]
  exact (sq_le_sq.mp h3).trans_eq (abs_norm _)

theorem l2pm_aux_pt {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) {t : ℝ} (ht0 : 0 < t) (htπ : t ≤ π) :
    Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤
      4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)) := by
  set v := ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ with hv
  have hv3 : v ≤ 3 := by
    calc v ≤ ‖Complex.exp ((t : ℂ) * I)‖ + ‖(ρ : ℂ)‖ := norm_sub_le _ _
      _ = 1 + ρ := by rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hρ0]
      _ ≤ 3 := by linarith
  have hvt : t / π ≤ v := by
    have h1 := l2pm_aux_sin_le hρ0 t
    have h2 : 2 / π * (t / 2) ≤ Real.sin (t / 2) := Real.mul_le_sin (by linarith) (by linarith)
    have h3 : 2 / π * (t / 2) = t / π := by field_simp
    rw [h3] at h2
    exact h2.trans ((le_abs_self _).trans h1)
  have htπpos : 0 < t / π := div_pos ht0 Real.pi_pos
  have hvpos : 0 < v := htπpos.trans_le hvt
  have hsum_nonneg : 0 ≤ 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)) := by positivity
  rcases le_or_gt 1 v with hv1 | hv1
  · have hl0 : 0 ≤ Real.log v := Real.log_nonneg hv1
    have hl2 : Real.log v ≤ 2 := by
      have := Real.log_le_sub_one_of_pos hvpos
      linarith
    nlinarith
  · have hl : -Real.log v ≤ 4 * v ^ (-(1 / 4 : ℝ)) := by
      have := Real.log_le_rpow_div (inv_nonneg.mpr hvpos.le) (by norm_num : (0:ℝ) < 1 / 4)
      rw [Real.log_inv, Real.inv_rpow hvpos.le, ← Real.rpow_neg hvpos.le] at this
      linarith
    have hl0 : 0 ≤ -Real.log v := by
      have := Real.log_neg hvpos hv1
      linarith
    have hpow : (v ^ (-(1 / 4 : ℝ))) ^ 2 = v ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hvpos.le]
      norm_num
    have hsq : Real.log v ^ 2 ≤ 16 * v ^ (-(1 / 2 : ℝ)) := by
      have : (-Real.log v) ^ 2 ≤ (4 * v ^ (-(1 / 4 : ℝ))) ^ 2 := pow_le_pow_left₀ hl0 hl 2
      rw [neg_sq, mul_pow, hpow] at this
      linarith
    have hmono : v ^ (-(1 / 2 : ℝ)) ≤ (t / π) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos htπpos hvt (by norm_num)
    have heq : (t / π) ^ (-(1 / 2 : ℝ)) = Real.sqrt π * t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.div_rpow ht0.le Real.pi_pos.le, Real.rpow_neg Real.pi_pos.le,
        ← Real.sqrt_eq_rpow]
      field_simp
    rw [heq] at hmono
    nlinarith

theorem l2pm_aux_meas (ρ : ℝ) :
    Measurable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2) := by
  fun_prop

theorem l2pm_aux_half {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      MeasureTheory.volume 0 π ∧
    ∫ t in (0:ℝ)..π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤ 36 * π := by
  have hr : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) MeasureTheory.volume 0 π :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hg : IntervalIntegrable (fun t : ℝ => 4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)))
      MeasureTheory.volume 0 π :=
    intervalIntegrable_const.add (hr.const_mul _)
  have hle : ∀ t ∈ Set.Ioc 0 π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤
      4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ)) :=
    fun t ht => l2pm_aux_pt hρ0 hρ2 ht.1 ht.2
  have hf : IntervalIntegrable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      MeasureTheory.volume 0 π := by
    apply hg.mono_fun' (l2pm_aux_meas ρ).aestronglyMeasurable
    rw [Set.uIoc_of_le Real.pi_pos.le]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro t ht
    dsimp only
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hle t ht
  refine ⟨hf, ?_⟩
  calc ∫ t in (0:ℝ)..π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2
      ≤ ∫ t in (0:ℝ)..π, (4 + 16 * Real.sqrt π * t ^ (-(1 / 2 : ℝ))) :=
        intervalIntegral.integral_mono_on_of_le_Ioo Real.pi_pos.le hf hg
          (fun t ht => hle t ⟨ht.1, ht.2.le⟩)
    _ = 36 * π := by
        rw [intervalIntegral.integral_add intervalIntegrable_const (hr.const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by norm_num)), show (-(1 / 2 : ℝ)) + 1 = 1 / 2 by norm_num,
          Real.zero_rpow (by norm_num), ← Real.sqrt_eq_rpow]
        have := Real.mul_self_sqrt Real.pi_pos.le
        simp only [smul_eq_mul, sub_zero]
        nlinarith

theorem l2pm_aux_even (ρ t : ℝ) :
    ‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖ = ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ := by
  have h : ‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖ ^ 2 =
      ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 := by
    rw [l2pm_aux_norm_sq, l2pm_aux_norm_sq, Real.cos_neg]
  calc ‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖
      = Real.sqrt (‖Complex.exp (((-t : ℝ) : ℂ) * I) - (ρ : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2) := by rw [h]
    _ = ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ := Real.sqrt_sq (norm_nonneg _)

theorem l2pm_aux_sym {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      MeasureTheory.volume (-π) π ∧
    ∫ t in (-π)..π, Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 ≤ 72 * π := by
  obtain ⟨hi, hb⟩ := l2pm_aux_half hρ0 hρ2
  set G := fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2 with hG
  have heven : ∀ t, G (-t) = G t := fun t => by simp only [hG]; rw [l2pm_aux_even]
  have hi' : IntervalIntegrable G MeasureTheory.volume (-π) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simp only [neg_neg, neg_zero, heven]
    exact hi.symm
  have hint : ∫ t in (-π)..0, G t = ∫ t in (0:ℝ)..π, G t := by
    have := intervalIntegral.integral_comp_neg (a := -π) (b := 0) G
    simp only [heven, neg_zero, neg_neg] at this
    exact this
  refine ⟨hi'.trans hi, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hi' hi, hint]
  linarith

theorem l2pm_aux_periodic (ρ : ℝ) :
    Function.Periodic (fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - (ρ : ℂ)‖ ^ 2)
      (2 * π) := by
  intro t
  simp only
  have : Complex.exp (((t + 2 * π : ℝ) : ℂ) * I) = Complex.exp ((t : ℂ) * I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add]
    have h2 : Complex.exp (((2 * π : ℝ) : ℂ) * I) = 1 := by
      push_cast
      exact Complex.exp_two_pi_mul_I
    rw [h2, mul_one]
  rw [this]

theorem l2pm_aux_rot (α : ℂ) (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * I) - α‖ =
      ‖Complex.exp (((θ - Complex.arg α : ℝ) : ℂ) * I) - ((‖α‖ : ℝ) : ℂ)‖ := by
  have hθ : Complex.exp ((θ : ℂ) * I) = Complex.exp ((Complex.arg α : ℂ) * I) *
      Complex.exp (((θ - Complex.arg α : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have key : Complex.exp ((θ : ℂ) * I) - α = Complex.exp ((Complex.arg α : ℂ) * I) *
      (Complex.exp (((θ - Complex.arg α : ℝ) : ℂ) * I) - ((‖α‖ : ℝ) : ℂ)) := by
    rw [mul_sub, ← hθ]
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I α]
    ring
  rw [key, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem l2pm_aux_root {α : ℂ} (hα : ‖α‖ ≤ 2) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)
      MeasureTheory.volume 0 (2 * π) ∧
    ∫ θ in (0:ℝ)..(2 * π), Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2 ≤ 72 * π := by
  obtain ⟨hi, hb⟩ := l2pm_aux_sym (norm_nonneg α) hα
  set G := fun t : ℝ => Real.log ‖Complex.exp ((t : ℂ) * I) - ((‖α‖ : ℝ) : ℂ)‖ ^ 2 with hG
  have hper : Function.Periodic G (2 * π) := l2pm_aux_periodic ‖α‖
  have hfun : (fun θ : ℝ => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2) =
      fun θ => G (θ - Complex.arg α) := by
    funext θ
    simp only [hG]
    rw [l2pm_aux_rot]
  rw [hfun]
  have hi2 : IntervalIntegrable G MeasureTheory.volume (-π) (-π + 2 * π) := by
    rw [show -π + 2 * π = π by ring]
    exact hi
  have hall : ∀ a b, IntervalIntegrable G MeasureTheory.volume a b :=
    fun a b => hper.intervalIntegrable (by positivity) hi2 a b
  constructor
  · have := (hall (0 - Complex.arg α) (2 * π - Complex.arg α)).comp_sub_right (Complex.arg α)
    simpa using this
  · rw [intervalIntegral.integral_comp_sub_right]
    have := hper.intervalIntegral_add_eq (0 - Complex.arg α) (-π)
    rw [show 0 - Complex.arg α + 2 * π = 2 * π - Complex.arg α by ring,
      show -π + 2 * π = π by ring] at this
    rw [this]
    exact hb

theorem l2pm_aux_sq_sum_le (S : Multiset ℂ) (u : ℂ → ℝ) :
    (S.map u).sum ^ 2 ≤ (Multiset.card S : ℝ) * (S.map (fun a => u a ^ 2)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    push_cast
    set s := (S.map u).sum
    set t := (S.map (fun a => u a ^ 2)).sum
    set k := (Multiset.card S : ℝ)
    have ht : 0 ≤ t := Multiset.sum_nonneg (fun y hy => by
      obtain ⟨b, _, rfl⟩ := Multiset.mem_map.mp hy
      positivity)
    have hk : 0 ≤ k := Nat.cast_nonneg _
    have key : 2 * u a * s ≤ k * u a ^ 2 + t := by
      rcases eq_or_lt_of_le hk with hk0 | hkpos
      · rw [← hk0] at ih
        have : s = 0 := by nlinarith [sq_nonneg s]
        rw [this, ← hk0]
        nlinarith
      · have h1 : 0 ≤ k * (k * u a ^ 2 + t - 2 * u a * s) := by
          nlinarith [sq_nonneg (k * u a - s)]
        have h2 : 0 ≤ k * u a ^ 2 + t - 2 * u a * s := (mul_nonneg_iff_of_pos_left hkpos).mp h1
        linarith
    nlinarith

theorem l2pm_aux_int_sum (S : Multiset ℂ) (hS : ∀ α ∈ S, ‖α‖ ≤ 2) :
    IntervalIntegrable
      (fun θ : ℝ => (S.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum)
      MeasureTheory.volume 0 (2 * π) ∧
    ∫ θ in (0:ℝ)..(2 * π), (S.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum
      ≤ (Multiset.card S : ℝ) * (72 * π) := by
  induction S using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.sum_zero, Multiset.card_zero]
    exact ⟨intervalIntegrable_const, by simp⟩
  | cons a S ih =>
    have ha := l2pm_aux_root (hS a (Multiset.mem_cons_self a S))
    have ih' := ih (fun α hα => hS α (Multiset.mem_cons_of_mem hα))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    refine ⟨ha.1.add ih'.1, ?_⟩
    rw [intervalIntegral.integral_add ha.1 ih'.1]
    push_cast
    linarith [ha.2, ih'.2]

/-- Explicit coefficients of `polyPM x`. -/
theorem l2pm_aux_coeff {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (polyPM x).coeff m = if h : m < N then ((sgn (x ⟨m, h⟩) : ℝ) : ℂ) else 0 := by
  simp only [polyPM, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨m, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hbm
      exact hb (Fin.ext hbm)
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [if_neg]
    intro hbm
    exact h (hbm ▸ b.2)

/-- Every coefficient of `polyPM x` is `0` or has norm `1`. -/
theorem l2pm_aux_coeff_mem {N : ℕ} (x : Fin N → Bool) (m : ℕ) :
    (polyPM x).coeff m = 0 ∨ ‖(polyPM x).coeff m‖ = 1 := by
  rw [l2pm_aux_coeff]
  split_ifs with h
  · right
    rw [Complex.norm_real, Real.norm_eq_abs, abs_sgn]
  · left
    rfl

theorem l2pm_aux_ne_zero {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) : polyPM x ≠ 0 := by
  intro h0
  have h := l2pm_aux_coeff x 0
  rw [h0, dif_pos (by omega : 0 < N), Polynomial.coeff_zero] at h
  have h2 := congrArg (fun z : ℂ => ‖z‖) h
  simp only [norm_zero, Complex.norm_real, Real.norm_eq_abs, abs_sgn] at h2
  exact zero_ne_one h2

theorem l2pm_aux_norm_leadingCoeff {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    ‖(polyPM x).leadingCoeff‖ = 1 := by
  rcases l2pm_aux_coeff_mem x (polyPM x).natDegree with h | h
  · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr (l2pm_aux_ne_zero hN x))
  · exact h

theorem l2pm_aux_natDegree_le {N : ℕ} (x : Fin N → Bool) : (polyPM x).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [l2pm_aux_coeff, dif_neg]
  intro h
  exact absurd (lt_trans h hm) (lt_irrefl _)

/-- Every root of a `±1` polynomial has modulus `< 2` (Cauchy bound). -/
theorem l2pm_aux_root_norm_le {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (α : ℂ)
    (hα : α ∈ (polyPM x).roots) : ‖α‖ ≤ 2 := by
  have hx := l2pm_aux_ne_zero hN x
  have h1 := Polynomial.IsRoot.norm_lt_cauchyBound hx ((Polynomial.mem_roots hx).mp hα)
  have h2 : Polynomial.cauchyBound (polyPM x) ≤ 2 := by
    unfold Polynomial.cauchyBound
    have hl : ‖(polyPM x).leadingCoeff‖₊ = 1 := by
      rw [← NNReal.coe_inj, coe_nnnorm, l2pm_aux_norm_leadingCoeff hN x, NNReal.coe_one]
    rw [hl, div_one]
    have : (Finset.range (polyPM x).natDegree).sup (fun i => ‖(polyPM x).coeff i‖₊) ≤ 1 := by
      apply Finset.sup_le
      intro i _
      rcases l2pm_aux_coeff_mem x i with h | h
      · simp [h]
      · rw [← NNReal.coe_le_coe, coe_nnnorm, h, NNReal.coe_one]
    calc _ ≤ (1 : NNReal) + 1 := by gcongr
      _ = 2 := by norm_num
  have h3 : ‖α‖₊ < 2 := lt_of_lt_of_le h1 h2
  have h4 : ‖α‖ < 2 := by
    rw [← coe_nnnorm]
    exact_mod_cast h3
  exact h4.le

theorem l2pm_aux_log_norm_prod (S : Multiset ℂ) (z : ℂ) (hz : (S.map (z - ·)).prod ≠ 0) :
    Real.log ‖(S.map (z - ·)).prod‖ = (S.map (fun α => Real.log ‖z - α‖)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons] at hz ⊢
    have h1 : z - a ≠ 0 := left_ne_zero_of_mul hz
    have h2 : (S.map (z - ·)).prod ≠ 0 := right_ne_zero_of_mul hz
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2), ih h2]

/-- Off the zeros, `log |f(z)| = log ‖lead‖ + ∑_α log |z − α| = ∑_α log |z − α|`. -/
theorem l2pm_aux_log_eval {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (z : ℂ)
    (hz : (polyPM x).eval z ≠ 0) :
    Real.log ‖(polyPM x).eval z‖ = ((polyPM x).roots.map (fun α => Real.log ‖z - α‖)).sum := by
  have h := (IsAlgClosed.splits (polyPM x)).eval_eq_prod_roots z
  rw [h] at hz ⊢
  have hp : ((polyPM x).roots.map (z - ·)).prod ≠ 0 := right_ne_zero_of_mul hz
  rw [norm_mul, l2pm_aux_norm_leadingCoeff hN x, one_mul]
  exact l2pm_aux_log_norm_prod _ z hp

theorem l2pm_aux_ae_ne_zero {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    ∀ᵐ θ : ℝ ∂MeasureTheory.volume, (polyPM x).eval (Complex.exp ((θ : ℂ) * I)) ≠ 0 := by
  have hx := l2pm_aux_ne_zero hN x
  have hc : (circleMap 0 1 ⁻¹' {z | (polyPM x).IsRoot z}).Countable := by
    apply Set.Countable.preimage_circleMap _ 0 one_ne_zero
    exact ((polyPM x).roots.finite_toSet.subset
      (fun z hz => (Polynomial.mem_roots hx).mpr hz)).countable
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ (hc.measure_zero _)
  intro θ hθ
  simpa [circleMap] using hθ

theorem l2pm_aux_pointwise {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    ∀ᵐ θ : ℝ ∂MeasureTheory.volume, Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2 ≤
      (Multiset.card (polyPM x).roots : ℝ) *
        ((polyPM x).roots.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum := by
  filter_upwards [l2pm_aux_ae_ne_zero hN x] with θ hθ
  rw [l2pm_aux_log_eval hN x _ hθ]
  exact l2pm_aux_sq_sum_le _ _

theorem l2pm_aux_meas_poly {N : ℕ} (x : Fin N → Bool) :
    Measurable (fun θ : ℝ => Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2) := by
  have : Continuous (fun θ : ℝ => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖) := by
    fun_prop
  exact (Real.measurable_log.comp this.measurable).pow_const 2

/-- Integrability of `θ ↦ (log |f(e^{iθ})|)²` (dominated by `d · ∑_α (log|e^{iθ} − α|)²`). -/
theorem l2pm_aux_log_sq_intervalIntegrable {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    IntervalIntegrable (fun θ => Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2)
      MeasureTheory.volume 0 (2 * π) := by
  have hS := l2pm_aux_int_sum (polyPM x).roots (fun α hα => l2pm_aux_root_norm_le hN x α hα)
  apply (hS.1.const_mul (Multiset.card (polyPM x).roots : ℝ)).mono_fun'
  · exact (l2pm_aux_meas_poly x).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_ae ?_
    filter_upwards [l2pm_aux_pointwise hN x] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hθ

theorem log_sq_boundPM {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    cav (fun θ => Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2) ≤ 400 * N ^ 2 := by
  have hS := l2pm_aux_int_sum (polyPM x).roots (fun α hα => l2pm_aux_root_norm_le hN x α hα)
  have hcard : (Multiset.card (polyPM x).roots : ℝ) ≤ N := by
    have h1 := Polynomial.card_roots' (polyPM x)
    have h2 : (polyPM x).natDegree ≤ N := l2pm_aux_natDegree_le x
    exact_mod_cast h1.trans h2
  set d := (Multiset.card (polyPM x).roots : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hint := l2pm_aux_log_sq_intervalIntegrable hN x
  have hmono : ∫ θ in (0:ℝ)..(2 * π), Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2
      ≤ ∫ θ in (0:ℝ)..(2 * π), d *
        ((polyPM x).roots.map (fun α => Real.log ‖Complex.exp ((θ : ℂ) * I) - α‖ ^ 2)).sum :=
    intervalIntegral.integral_mono_ae (by positivity) hint (hS.1.const_mul d)
      (l2pm_aux_pointwise hN x)
  rw [intervalIntegral.integral_const_mul] at hmono
  have h2 := mul_le_mul_of_nonneg_left hS.2 hd0
  have hπ : 0 < π := Real.pi_pos
  unfold cav
  calc (2 * π)⁻¹ * ∫ θ in (0:ℝ)..(2 * π),
        Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2
      ≤ (2 * π)⁻¹ * (d * (d * (72 * π))) :=
        mul_le_mul_of_nonneg_left (hmono.trans h2) (by positivity)
    _ = 36 * d ^ 2 := by field_simp; ring
    _ ≤ 36 * N ^ 2 := by gcongr
    _ ≤ 400 * N ^ 2 := by nlinarith [sq_nonneg (N : ℝ)]

theorem log_sq_intervalIntegrablePM {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) :
    IntervalIntegrable (fun θ => Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ ^ 2)
      MeasureTheory.volume 0 (2 * π) :=
  l2pm_aux_log_sq_intervalIntegrable hN x

end E522

end

/- ## Section: `SmallBallPM` -/

section

/-
# Super-polynomially small balls, `±1` polynomials

Adapt `Erdos522/SmallBall.lean`. With threshold `2ε`: two distinct choices `u ≠ u'` of the first
`K` signs with `|f| < 2ε` give `|∑_{j<K} (sgn u_j − sgn u'_j) e^{ijθ}| < 4ε`, i.e.
`|∑_{j<K} c_j e^{ijθ}| < 2ε` with `c = (sgn u − sgn u')/2 ∈ {−1,0,1}^K \ 0` — the SAME bad set
as in the `0/1` case, whose normalised measure is `≤ 3^K · K · (2ε)^{1/K}`.
-/

open Real Complex MeasureTheory

namespace E522

lemma sbpm_aux_eval_polyPM {N : ℕ} (x : Fin N → Bool) (z : ℂ) :
    (polyPM x).eval z = ∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * z ^ (k : ℕ) := by
  simp [polyPM, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- Separation, `±1` case: if all nonzero `{-1,0,1}` combinations of `1, z, …, z^{K-1}` have
norm `≥ 2ε`, then at most a `2^{-K}` fraction of the cube has `|f_x(z)| < 2ε`. -/
lemma sbpm_aux_sep {N K : ℕ} (hKN : K ≤ N) (ε : ℝ) (z : ℂ)
    (hz : ∀ c ∈ sb_aux_S K, 2 * ε ≤ ‖∑ j : Fin K, (c j : ℂ) * z ^ (j : ℕ)‖) :
    cubeProb N (fun x => ‖(polyPM x).eval z‖ < 2 * ε) ≤ (1 / 2) ^ K := by
  classical
  unfold cubeProb
  set s := Finset.univ.filter (fun x : Fin N → Bool => ‖(polyPM x).eval z‖ < 2 * ε) with hs
  let f : (Fin N → Bool) → (Fin (N - K) → Bool) := fun x i => x ⟨(i : ℕ) + K, by omega⟩
  have hinj : Set.InjOn f s := by
    intro x hx x' hx' hfx
    simp only [hs, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hx'
    -- half the difference vector
    let c : Fin K → ℤ := fun j =>
      (if x (Fin.castLE hKN j) then 1 else 0) - (if x' (Fin.castLE hKN j) then 1 else 0)
    have hcmem : c ∈ Fintype.piFinset fun _ => ({-1, 0, 1} : Finset ℤ) := by
      rw [Fintype.mem_piFinset]
      intro j
      simp only [c]
      split_ifs <;> simp
    have hsame : ∀ k : Fin N, K ≤ (k : ℕ) → x k = x' k := by
      intro k hk
      have := congrFun hfx ⟨(k : ℕ) - K, by omega⟩
      simp only [f] at this
      have hk' : (⟨(k : ℕ) - K + K, by omega⟩ : Fin N) = k := Fin.ext (by simp; omega)
      rwa [hk'] at this
    have hdiff : (polyPM x).eval z - (polyPM x').eval z =
        2 * ∑ j : Fin K, (c j : ℂ) * z ^ (j : ℕ) := by
      rw [sbpm_aux_eval_polyPM, sbpm_aux_eval_polyPM, ← Finset.sum_sub_distrib]
      rw [sb_aux_sum_castLE hKN, Finset.mul_sum]
      · apply Finset.sum_congr rfl
        intro j _
        simp only [c, sgn, Fin.val_castLE]
        split_ifs <;> push_cast <;> ring
      · intro k hk
        rw [hsame k hk, sub_self]
    have hc0 : c = 0 := by
      by_contra hne
      have h1 := hz c (Finset.mem_erase.2 ⟨hne, hcmem⟩)
      have h2 : ‖(polyPM x).eval z - (polyPM x').eval z‖ < 4 * ε := by
        calc ‖(polyPM x).eval z - (polyPM x').eval z‖
            ≤ ‖(polyPM x).eval z‖ + ‖(polyPM x').eval z‖ := norm_sub_le _ _
          _ < 2 * ε + 2 * ε := add_lt_add hx hx'
          _ = 4 * ε := by ring
      rw [hdiff, norm_mul] at h2
      have h22 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h22] at h2
      linarith
    funext k
    by_cases hk : (k : ℕ) < K
    · have h1 := congrFun hc0 ⟨k, hk⟩
      simp only [c, Pi.zero_apply] at h1
      have hk' : Fin.castLE hKN ⟨(k : ℕ), hk⟩ = k := Fin.ext rfl
      rw [hk'] at h1
      cases hxk : x k <;> cases hx'k : x' k <;> simp_all
    · exact hsame k (by omega)
  have hcard : s.card ≤ 2 ^ (N - K) := by
    have := Finset.card_le_card_of_injOn f (t := Finset.univ) (fun _ _ => Finset.mem_coe.2
      (Finset.mem_univ _)) hinj
    simpa using this
  have h2N : (2:ℝ) ^ N = 2 ^ (N - K) * 2 ^ K := by
    rw [← pow_add, Nat.sub_add_cancel hKN]
  rw [div_le_iff₀ (by positivity), h2N]
  have : ((s.card : ℕ) : ℝ) ≤ 2 ^ (N - K) := by exact_mod_cast hcard
  calc ((s.card : ℕ) : ℝ) ≤ 2 ^ (N - K) := this
    _ = (1 / 2) ^ K * (2 ^ (N - K) * 2 ^ K) := by
        rw [one_div, inv_pow]; field_simp

/-- `cubeProb` of the small-value event as an average of indicators. -/
lemma sbpm_aux_cubeProb_eq {N : ℕ} (ε : ℝ) (θ : ℝ) :
    cubeProb N (fun x => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε) =
      (∑ x : Fin N → Bool, smallIndPM x ε θ) / 2 ^ N := by
  classical
  unfold cubeProb smallIndPM
  rw [Finset.natCast_card_filter]

lemma sbpm_aux_ii_smallInd {N : ℕ} (x : Fin N → Bool) (ε a b : ℝ) :
    IntervalIntegrable (smallIndPM x ε) volume a b := by
  unfold smallIndPM
  apply sb_aux_ii_lt (h := fun θ : ℝ => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖) _
    (2 * ε) a b
  exact ((polyPM x).continuous.comp (by fun_prop)).norm

lemma sbpm_aux_ii_cubeProb {N : ℕ} (ε a b : ℝ) :
    IntervalIntegrable (fun θ : ℝ =>
      cubeProb N (fun x => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε)) volume a b := by
  simp_rw [sbpm_aux_cubeProb_eq]
  apply IntervalIntegrable.div_const
  exact sb_aux_ii_sum (Finset.univ : Finset (Fin N → Bool))
    (F := fun x θ => smallIndPM x ε θ) (fun x _ => sbpm_aux_ii_smallInd x ε a b)

theorem small_ball_sepPM {N K : ℕ} (hK1 : 1 ≤ K) (hKN : K ≤ N) (ε : ℝ) (hε : 0 < ε)
    (hε2 : 2 * ε < 1) :
    cav (fun θ => cubeProb N (fun x =>
        ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε)) ≤
      (1 / 2) ^ K + 3 ^ K * K * (2 * ε) ^ ((1 : ℝ) / K) := by
  classical
  set ρ := (2 * ε) ^ ((1:ℝ) / K) with hρ
  set S := sb_aux_S K with hS
  set Ic : (Fin K → ℤ) → ℝ → ℝ := fun c θ =>
    if ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < 2 * ε
      then (1:ℝ) else 0 with hIc
  have hIc_nonneg : ∀ c θ, 0 ≤ Ic c θ := fun c θ => by
    simp only [hIc]; split_ifs <;> norm_num
  have hpt : ∀ θ : ℝ,
      cubeProb N (fun x => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε) ≤
      (1 / 2) ^ K + ∑ c ∈ S, Ic c θ := by
    intro θ
    by_cases hB : ∃ c ∈ S,
        ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖ < 2 * ε
    · obtain ⟨c, hcS, hc⟩ := hB
      have h1 : cubeProb N (fun x => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε)
          ≤ 1 := by
        unfold cubeProb
        rw [div_le_one (by positivity)]
        have := Finset.card_filter_le (Finset.univ : Finset (Fin N → Bool))
          (fun x => ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε)
        have h2 : ((Finset.univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
          simp
        rw [← h2]
        exact_mod_cast this
      have h2 : 1 ≤ ∑ c ∈ S, Ic c θ := by
        calc (1:ℝ) = Ic c θ := by simp only [hIc]; rw [if_pos hc]
          _ ≤ ∑ c ∈ S, Ic c θ :=
            Finset.single_le_sum (f := fun c => Ic c θ) (fun c _ => hIc_nonneg c θ) hcS
      have h3 : (0:ℝ) ≤ (1 / 2) ^ K := by positivity
      linarith
    · push Not at hB
      have h1 := sbpm_aux_sep hKN ε (Complex.exp ((θ : ℂ) * I)) hB
      have h2 : 0 ≤ ∑ c ∈ S, Ic c θ := Finset.sum_nonneg (fun c _ => hIc_nonneg c θ)
      linarith
  have hIIc : ∀ c ∈ S, IntervalIntegrable (Ic c) volume 0 (2 * π) := by
    intro c _
    exact sb_aux_ii_lt (h := fun θ : ℝ =>
      ‖∑ j : Fin K, (c j : ℂ) * (Complex.exp ((θ : ℂ) * I)) ^ (j : ℕ)‖) (by fun_prop)
      (2 * ε) 0 (2 * π)
  have hIIsum : IntervalIntegrable (fun θ => ∑ c ∈ S, Ic c θ) volume 0 (2 * π) := by
    exact sb_aux_ii_sum S hIIc
  have hIIconst : IntervalIntegrable (fun _ : ℝ => ((1:ℝ) / 2) ^ K) volume 0 (2 * π) :=
    intervalIntegrable_const
  have hc_bound : ∀ c ∈ S, cav (Ic c) ≤ K * ρ := by
    intro c hc
    have hc0 : c ≠ 0 := (Finset.mem_erase.1 hc).1
    exact sb_aux_bad_c hK1 c hc0 (by positivity) hε2
  calc cav (fun θ => cubeProb N (fun x =>
        ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε))
      ≤ cav (fun θ => (1 / 2) ^ K + ∑ c ∈ S, Ic c θ) :=
        sb_aux_cav_mono (sbpm_aux_ii_cubeProb ε 0 (2 * π)) (hIIconst.add hIIsum) hpt
    _ = (1 / 2) ^ K + ∑ c ∈ S, cav (Ic c) := by
        rw [sb_aux_cav_add hIIconst hIIsum, sb_aux_cav_const, sb_aux_cav_sum S hIIc]
    _ ≤ (1 / 2) ^ K + ∑ c ∈ S, (K * ρ) := by
        gcongr with c hc
        exact hc_bound c hc
    _ = (1 / 2) ^ K + S.card * (K * ρ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / 2) ^ K + 3 ^ K * K * ρ := by
        have hS3 : (S.card : ℝ) ≤ 3 ^ K := by exact_mod_cast sb_aux_S_card K
        have hKρ : 0 ≤ (K : ℝ) * ρ := by positivity
        nlinarith

theorem cav_cubeProb_eqPM {N : ℕ} (ε : ℝ) :
    cav (fun θ => cubeProb N (fun x =>
        ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖ < 2 * ε)) =
      cubeAvg N (fun x => cav (smallIndPM x ε)) := by
  unfold cav cubeAvg
  simp_rw [sbpm_aux_cubeProb_eq]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_finsetSum (fun x _ => sbpm_aux_ii_smallInd x ε 0 (2 * π)),
    ← Finset.mul_sum]
  ring

end E522

end

/- ## Section: `TransferPM` -/

section

/-
# Transfer for the `±1` statement

Adapt `Erdos522/Transfer.lean` with `count[|{-1,1}]` instead of `count[|{0,1}]`
(reuse `bitsOf`, `rawCount`, `measurable_bitsOf`; for `x i ∈ {-1,1}`,
`sgn (decide (x i = 1)) = x i`).
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace E522

noncomputable section

/-- The law of one `±1` coefficient: uniform on `{-1,1}` with respect to counting measure. -/
abbrev trpm_aux_coinLaw : Measure ℂ := Measure.count[|({-1, 1} : Set ℂ)]

lemma trpm_aux_neg_one_ne_one : (-1 : ℂ) ≠ 1 := by norm_num

lemma trpm_aux_measurableSet_pm : MeasurableSet ({-1, 1} : Set ℂ) :=
  (Set.toFinite _).measurableSet

lemma trpm_aux_count_pm : Measure.count ({-1, 1} : Set ℂ) = 2 := by
  rw [Measure.count_apply_finite _ (Set.toFinite _)]
  have : (Set.toFinite ({-1, 1} : Set ℂ)).toFinset = {-1, 1} := by
    ext z; simp
  rw [this, Finset.card_pair trpm_aux_neg_one_ne_one]
  simp

instance trpm_aux_coinLaw_isProb : IsProbabilityMeasure trpm_aux_coinLaw :=
  cond_isProbabilityMeasure_of_finite (by rw [trpm_aux_count_pm]; norm_num)
    (by rw [trpm_aux_count_pm]; norm_num)

lemma trpm_aux_coinLaw_apply (t : Set ℂ) :
    trpm_aux_coinLaw t = (1 / 2 : ENNReal) * Measure.count (({-1, 1} : Set ℂ) ∩ t) := by
  rw [trpm_aux_coinLaw, cond_apply trpm_aux_measurableSet_pm, trpm_aux_count_pm]
  simp

lemma trpm_aux_coinLaw_compl : trpm_aux_coinLaw ({-1, 1} : Set ℂ)ᶜ = 0 := by
  rw [trpm_aux_coinLaw_apply]; simp

lemma trpm_aux_coinLaw_eq_one : trpm_aux_coinLaw {z : ℂ | decide (z = 1) = true} = 1 / 2 := by
  rw [trpm_aux_coinLaw_apply]
  have : ({-1, 1} : Set ℂ) ∩ {z : ℂ | decide (z = 1) = true} = {1} := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro rfl; exact ⟨Or.inr rfl, rfl⟩
  rw [this, Measure.count_singleton]
  simp

lemma trpm_aux_coinLaw_eq_zero : trpm_aux_coinLaw {z : ℂ | decide (z = 1) = false} = 1 / 2 := by
  rw [trpm_aux_coinLaw_apply]
  have : ({-1, 1} : Set ℂ) ∩ {z : ℂ | decide (z = 1) = false} = {-1} := by
    ext z; simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_ofPred_eq, decide_eq_false_iff_not]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact h
      · exact absurd h h'
    · rintro rfl; exact ⟨Or.inl rfl, trpm_aux_neg_one_ne_one⟩
  rw [this, Measure.count_singleton]
  simp

lemma trpm_aux_coinLaw_bit (b : Bool) :
    trpm_aux_coinLaw {z : ℂ | decide (z = 1) = b} = 1 / 2 := by
  cases b
  · exact trpm_aux_coinLaw_eq_zero
  · exact trpm_aux_coinLaw_eq_one

/-- The product law of the `±1` coefficient sequence. -/
abbrev trpm_aux_nuLaw : Measure (ℕ → ℂ) := Measure.infinitePi (fun _ : ℕ => trpm_aux_coinLaw)

lemma trpm_aux_nuLaw_bitsOf_eq (N : ℕ) (a : Fin N → Bool) :
    trpm_aux_nuLaw {x | bitsOf N x = a} = (1 / 2 : ENNReal) ^ N := by
  classical
  let t : ℕ → Set ℂ := fun k =>
    if h : k < N then {z : ℂ | decide (z = 1) = a ⟨k, h⟩} else Set.univ
  have hset : {x : ℕ → ℂ | bitsOf N x = a} = ((Finset.range N : Finset ℕ) : Set ℕ).pi t := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.coe_range, Set.mem_Iio, t]
    constructor
    · intro h k hk
      rw [dif_pos hk]
      have := congrFun h ⟨k, hk⟩
      simpa [bitsOf] using this
    · intro h
      funext k
      have := h k k.2
      rw [dif_pos k.2] at this
      simpa [bitsOf] using this
  rw [hset, Measure.infinitePi_pi]
  · rw [Finset.prod_congr rfl (g := fun _ => (1 / 2 : ENNReal))]
    · simp
    · intro k hk
      have hk' : k < N := Finset.mem_range.mp hk
      simp only [t, dif_pos hk']
      exact trpm_aux_coinLaw_bit _
  · intro k _
    simp only [t]
    split_ifs with hk
    · exact measurableSet_decide_eq _
    · exact MeasurableSet.univ

lemma trpm_aux_nuLaw_bitsOf_mem (N : ℕ) (P : (Fin N → Bool) → Prop) :
    trpm_aux_nuLaw {x | P (bitsOf N x)} = ENNReal.ofReal (cubeProb N P) := by
  classical
  have hset : {x : ℕ → ℂ | P (bitsOf N x)} =
      ⋃ a ∈ (Finset.univ.filter P : Finset (Fin N → Bool)), {x | bitsOf N x = a} := by
    ext x; simp
  rw [hset, measure_biUnion_finset]
  · rw [Finset.sum_congr rfl (fun a _ => trpm_aux_nuLaw_bitsOf_eq N a)]
    rw [Finset.sum_const, nsmul_eq_mul, cubeProb]
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    rw [ENNReal.ofReal_natCast]
    rw [div_eq_mul_inv]
    congr 1
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    rw [one_mul, ENNReal.inv_pow]
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hab (hx.symm.trans hx')
  · intro a _
    exact measurable_bitsOf N (measurableSet_singleton a)

lemma trpm_aux_polyPM_bitsOf (x : ℕ → ℂ) (hx : ∀ i, x i = -1 ∨ x i = 1) (n : ℕ) :
    polyPM (bitsOf (n + 1) x) = ∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (x i) := by
  rw [polyPM, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (x i))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  rcases hx k with h | h <;> simp [bitsOf, sgn, h, trpm_aux_neg_one_ne_one]

lemma trpm_aux_rawCount_eq (x : ℕ → ℂ) (hx : ∀ i, x i = -1 ∨ x i = 1) (n : ℕ) :
    rawCount x n = rootCountPM (bitsOf (n + 1) x) := by
  rw [rawCount, rootCountPM, trpm_aux_polyPM_bitsOf x hx n]

end

theorem transferPM {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    (c : ℕ → Ω → ℂ) (h_indep : iIndepFun c ℙ)
    (h_unif : ∀ i, MeasureTheory.pdf.IsUniform (c i) ({-1, 1} : Set ℂ) ℙ Measure.count)
    (hsum : ∀ m : ℕ, Summable (fun n : ℕ =>
      cubeProb (n + 1) (fun x => (1 : ℝ) / (m + 1) < |(2 * rootCountPM x : ℝ) / n - 1|))) :
    ℙ {ω | Tendsto (fun n : ℕ => (2 * rawCount (fun i => c i ω) n : ℝ) / n) atTop (𝓝 1)} = 1 := by
  -- each coefficient is a.e.-measurable with law `trpm_aux_coinLaw`
  have hlaw : ∀ i, Measure.map (c i) ℙ = trpm_aux_coinLaw := fun i => (h_unif i).map_eq
  have hmeas : ∀ i, AEMeasurable (c i) ℙ := fun i => (h_unif i).aemeasurable
  set X : Ω → ℕ → ℂ := fun ω i => c i ω with hX
  have hXm : AEMeasurable X ℙ := AEMeasurable.of_eval hmeas
  have hmap : Measure.map X ℙ = trpm_aux_nuLaw := by
    rw [h_indep.map_fun_eq_infinitePi_map₀ hXm]
    congr 1
    funext i
    exact hlaw i
  -- almost every sequence is `{-1,1}`-valued
  have hpm : ∀ᵐ x ∂trpm_aux_nuLaw, ∀ i, x i = -1 ∨ x i = 1 := by
    rw [ae_all_iff]
    intro i
    have hev : Measure.map (fun x : ℕ → ℂ => x i) trpm_aux_nuLaw = trpm_aux_coinLaw :=
      Measure.infinitePi_map_eval _ i
    have : ∀ᵐ z ∂trpm_aux_coinLaw, z = -1 ∨ z = 1 := by
      rw [ae_iff]
      have hs : {z : ℂ | ¬(z = -1 ∨ z = 1)} = ({-1, 1} : Set ℂ)ᶜ := by
        ext z; simp
      rw [hs]; exact trpm_aux_coinLaw_compl
    rw [← hev] at this
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable this
  -- Borel–Cantelli for each tolerance
  have hBC : ∀ m : ℕ, ∀ᵐ x ∂trpm_aux_nuLaw, ∀ᶠ n in atTop,
      x ∉ {y : ℕ → ℂ | (1 : ℝ) / (m + 1) <
        |(2 * rootCountPM (bitsOf (n + 1) y) : ℝ) / n - 1|} := by
    intro m
    apply ae_eventually_notMem
    have hterm : ∀ n : ℕ, trpm_aux_nuLaw {y : ℕ → ℂ | (1 : ℝ) / (m + 1) <
        |(2 * rootCountPM (bitsOf (n + 1) y) : ℝ) / n - 1|} =
        ENNReal.ofReal (cubeProb (n + 1)
          (fun x => (1 : ℝ) / (m + 1) < |(2 * rootCountPM x : ℝ) / n - 1|)) := fun n =>
      trpm_aux_nuLaw_bitsOf_mem (n + 1)
        (fun x => (1 : ℝ) / (m + 1) < |(2 * rootCountPM x : ℝ) / n - 1|)
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => cubeProb_nonneg _ _) (hsum m)]
    exact ENNReal.ofReal_ne_top
  have hgood : ∀ᵐ x ∂trpm_aux_nuLaw,
      Tendsto (fun n : ℕ => (2 * rawCount x n : ℝ) / n) atTop (𝓝 1) := by
    have hall : ∀ᵐ x ∂trpm_aux_nuLaw, ∀ m : ℕ, ∀ᶠ n in atTop,
        x ∉ {y : ℕ → ℂ | (1 : ℝ) / (m + 1) <
          |(2 * rootCountPM (bitsOf (n + 1) y) : ℝ) / n - 1|} := ae_all_iff.mpr hBC
    filter_upwards [hpm, hall] with x hx hm
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm'⟩ := exists_nat_one_div_lt hε
    obtain ⟨N, hN⟩ := (hm m).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    simp only [not_lt] at h1
    rw [Real.dist_eq, trpm_aux_rawCount_eq x hx n]
    exact lt_of_le_of_lt h1 hm'
  have hae : ∀ᵐ ω ∂(ℙ : Measure Ω),
      Tendsto (fun n : ℕ => (2 * rawCount (fun i => c i ω) n : ℝ) / n) atTop (𝓝 1) := by
    rw [← hmap] at hgood
    exact ae_of_ae_map hXm hgood
  -- an a.e. true (possibly non-measurable) event has probability one
  set S := {ω | Tendsto (fun n : ℕ => (2 * rawCount (fun i => c i ω) n : ℝ) / n) atTop (𝓝 1)}
  have hc : (ℙ : Measure Ω) Sᶜ = 0 := by
    rw [ae_iff] at hae
    exact hae
  apply le_antisymm prob_le_one
  have := measure_union_le (μ := (ℙ : Measure Ω)) S Sᶜ
  rw [Set.union_compl_self, measure_univ, hc, add_zero] at this
  exact this

end E522

end

/- ## Section: `BridgePM` -/

section

/-
# Bridge for the `±1` polynomial

Same as `Bridge.lean` with `Z = W` (no mean term, no factor 2):
`Λ(s) = cav(log|W_s|)`, `W_0 = f/√N`.
-/

open Real Complex MeasureTheory Filter Topology

namespace E522

noncomputable section

lemma log_norm_WPM_ii {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (s : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖Wfun (rho N s) x θ‖) volume 0 (2 * π) := by
  have hmero : MeromorphicOn (fun z => (polyPM x).eval z) (Metric.sphere (0 : ℂ) |Real.exp s|) :=
    AnalyticOnNhd.meromorphicOn (fun z _ => (Polynomial.differentiable (polyPM x)).analyticAt z)
  have h1 : CircleIntegrable (fun z => Real.log ‖(polyPM x).eval z‖) 0 (Real.exp s) :=
    hmero.circleIntegrable_log_norm
  have h2 : IntervalIntegrable (fun θ => Real.log (1 / Real.sqrt (sig2 N s)) +
      Real.log ‖(polyPM x).eval (circleMap 0 (Real.exp s) θ)‖) volume 0 (2 * π) :=
    intervalIntegrable_const.add h1
  refine h2.congr_ae ?_
  filter_upwards [WPM_ne_zero_ae hN x s] with θ hθ
  rw [Wfun_eq_evalPM] at hθ ⊢
  have hσ : 0 < 1 / Real.sqrt (sig2 N s) := by
    have := sig2_pos hN s
    positivity
  have hev : (polyPM x).eval (circleMap 0 (Real.exp s) θ) ≠ 0 := by
    intro h; apply hθ; rw [h, mul_zero]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hσ.le,
    Real.log_mul hσ.ne' (norm_ne_zero_iff.mpr hev)]

lemma phiD_WPM_ii {N : ℕ} (x : Fin N → Bool) (s : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    IntervalIntegrable (fun θ => phiD δ (Wfun (rho N s) x θ)) volume 0 (2 * π) :=
  ((phiD_continuous hδ).comp (Wfun_continuous _ x)).intervalIntegrable _ _

lemma psiB_WPM_ii {N : ℕ} (x : Fin N → Bool) (s : ℝ) {β : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (fun θ => psiB β (Wfun (rho N s) x θ)) volume 0 (2 * π) :=
  ((psiB_continuous hβ).comp (Wfun_continuous _ x)).intervalIntegrable _ _

lemma lam_le_cav_phiDPM {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool) (s : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    LamPM x s ≤ cav (fun θ => phiD δ (Wfun (rho N s) x θ)) := by
  rw [lam_eq_cavPM hN x s]
  apply cav_mono_ae (log_norm_WPM_ii hN x s) (phiD_WPM_ii x s hδ)
  filter_upwards [WPM_ne_zero_ae hN x s] with θ hθ
  exact log_norm_le_phiD hδ hθ

lemma smallIndPM_nonneg {N : ℕ} (x : Fin N → Bool) (ε' θ : ℝ) : 0 ≤ smallIndPM x ε' θ := by
  unfold smallIndPM; split_ifs <;> norm_num

lemma smallIndPM_le_one {N : ℕ} (x : Fin N → Bool) (ε' θ : ℝ) : smallIndPM x ε' θ ≤ 1 := by
  unfold smallIndPM; split_ifs <;> norm_num

lemma evalCirclePM_continuous {N : ℕ} (x : Fin N → Bool) :
    Continuous (fun θ : ℝ => (polyPM x).eval (Complex.exp ((θ : ℂ) * I))) :=
  (Polynomial.continuous _).comp (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const))

lemma smallIndPM_measurable {N : ℕ} (x : Fin N → Bool) (ε' : ℝ) :
    Measurable (smallIndPM x ε') := by
  unfold smallIndPM
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt ((evalCirclePM_continuous x).norm.measurable) measurable_const

lemma smallIndPM_ii {N : ℕ} (x : Fin N → Bool) (ε' : ℝ) :
    IntervalIntegrable (smallIndPM x ε') volume 0 (2 * π) := by
  refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun
    (smallIndPM_measurable x ε').aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun θ => ?_)
  simp only [Real.norm_eq_abs, abs_one]
  rw [abs_of_nonneg (smallIndPM_nonneg x ε' θ)]
  exact smallIndPM_le_one x ε' θ

lemma log_norm_evalCirclePM_ii {N : ℕ} (x : Fin N → Bool) :
    IntervalIntegrable (fun θ : ℝ => Real.log ‖(polyPM x).eval (Complex.exp ((θ : ℂ) * I))‖)
      volume 0 (2 * π) := by
  have hmero : MeromorphicOn (fun z => (polyPM x).eval z) (Metric.sphere (0 : ℂ) |(1 : ℝ)|) :=
    AnalyticOnNhd.meromorphicOn (fun z _ => (Polynomial.differentiable (polyPM x)).analyticAt z)
  have h1 : CircleIntegrable (fun z => Real.log ‖(polyPM x).eval z‖) 0 1 :=
    hmero.circleIntegrable_log_norm
  unfold CircleIntegrable at h1
  convert h1 using 3 with θ
  rw [circleMap_zero_eq]; simp

lemma lam_zero_gePM {N : ℕ} (hN : 1 ≤ N) (x : Fin N → Bool)
    {ε' δ β : ℝ} (hε' : 0 < ε') (hηδ : 2 * ε' / Real.sqrt N ≤ δ) (hδ1 : δ ≤ 1) (hβ : 0 < β) :
    cav (fun θ => phiD δ (Wfun (rho N 0) x θ)) - δ ^ 2 / (2 * β ^ 2)
      - 2 * Real.log (2 * δ / (2 * ε' / Real.sqrt N)) * cav (fun θ => psiB β (Wfun (rho N 0) x θ))
      - ((1 + Real.log N) * cav (smallIndPM x ε')
          + Real.sqrt (cav (smallIndPM x ε')) * Real.sqrt (400 * N ^ 2))
      ≤ LamPM x 0 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  set η := 2 * ε' / Real.sqrt N with hη
  have hηpos : 0 < η := by positivity
  have hδ : 0 < δ := lt_of_lt_of_le hηpos hηδ
  set Λ := Real.log (2 * δ / η) with hΛ
  set Z := fun θ => Wfun (rho N 0) x θ with hZ
  set Tint : ℝ → ℝ := fun θ => if ‖Z θ‖ < η then 1 + Real.log (1 / ‖Z θ‖) else 0 with hTint
  set f := fun θ : ℝ => (polyPM x).eval (Complex.exp ((θ : ℂ) * I)) with hf
  have hZf : ∀ θ, Z θ = ((1 / Real.sqrt N : ℝ) : ℂ) * f θ := fun θ => Wfun_zero_evalPM x θ
  have hlogN : 0 ≤ Real.log (Real.sqrt N) := by
    apply Real.log_nonneg
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hN)
  set Tb : ℝ → ℝ := fun θ => smallIndPM x ε' θ * (1 + Real.log (Real.sqrt N) + |Real.log ‖f θ‖|)
    with hTb
  have hTb_nonneg : ∀ θ, 0 ≤ Tb θ := fun θ =>
    mul_nonneg (smallIndPM_nonneg x ε' θ) (by positivity)
  have hnormZ : ∀ θ, ‖Z θ‖ = 1 / Real.sqrt N * ‖f θ‖ := by
    intro θ
    rw [hZf θ, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hTint_nonneg : ∀ θ, 0 ≤ Tint θ := by
    intro θ
    simp only [hTint]
    split_ifs with h
    · by_cases hz : ‖Z θ‖ = 0
      · rw [hz]; simp
      · have hz' : 0 < ‖Z θ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
        have : 0 ≤ Real.log (1 / ‖Z θ‖) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ hz', one_mul]
          exact le_trans h.le (le_trans hηδ hδ1)
        linarith
    · exact le_refl 0
  have hTint_le : ∀ θ, Tint θ ≤ Tb θ := by
    intro θ
    simp only [hTint, hTb]
    split_ifs with h
    · have hsmall : ‖f θ‖ < 2 * ε' := by
        rw [hnormZ θ] at h
        rw [hη] at h
        have h2 : 0 < 1 / Real.sqrt N := by positivity
        calc ‖f θ‖ = (1 / Real.sqrt N * ‖f θ‖) / (1 / Real.sqrt N) := by field_simp
          _ < (2 * ε' / Real.sqrt N) / (1 / Real.sqrt N) := by
            exact div_lt_div_of_pos_right h h2
          _ = 2 * ε' := by field_simp
      have hind : smallIndPM x ε' θ = 1 := by
        unfold smallIndPM; rw [if_pos hsmall]
      rw [hind, one_mul]
      by_cases hf0 : f θ = 0
      · have : ‖Z θ‖ = 0 := by rw [hnormZ θ, hf0, norm_zero, mul_zero]
        rw [this, hf0]; simp; linarith
      · have hfpos : 0 < ‖f θ‖ := norm_pos_iff.mpr hf0
        rw [hnormZ θ, one_div, Real.log_inv, Real.log_mul (by positivity) hfpos.ne']
        have : -(Real.log (1 / Real.sqrt N)) = Real.log (Real.sqrt N) := by
          rw [one_div, Real.log_inv, neg_neg]
        have habs : -Real.log ‖f θ‖ ≤ |Real.log ‖f θ‖| := neg_le_abs _
        linarith
    · exact hTb_nonneg θ
  have hlogf := log_norm_evalCirclePM_ii x
  have hTb_ii : IntervalIntegrable Tb volume 0 (2 * π) := by
    have hdom : IntervalIntegrable (fun θ => (1 + Real.log (Real.sqrt N)) + |Real.log ‖f θ‖|)
        volume 0 (2 * π) := intervalIntegrable_const.add hlogf.abs
    refine hdom.mono_fun ?_ ?_
    · exact ((smallIndPM_measurable x ε').mul (measurable_const.add
        ((evalCirclePM_continuous x).norm.measurable.log.abs))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun θ => ?_)
      simp only [hTb, Real.norm_eq_abs]
      rw [abs_of_nonneg (hTb_nonneg θ), abs_of_nonneg (by positivity)]
      calc smallIndPM x ε' θ * (1 + Real.log (Real.sqrt N) + |Real.log ‖f θ‖|)
          ≤ 1 * (1 + Real.log (Real.sqrt N) + |Real.log ‖f θ‖|) := by
            apply mul_le_mul_of_nonneg_right (smallIndPM_le_one x ε' θ) (by positivity)
        _ = _ := by ring
  have hTint_meas : Measurable Tint := by
    simp only [hTint]
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt ((Wfun_continuous _ x).norm.measurable) measurable_const
    · exact measurable_const.add (measurable_const.div
        (Wfun_continuous _ x).norm.measurable).log
  have hTint_ii : IntervalIntegrable Tint volume 0 (2 * π) := by
    refine hTb_ii.mono_fun hTint_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun θ => ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (hTint_nonneg θ), abs_of_nonneg (hTb_nonneg θ)]
    exact hTint_le θ
  rw [lam_eq_cavPM hN x 0]
  have hphi := phiD_WPM_ii x 0 hδ (N := N)
  have hpsi := psiB_WPM_ii x 0 hβ (N := N)
  have hlogZ := log_norm_WPM_ii hN x 0
  have hRHS_ii : IntervalIntegrable (fun θ => phiD δ (Z θ) - δ ^ 2 / (2 * β ^ 2)
      - 2 * Λ * psiB β (Z θ) - Tint θ) volume 0 (2 * π) :=
    ((hphi.sub intervalIntegrable_const).sub (hpsi.const_mul _)).sub hTint_ii
  have hpt : cav (fun θ => phiD δ (Z θ) - δ ^ 2 / (2 * β ^ 2) - 2 * Λ * psiB β (Z θ) - Tint θ)
      ≤ cav (fun θ => Real.log ‖Z θ‖) := by
    apply cav_mono_ae hRHS_ii hlogZ
    filter_upwards [WPM_ne_zero_ae hN x 0] with θ hθ
    have := phiD_sub_log_le hηpos hηδ hδ1 hβ hθ
    simp only [hTint]
    linarith
  have hcav_split : cav (fun θ => phiD δ (Z θ) - δ ^ 2 / (2 * β ^ 2) - 2 * Λ * psiB β (Z θ)
      - Tint θ) = cav (fun θ => phiD δ (Z θ)) - δ ^ 2 / (2 * β ^ 2)
        - 2 * Λ * cav (fun θ => psiB β (Z θ)) - cav Tint := by
    rw [cav_sub ((hphi.sub intervalIntegrable_const).sub (hpsi.const_mul _)) hTint_ii,
      cav_sub (hphi.sub intervalIntegrable_const) (hpsi.const_mul _),
      cav_sub hphi intervalIntegrable_const, cav_const, cav_const_mul]
  have hTbound : cav Tint ≤ (1 + Real.log N) * cav (smallIndPM x ε')
      + Real.sqrt (cav (smallIndPM x ε')) * Real.sqrt (400 * N ^ 2) := by
    have h1 : cav Tint ≤ cav Tb := cav_mono hTint_ii hTb_ii hTint_le
    have hA : IntervalIntegrable (fun θ => |smallIndPM x ε' θ * Real.log ‖f θ‖|) volume 0 (2 * π) := by
      refine hlogf.abs.mono_fun ?_ ?_
      · exact ((smallIndPM_measurable x ε').mul
          ((evalCirclePM_continuous x).norm.measurable.log)).abs.aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun θ => ?_)
        simp only [Real.norm_eq_abs, abs_abs]
        rw [abs_mul, abs_of_nonneg (smallIndPM_nonneg x ε' θ)]
        calc smallIndPM x ε' θ * |Real.log ‖f θ‖| ≤ 1 * |Real.log ‖f θ‖| :=
              mul_le_mul_of_nonneg_right (smallIndPM_le_one x ε' θ) (abs_nonneg _)
          _ = |Real.log ‖f θ‖| := one_mul _
    have h2 : cav Tb = (1 + Real.log (Real.sqrt N)) * cav (smallIndPM x ε')
        + cav (fun θ => |smallIndPM x ε' θ * Real.log ‖f θ‖|) := by
      have hsplit : Tb = fun θ => (1 + Real.log (Real.sqrt N)) * smallIndPM x ε' θ
          + |smallIndPM x ε' θ * Real.log ‖f θ‖| := by
        funext θ
        simp only [hTb]
        rw [abs_mul, abs_of_nonneg (smallIndPM_nonneg x ε' θ)]
        ring
      rw [hsplit, cav_add ((smallIndPM_ii x ε').const_mul _) hA, cav_const_mul]
    have hsq : (fun θ => smallIndPM x ε' θ ^ 2) = smallIndPM x ε' := by
      funext θ; unfold smallIndPM; split_ifs <;> norm_num
    have h3 : cav (fun θ => |smallIndPM x ε' θ * Real.log ‖f θ‖|)
        ≤ Real.sqrt (cav (smallIndPM x ε')) * Real.sqrt (400 * N ^ 2) := by
      have hCS := cav_mul_le_sqrt (F := smallIndPM x ε') (G := fun θ => Real.log ‖f θ‖)
        (by rw [hsq]; exact smallIndPM_ii x ε')
        (log_sq_intervalIntegrablePM hN x)
      rw [hsq] at hCS
      refine le_trans hCS ?_
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact Real.sqrt_le_sqrt (log_sq_boundPM hN x)
    have h4 : Real.log (Real.sqrt N) ≤ Real.log N := by
      apply Real.log_le_log hsqN
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [show (1:ℝ) ≤ N by exact_mod_cast hN]
    have hμ : 0 ≤ cav (smallIndPM x ε') := cav_nonneg (smallIndPM_nonneg x ε')
    nlinarith [h1, h2, h3, h4, hμ, mul_le_mul_of_nonneg_right (add_le_add_left h4 1) hμ]
  rw [hcav_split] at hpt
  have hΛnn : 0 ≤ Λ := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hηpos, one_mul]
    linarith
  linarith

lemma EF_boundPM {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {δ εb : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hεb : 0 < εb) :
    |cubeAvg (n + 1) (fun x => cav (fun θ => phiD δ (Wfun (rho (n + 1) s) x θ))) - kappa δ|
      ≤ eBound n δ εb := by
  set N := n + 1 with hNdef
  have hN : 1 ≤ N := by omega
  set ρ := rho N s with hρ
  have hswap := cubeAvg_cav (N := N) (fun x θ => phiD δ (Wfun ρ x θ))
    (fun x => phiD_WPM_ii x s hδ)
  rw [hswap]
  set g : ℝ → ℝ := fun θ => cubeAvg N (fun x => phiD δ (Wfun ρ x θ)) with hg
  have hg_cont : Continuous g := by
    simp only [hg, cubeAvg]
    refine Continuous.div_const ?_ _
    refine continuous_finsetSum _ (fun x _ => ?_)
    exact (phiD_continuous hδ).comp (Wfun_continuous _ x)
  have hsub : cav g - kappa δ = cav (fun θ => g θ - kappa δ) := by
    rw [cav_sub (hg_cont.intervalIntegrable _ _) intervalIntegrable_const, cav_const]
  rw [hsub]
  refine le_trans (abs_cav_le _) ?_
  set bad : ℝ → ℝ := fun θ => if |Real.sin θ| < εb then 1 else 0 with hbad
  set cap : ℝ := 2 * (|Real.log δ| + 1) with hcap
  set lind : ℝ := 10 * (2 / Real.sqrt (n + 1)) / δ ^ 3
      + 20 / ((n + 1) * εb) * (1 / δ ^ 2 + 10 * (n + 1) * (2 / Real.sqrt (n + 1)) / δ ^ 3)
    with hlind
  have hlind_nn : 0 ≤ lind := by positivity
  have hcap_nn : 0 ≤ cap := by positivity
  have hpt : ∀ θ, |g θ - kappa δ| ≤ bad θ * cap + lind := by
    intro θ
    by_cases hθ : |Real.sin θ| < εb
    · have hb : bad θ = 1 := by simp only [hbad]; rw [if_pos hθ]
      rw [hb, one_mul]
      have := cubeAvg_phiD_W_abs_le hN s θ hδ hδ1
      linarith
    · have hb : bad θ = 0 := by simp only [hbad]; rw [if_neg hθ]
      rw [hb, zero_mul, zero_add]
      push Not at hθ
      have hsin : Real.sin θ ≠ 0 := by
        intro h; rw [h, abs_zero] at hθ; linarith
      have hL := lindeberg ρ (fun k => rho_nonneg N s k) (sum_rho_sq hN s)
        (2 / Real.sqrt (n + 1)) (fun k hk => by
          have := rho_le (n := n) hn hs (k := k) (by omega)
          simpa [hρ, hNdef] using this)
        θ δ hδ hδ1 (20 / ((n + 1) * εb)) (fun J hJ => by
          have := P_bound hn hs θ hsin (J := J) (by omega)
          refine le_trans this ?_
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          exact mul_le_mul_of_nonneg_left hθ (by positivity))
      have hcast : ((N : ℕ) : ℝ) = (n : ℝ) + 1 := by simp [hNdef]
      rw [hcast] at hL
      simpa [hlind, hg] using hL
  have hbad_meas : Measurable bad := by
    simp only [hbad]
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt (Real.continuous_sin.abs.measurable) measurable_const
  have hbad_nn : ∀ θ, 0 ≤ bad θ := fun θ => by simp only [hbad]; split_ifs <;> norm_num
  have hbad_le : ∀ θ, bad θ ≤ 1 := fun θ => by simp only [hbad]; split_ifs <;> norm_num
  have hbad_ii : IntervalIntegrable bad volume 0 (2 * π) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun hbad_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun θ => ?_)
    simp only [Real.norm_eq_abs, abs_one]
    rw [abs_of_nonneg (hbad_nn θ)]; exact hbad_le θ
  have hA_ii : IntervalIntegrable (fun θ => |g θ - kappa δ|) volume 0 (2 * π) :=
    ((hg_cont.sub continuous_const).abs).intervalIntegrable _ _
  have hB_ii : IntervalIntegrable (fun θ => bad θ * cap + lind) volume 0 (2 * π) :=
    (hbad_ii.mul_const _).add intervalIntegrable_const
  refine le_trans (cav_mono hA_ii hB_ii hpt) ?_
  rw [cav_add (hbad_ii.mul_const _) intervalIntegrable_const, cav_const]
  have hcav_bad : cav (fun θ => bad θ * cap) = cap * cav bad := by
    have : (fun θ => bad θ * cap) = fun θ => cap * bad θ := by funext θ; ring
    rw [this, cav_const_mul]
  rw [hcav_bad]
  have hbadcav : cav bad ≤ 2 * εb := cav_bad_theta hεb
  unfold eBound
  have e2 : cap * cav bad ≤ 2 * εb * cap := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hbadcav hcap_nn
  simp only [hcap] at e2
  have e1 : 0 ≤ (Real.sqrt (2 * εb) + 20 / (Real.sqrt (n + 1) * εb)) / (2 * δ) := by positivity
  linarith

lemma EK_boundPM {N : ℕ} (hN : 1 ≤ N) {β β₂ : ℝ} (hβ : 0 < β) (hβ₂ : 0 < β₂) :
    cubeAvg N (fun x => cav (fun θ => psiB β (Wfun (rho N 0) x θ))) ≤
      2 * β₂ + 2 / Real.sqrt N + β ^ 2 / β₂ ^ 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  rw [cubeAvg_cav (N := N) (fun x θ => psiB β (Wfun (rho N 0) x θ))
    (fun x => psiB_WPM_ii x 0 hβ)]
  apply cav_le_of_le_const
  · refine Continuous.intervalIntegrable ?_ _ _
    simp only [cubeAvg]
    refine Continuous.div_const ?_ _
    exact continuous_finsetSum _ (fun x _ => (psiB_continuous hβ).comp (Wfun_continuous _ x))
  · intro θ
    classical
    have hpt : ∀ x : Fin N → Bool, psiB β (Wfun (rho N 0) x θ) ≤
        (if ‖Wfun (rho N 0) x θ‖ < β₂ then 1 else 0) + β ^ 2 / β₂ ^ 2 :=
      fun x => psiB_le_indicator hβ hβ₂ _
    refine le_trans (cubeAvg_mono hpt) ?_
    rw [cubeAvg_add, cubeAvg_const, ← cubeProb_eq_cubeAvg]
    gcongr
    have hZ : ∀ x : Fin N → Bool, Wfun (rho N 0) x θ =
        ((1 / Real.sqrt N : ℝ) : ℂ) * (∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + 0) := by
      intro x
      unfold Wfun
      simp only [rho_zero, add_zero]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      push_cast; ring
    have hev : ∀ x : Fin N → Bool, ‖Wfun (rho N 0) x θ‖ < β₂ →
        ‖∑ k : Fin N, ((sgn (x k) : ℝ) : ℂ) * ex k θ + 0‖ < β₂ * Real.sqrt N := by
      intro x hx
      rw [hZ x, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at hx
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ hsqN] at hx
      linarith
    refine le_trans (cubeProb_mono hev) ?_
    refine le_trans (lo_bound hN θ 0 (β₂ * Real.sqrt N) (by positivity)) (le_of_eq ?_)
    field_simp

lemma F_concPM {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : |s| ≤ 1 / (2 * n)) {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 ≤ t) :
    cubeProb (n + 1) (fun x => t ≤ |cav (fun θ => phiD δ (Wfun (rho (n + 1) s) x θ))
        - cubeAvg (n + 1) (fun y => cav (fun θ => phiD δ (Wfun (rho (n + 1) s) y θ)))|)
      ≤ 2 * Real.exp (-t ^ 2 / (2 * vF n δ)) := by
  apply cube_tail _ _ _ (vF_pos n hδ) ht
  intro x
  have hL : 0 < Nat.sqrt (n + 1) := Nat.sqrt_pos.mpr (by omega)
  have h := sum_mgDiff_sq_le (N := n + 1) hL (rho (n + 1) s) (2 / Real.sqrt (n + 1))
    (fun k => rho_nonneg _ s k) (fun k hk => by
      have := rho_le (n := n) hn hs (k := k) hk
      simpa using this)
    (fun _ => (0 : ℂ)) continuous_const (phiD δ) (gphiD δ) (1 / (2 * δ))
    (3 / δ ^ 2) (phiD_continuous hδ) (gphiD_continuous hδ) (fun z w => phiD_taylor2 hδ z w)
    (fun z => gphiD_norm_le hδ z) (fun z w => gphiD_lip hδ z w) x
  simpa [vF] using h

lemma K_concPM {n : ℕ} (hn : 1 ≤ n) {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    cubeProb (n + 1) (fun x => t ≤ |cav (fun θ => psiB β (Wfun (rho (n + 1) 0) x θ))
        - cubeAvg (n + 1) (fun y => cav (fun θ => psiB β (Wfun (rho (n + 1) 0) y θ)))|)
      ≤ 2 * Real.exp (-t ^ 2 / (2 * vK n β)) := by
  apply cube_tail _ _ _ (vK_pos n hβ) ht
  intro x
  have hL : 0 < Nat.sqrt (n + 1) := Nat.sqrt_pos.mpr (by omega)
  have hs : |(0 : ℝ)| ≤ 1 / (2 * n) := by rw [abs_zero]; positivity
  have h := sum_mgDiff_sq_le (N := n + 1) hL (rho (n + 1) 0) (2 / Real.sqrt (n + 1))
    (fun k => rho_nonneg _ 0 k) (fun k hk => by
      have := rho_le (n := n) hn hs (k := k) hk
      simpa using this)
    (fun _ => (0 : ℂ)) continuous_const (psiB β) (gpsiB β) (1 / β)
    (10 / β ^ 2) (psiB_continuous hβ) (gpsiB_continuous hβ) (fun z w => psiB_taylor2 hβ z w)
    (fun z => gpsiB_norm_le hβ z) (fun z w => gpsiB_lip hβ z w) x
  simpa [vK] using h

end

end E522

end

/- ## Section: `MainPM` -/

section

/-
# Assembly for the `±1` polynomial (same parameters, `Err`, `Bnd` as the `0/1` case)
-/

open Real Complex MeasureTheory Filter Topology

namespace E522

noncomputable section

def FsPM (n : ℕ) (s : ℝ) (x : Fin (n + 1) → Bool) : ℝ :=
  cav (fun θ => phiD (pδ n) (Wfun (rho (n + 1) s) x θ))

def KsPM (n : ℕ) (x : Fin (n + 1) → Bool) : ℝ :=
  cav (fun θ => psiB (pβ n) (Wfun (rho (n + 1) 0) x θ))

def GoodPM (n : ℕ) (c : ℝ) (x : Fin (n + 1) → Bool) : Prop :=
  |FsPM n (c / n) x - cubeAvg (n + 1) (FsPM n (c / n))| < pt n ∧
  |FsPM n (-(c / n)) x - cubeAvg (n + 1) (FsPM n (-(c / n)))| < pt n ∧
  |FsPM n 0 x - cubeAvg (n + 1) (FsPM n 0)| < pt n ∧
  |KsPM n x - cubeAvg (n + 1) (KsPM n)| < pt n ∧
  cav (smallIndPM x (pε' n)) ≤ NN n ^ (-(4 : ℝ))

lemma good_boundPM {n : ℕ} (hn : 3 ≤ n) {c : ℝ} (hc : 0 < c) (hc2 : c ≤ 1 / 2)
    (x : Fin (n + 1) → Bool) (hG : GoodPM n c x) :
    |(2 * rootCountPM x : ℝ) / n - 1| ≤ c / 2 + 4 * Err n / c := by
  obtain ⟨hFp, hFm, hF0, hK, hμ⟩ := hG
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN1 : 1 ≤ n + 1 := by omega
  have hδ := pδ_pos n
  have hδ1 := pδ_le_one n
  have hβ := pβ_pos n
  have hβ₂ := pβ₂_pos n
  have ht := pt_pos n
  have hh : 0 < c / n := div_pos hc hnpos
  have hsh : |c / n| ≤ 1 / (2 * n) := by
    rw [abs_of_pos hh, div_le_div_iff₀ hnpos (by positivity)]
    nlinarith
  have hsmh : |-(c / n)| ≤ 1 / (2 * n) := by rwa [abs_neg]
  have hs0 : |(0 : ℝ)| ≤ 1 / (2 * n) := by rw [abs_zero]; positivity
  have hΛ := Err_nonneg_parts n
  have hC : 0 ≤ 2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n := by
    have := Real.sqrt_nonneg (NN n); positivity
  have hD : 0 ≤ (1 + Real.log (NN n)) * NN n ^ (-(4 : ℝ))
      + Real.sqrt (NN n ^ (-(4 : ℝ))) * Real.sqrt (400 * NN n ^ 2) := by
    have := Real.log_nonneg (one_le_NN n)
    have := Real.rpow_nonneg (NN_pos n).le (-(4 : ℝ))
    positivity
  have hA : 0 ≤ pδ n ^ 2 / (2 * pβ n ^ 2) := by positivity
  have hΛC : 0 ≤ 2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
      * (2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n) := by positivity
  have hE : ∀ s : ℝ, |s| ≤ 1 / (2 * n) →
      |cubeAvg (n + 1) (FsPM n s) - kappa (pδ n)| ≤ eBound n (pδ n) (pt n) := fun s hs =>
    EF_boundPM hn1 hs hδ hδ1 ht
  have hup : ∀ s : ℝ, |s| ≤ 1 / (2 * n) →
      |FsPM n s x - cubeAvg (n + 1) (FsPM n s)| < pt n →
        LamPM x s ≤ kappa (pδ n) + Err n := by
    intro s hs hdev
    have h1 : LamPM x s ≤ FsPM n s x := lam_le_cav_phiDPM hN1 x s hδ
    have h3 := (abs_lt.mp hdev).2
    have h4 := (abs_le.mp (hE s hs)).2
    unfold Err
    linarith
  have hUp := hup (c / n) hsh hFp
  have hDn := hup (-(c / n)) hsmh hFm
  have hLo : kappa (pδ n) - Err n ≤ LamPM x 0 := by
    have hlow := lam_zero_gePM (N := n + 1) hN1 x (pε'_pos n)
      (by simpa [NN] using eta_le_delta n) hδ1 hβ
    have hK_le : KsPM n x ≤ 2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n := by
      have hEK := EK_boundPM (N := n + 1) hN1 hβ hβ₂
      have := (abs_lt.mp hK).2
      have hKs : cubeAvg (n + 1) (KsPM n) = cubeAvg (n + 1)
          (fun x => cav (fun θ => psiB (pβ n) (Wfun (rho (n + 1) 0) x θ))) := rfl
      rw [hKs] at this
      simp only [NN] at hEK ⊢
      linarith
    have hT : (1 + Real.log (((n + 1 : ℕ) : ℝ))) * cav (smallIndPM x (pε' n))
        + Real.sqrt (cav (smallIndPM x (pε' n))) * Real.sqrt (400 * ((n + 1 : ℕ) : ℝ) ^ 2)
        ≤ (1 + Real.log (NN n)) * NN n ^ (-(4 : ℝ))
          + Real.sqrt (NN n ^ (-(4 : ℝ))) * Real.sqrt (400 * NN n ^ 2) := by
      have hlog : 0 ≤ 1 + Real.log (NN n) := by
        have := Real.log_nonneg (one_le_NN n); linarith
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hμ hlog
      · exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hμ) (Real.sqrt_nonneg _)
    have hΛK : 2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n))) * KsPM n x ≤
        2 * Real.log (2 * pδ n / (2 * pε' n / Real.sqrt (NN n)))
          * (2 * pβ₂ n + 2 / Real.sqrt (NN n) + pβ n ^ 2 / pβ₂ n ^ 2 + pt n) :=
      mul_le_mul_of_nonneg_left hK_le (by positivity)
    have h3 := (abs_lt.mp hF0).1
    have h4 := (abs_le.mp (hE 0 hs0)).1
    have hF0v : FsPM n 0 x = cav (fun θ => phiD (pδ n) (Wfun (rho (n + 1) 0) x θ)) := rfl
    have hKv : KsPM n x = cav (fun θ => psiB (pβ n) (Wfun (rho (n + 1) 0) x θ)) := rfl
    rw [← hF0v, ← hKv] at hlow
    unfold Err
    simp only [NN] at hT hΛK hlow ⊢
    linarith
  have hdet := det_mainPM x (c / n) (kappa (pδ n)) (Err n) hh hUp hDn hLo
  have hR : |(2 * rootCountPM x : ℝ) / n - 1| = 2 / n * |(rootCountPM x : ℝ) - n / 2| := by
    rw [show (2 * rootCountPM x : ℝ) / n - 1 = 2 / n * ((rootCountPM x : ℝ) - n / 2) by
      field_simp]
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / n)]
  rw [hR]
  calc 2 / n * |(rootCountPM x : ℝ) - n / 2|
      ≤ 2 / n * ((n : ℝ) ^ 2 * (c / n) / 4 + 2 * Err n / (c / n)) :=
        mul_le_mul_of_nonneg_left hdet (by positivity)
    _ = c / 2 + 4 * Err n / c := by
        field_simp; ring

lemma prob_badPM {n : ℕ} (hn : 1 ≤ n) (hK : pK n ≤ n + 1) {c : ℝ} (hc : 0 < c)
    (hc2 : c ≤ 1 / 2) :
    cubeProb (n + 1) (fun x => ¬ GoodPM n c x) ≤ Bnd n := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hh : 0 < c / n := div_pos hc hnpos
  have hsh : |c / n| ≤ 1 / (2 * n) := by
    rw [abs_of_pos hh, div_le_div_iff₀ hnpos (by positivity)]
    nlinarith
  have hsmh : |-(c / n)| ≤ 1 / (2 * n) := by rwa [abs_neg]
  have hs0 : |(0 : ℝ)| ≤ 1 / (2 * n) := by rw [abs_zero]; positivity
  have hsub : ∀ x : Fin (n + 1) → Bool, ¬ GoodPM n c x →
      (pt n ≤ |FsPM n (c / n) x - cubeAvg (n + 1) (FsPM n (c / n))| ∨
        pt n ≤ |FsPM n (-(c / n)) x - cubeAvg (n + 1) (FsPM n (-(c / n)))|) ∨
      (pt n ≤ |FsPM n 0 x - cubeAvg (n + 1) (FsPM n 0)| ∨
        (pt n ≤ |KsPM n x - cubeAvg (n + 1) (KsPM n)| ∨
          NN n ^ (-(4 : ℝ)) < cav (smallIndPM x (pε' n)))) := by
    intro x hx
    unfold GoodPM at hx
    simp only [not_and_or, not_lt, not_le] at hx
    rcases hx with h | h | h | h | h
    · left; left; exact h
    · left; right; exact h
    · right; left; exact h
    · right; right; left; exact h
    · right; right; right; exact h
  refine le_trans (cubeProb_mono hsub) ?_
  refine le_trans (cubeProb_or_le _ _) ?_
  have e1 := cubeProb_or_le (N := n + 1)
    (fun x => pt n ≤ |FsPM n (c / n) x - cubeAvg (n + 1) (FsPM n (c / n))|)
    (fun x => pt n ≤ |FsPM n (-(c / n)) x - cubeAvg (n + 1) (FsPM n (-(c / n)))|)
  have e2 := cubeProb_or_le (N := n + 1)
    (fun x => pt n ≤ |FsPM n 0 x - cubeAvg (n + 1) (FsPM n 0)|)
    (fun x => (pt n ≤ |KsPM n x - cubeAvg (n + 1) (KsPM n)| ∨
        NN n ^ (-(4 : ℝ)) < cav (smallIndPM x (pε' n))))
  have e3 := cubeProb_or_le (N := n + 1)
    (fun x => pt n ≤ |KsPM n x - cubeAvg (n + 1) (KsPM n)|)
    (fun x => NN n ^ (-(4 : ℝ)) < cav (smallIndPM x (pε' n)))
  have p1 : cubeProb (n + 1) (fun x => pt n ≤ |FsPM n (c / n) x - cubeAvg (n + 1) (FsPM n (c / n))|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))) :=
    F_concPM hn hsh (pδ_pos n) (pt_pos n).le
  have p2 : cubeProb (n + 1)
      (fun x => pt n ≤ |FsPM n (-(c / n)) x - cubeAvg (n + 1) (FsPM n (-(c / n)))|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))) :=
    F_concPM hn hsmh (pδ_pos n) (pt_pos n).le
  have p3 : cubeProb (n + 1) (fun x => pt n ≤ |FsPM n 0 x - cubeAvg (n + 1) (FsPM n 0)|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vF n (pδ n))) :=
    F_concPM hn hs0 (pδ_pos n) (pt_pos n).le
  have p4 : cubeProb (n + 1) (fun x => pt n ≤ |KsPM n x - cubeAvg (n + 1) (KsPM n)|)
      ≤ 2 * Real.exp (-(pt n) ^ 2 / (2 * vK n (pβ n))) :=
    K_concPM hn (pβ_pos n) (pt_pos n).le
  have p5 : cubeProb (n + 1) (fun x => NN n ^ (-(4 : ℝ)) < cav (smallIndPM x (pε' n))) ≤
      NN n ^ (4 : ℝ) * ((1 / 2) ^ pK n + 3 ^ pK n * pK n * (2 * pε' n) ^ ((1 : ℝ) / pK n)) := by
    have hK1 : 1 ≤ pK n := by unfold pK; omega
    have hm := cube_markov (N := n + 1) (fun x => cav (smallIndPM x (pε' n)))
      (fun x => cav_nonneg (smallIndPM_nonneg x _)) (NN n ^ (-(4 : ℝ)))
      (Real.rpow_pos_of_pos (NN_pos n) _)
    refine le_trans hm ?_
    have hswap := cav_cubeProb_eqPM (N := n + 1) (pε' n)
    have hsb := small_ball_sepPM (N := n + 1) hK1 hK (pε' n) (pε'_pos n) (two_pε'_lt_one hn)
    rw [← hswap]
    rw [div_eq_mul_inv, ← Real.rpow_neg (NN_pos n).le, neg_neg, mul_comm]
    exact mul_le_mul_of_nonneg_left hsb (Real.rpow_nonneg (NN_pos n).le _)
  have hhalf : (0 : ℝ) ≤ (1 / 2) ^ (n + 1) := by positivity
  unfold Bnd
  linarith

theorem complete_convergencePM (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℕ =>
      cubeProb (n + 1) (fun x => ε < |(2 * rootCountPM x : ℝ) / n - 1|)) := by
  set ε₁ := min ε 1 with hε₁
  have hε₁pos : 0 < ε₁ := lt_min hε one_pos
  have hε₁le : ε₁ ≤ ε := min_le_left _ _
  have hε₁1 : ε₁ ≤ 1 := min_le_right _ _
  set c := ε₁ / 2 with hc
  have hcpos : 0 < c := by positivity
  have hc2 : c ≤ 1 / 2 := by rw [hc]; linarith
  apply Summable.of_norm_bounded_eventually_nat summable_bound
  have hErr := Err_eventually_le (ε₁ ^ 2 / 16) (by positivity)
  filter_upwards [hErr, pK_le_N_eventually, eventually_ge_atTop 3] with n hE hK hn
  rw [Real.norm_of_nonneg (cubeProb_nonneg _ _)]
  refine le_trans ?_ (Bnd_le hn)
  refine le_trans (cubeProb_mono (fun x hx => ?_)) (prob_badPM (by omega) hK hcpos hc2)
  intro hG
  have hb := good_boundPM hn hcpos hc2 x hG
  have h4 : 4 * Err n / c ≤ ε₁ / 2 := by
    rw [hc, div_le_iff₀ (by positivity)]
    nlinarith
  have : |(2 * rootCountPM x : ℝ) / n - 1| < ε := by
    have : c / 2 = ε₁ / 4 := by rw [hc]; ring
    linarith
  linarith

end

end E522

end

/- ## The targets -/

section

open MeasureTheory Filter
open scoped ProbabilityTheory Topology Real

namespace Erdos522

/-- The Formal Conjectures statement `erdos_522` (coefficients `±1`) with the answer `True`. -/
theorem erdos_522 :
    True ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      (c : KacCoefficients ({-1, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * c.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1 := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  intro Ω _ _ c
  have key := E522.transferPM c.toFun c.h_indep c.h_unif
    (fun m => E522.complete_convergencePM _ (by positivity))
  have hcount : ∀ ω (n : ℕ),
      c.numRootsInUnitDisk n ω = E522.rawCount (fun i => c.toFun i ω) n := fun ω n => rfl
  simp_rw [hcount]
  exact key

/-- The Formal Conjectures statement `erdos_522.variants.zero_one` (coefficients `0/1`) with
the answer `True`. -/
theorem erdos_522.variants.zero_one :
    True ↔ ∀ {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
      {n : ℕ} (hn : 1 ≤ n) (f : KacCoefficients ({0, 1} : Set ℂ) Ω),
      ℙ {ω | atTop.Tendsto (fun n : ℕ ↦ (2 * f.numRootsInUnitDisk n ω : ℝ) / n) (𝓝 1)} = 1 := by
  refine ⟨fun _ => ?_, fun _ => trivial⟩
  intro Ω _ _ n _ f
  have key := E522.transfer f.toFun f.h_indep f.h_unif
    (fun m => E522.complete_convergence _ (by positivity))
  have hcount : ∀ ω (n : ℕ),
      f.numRootsInUnitDisk n ω = E522.rawCount (fun i => f.toFun i ω) n := fun ω n => rfl
  simp_rw [hcount]
  exact key

#print axioms erdos_522
#print axioms erdos_522.variants.zero_one

end Erdos522

end
