import NLS.ZakharovShabat.Domain
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# The coefficient-space Zakharov–Shabat operator

This implements the domain-to-base operator in Chapter 1, §3, p. 23.
Both components use scalar modes `exp (i π n x)` on the period-two circle.
The pair spaces carry the maximum norm supplied by Lean's product instance.
The dissertation uses a different, equivalent pair norm; its numerical constants
are not asserted here. The operator is bounded from the one-derivative domain
into the base space. Closedness of its unbounded realization is proved in
`NLS.ZakharovShabat.ClosedOperator`.
-/

open scoped ENNReal
noncomputable section

namespace NLS.ZakharovShabat

/-- Pairs `(f₋, f₊)` of Fourier coefficients, with the maximum norm. -/
abbrev PairSpace (p : ℝ≥0∞) := Coeff p × Coeff p

/-- Pairs with one weighted derivative, with the maximum norm. -/
abbrev Domain (p : ℝ≥0∞) := ScalarDomain p × ScalarDomain p

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical inclusion of the operator domain into the base space. -/
def domainInclusion : Domain p →L[ℂ] PairSpace p :=
  scalarInclusion.prodMap scalarInclusion

@[simp] theorem domainInclusion_apply (f : Domain p) :
    domainInclusion f = (scalarInclusion f.1, scalarInclusion f.2) := rfl

theorem domainInclusion_injective : Function.Injective (domainInclusion (p := p)) := by
  intro f g h
  exact Prod.ext (scalarInclusion_injective (congrArg Prod.fst h))
    (scalarInclusion_injective (congrArg Prod.snd h))

theorem norm_domainInclusion_le (f : Domain p) : ‖domainInclusion f‖ ≤ ‖f‖ := by
  exact norm_prod_le_iff.mpr
    ⟨(norm_scalarInclusion_le f.1).trans (norm_fst_le f),
      (norm_scalarInclusion_le f.2).trans (norm_snd_le f)⟩

theorem domainInclusion_denseRange (hp : p ≠ ⊤) :
    DenseRange (domainInclusion (p := p)) :=
  (scalarInclusion_denseRange hp).prodMap (scalarInclusion_denseRange hp)

/-- The free operator `diag(i, -i) ∂ₓ`. -/
def freeOperator : Domain p →L[ℂ] PairSpace p :=
  (Complex.I • derivative).prodMap (-Complex.I • derivative)

@[simp] theorem freeOperator_fst_apply (f : Domain p) (n : ℤ) :
    (freeOperator f).1 n = -(Real.pi : ℂ) * n * f.1.val n := by
  change Complex.I * (Complex.I * (Real.pi : ℂ) * n * f.1.val n) = _
  simp only [← mul_assoc, Complex.I_mul_I, neg_one_mul]

@[simp] theorem freeOperator_snd_apply (f : Domain p) (n : ℤ) :
    (freeOperator f).2 n = (Real.pi : ℂ) * n * f.2.val n := by
  change -Complex.I * (Complex.I * (Real.pi : ℂ) * n * f.2.val n) = _
  simp only [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]

theorem norm_freeOperator_le (f : Domain p) : ‖freeOperator f‖ ≤ Real.pi * ‖f‖ := by
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖Complex.I • derivative f.1‖ ≤ _
    simpa only [norm_smul, Complex.norm_I, one_mul] using
      (norm_derivative_le f.1).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le f) Real.pi_pos.le)
  · change ‖-Complex.I • derivative f.2‖ ≤ _
    simpa only [norm_smul, norm_neg, Complex.norm_I, one_mul] using
      (norm_derivative_le f.2).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le f) Real.pi_pos.le)

/-- The off-diagonal potential matrix `[[0, φ₋], [φ₊, 0]]`. -/
def potentialOperator (hp : p ≠ ⊤) (φ : PairSpace p) : Domain p →L[ℂ] PairSpace p :=
  ((potentialMul hp φ.1).comp (ContinuousLinearMap.snd ℂ _ _)).prod
    ((potentialMul hp φ.2).comp (ContinuousLinearMap.fst ℂ _ _))

@[simp] theorem potentialOperator_apply (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) :
    potentialOperator hp φ f = (potentialMul hp φ.1 f.2, potentialMul hp φ.2 f.1) := rfl

theorem norm_potentialOperator_le (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) :
    ‖potentialOperator hp φ f‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖ * ‖f‖ := by
  have hC := WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp
  apply norm_prod_le_iff.mpr
  constructor
  · exact (norm_potentialMul_apply_le hp φ.1 f.2).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (norm_fst_le φ) hC) (norm_snd_le f)
        (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))
  · exact (norm_potentialMul_apply_le hp φ.2 f.1).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left (norm_snd_le φ) hC) (norm_fst_le f)
        (norm_nonneg _) (mul_nonneg hC (norm_nonneg _)))

/-- `L(φ) = diag(i, -i) ∂ₓ + [[0, φ₋], [φ₊, 0]]`, on Fourier coefficients. -/
def operator (hp : p ≠ ⊤) (φ : PairSpace p) : Domain p →L[ℂ] PairSpace p :=
  freeOperator + potentialOperator hp φ

theorem operator_fst_apply (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) (n : ℤ) :
    (operator hp φ f).1 n = -(Real.pi : ℂ) * n * f.1.val n +
      ∑' k : ℤ, φ.1 (n - k) * f.2.val k := by
  change (freeOperator f).1 n + potentialMul hp φ.1 f.2 n = _
  rw [freeOperator_fst_apply, potentialMul_apply]

theorem operator_snd_apply (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) (n : ℤ) :
    (operator hp φ f).2 n = (Real.pi : ℂ) * n * f.2.val n +
      ∑' k : ℤ, φ.2 (n - k) * f.1.val k := by
  change (freeOperator f).2 n + potentialMul hp φ.2 f.1 n = _
  rw [freeOperator_snd_apply, potentialMul_apply]

theorem norm_operator_apply_le (hp : p ≠ ⊤) (φ : PairSpace p) (f : Domain p) :
    ‖operator hp φ f‖ ≤ (Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖) * ‖f‖ := by
  calc
    _ ≤ ‖freeOperator f‖ + ‖potentialOperator hp φ f‖ := norm_add_le _ _
    _ ≤ Real.pi * ‖f‖ + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖ * ‖f‖ :=
      add_le_add (norm_freeOperator_le f) (norm_potentialOperator_le hp φ f)
    _ = _ := by ring

theorem norm_operator_le (hp : p ≠ ⊤) (φ : PairSpace p) :
    ‖operator hp φ‖ ≤ Real.pi + WeightedCoeff.sobolevEmbeddingConstant p hp * ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg Real.pi_pos.le (mul_nonneg
      (WeightedCoeff.sobolevEmbeddingConstant_nonneg p hp) (norm_nonneg _)))
    (norm_operator_apply_le hp φ)

@[simp] theorem operator_zero (hp : p ≠ ⊤) :
    operator hp (0 : PairSpace p) = freeOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply Prod.ext <;> ext n
  · simp [operator_fst_apply]
  · simp [operator_snd_apply]

/-- The dissertation's signed mode `eₙ⁻ = (exp (-i π n x), 0)`. -/
def negativeMode (n : ℤ) : Domain p := (scalarMode (-n) 1, 0)

/-- The dissertation's signed mode `eₙ⁺ = (0, exp (i π n x))`. -/
def positiveMode (n : ℤ) : Domain p := (0, scalarMode n 1)

/-- Both signed components have free eigenvalue `π n`. -/
theorem freeOperator_negativeMode (n : ℤ) :
    freeOperator (negativeMode (p := p) n) =
      ((Real.pi : ℂ) * n) • domainInclusion (negativeMode n) := by
  apply Prod.ext <;> ext k
  · by_cases h : k = -n <;> simp [negativeMode, h]
  · simp [negativeMode]

/-- Both signed components have free eigenvalue `π n`. -/
theorem freeOperator_positiveMode (n : ℤ) :
    freeOperator (positiveMode (p := p) n) =
      ((Real.pi : ℂ) * n) • domainInclusion (positiveMode n) := by
  apply Prod.ext <;> ext k
  · simp [positiveMode]
  · by_cases h : k = n <;> simp [positiveMode, h]

theorem domainInclusion_negativeMode_ne_zero (n : ℤ) :
    domainInclusion (negativeMode (p := p) n) ≠ 0 := by
  intro h
  have hc := congrArg (fun a : PairSpace p => a.1 (-n)) h
  simp [negativeMode] at hc

theorem domainInclusion_positiveMode_ne_zero (n : ℤ) :
    domainInclusion (positiveMode (p := p) n) ≠ 0 := by
  intro h
  have hc := congrArg (fun a : PairSpace p => a.2 n) h
  simp [positiveMode] at hc

/-- Unit off-diagonal potentials exchange the two included components. -/
theorem potentialOperator_unit (hp : p ≠ ⊤) (f : Domain p) :
    potentialOperator hp (lp.single p 0 1, lp.single p 0 1) f =
      (scalarInclusion f.2, scalarInclusion f.1) := by
  apply Prod.ext <;> ext n <;>
    simp [potentialMul_unit_apply]

/-- The spectral equation is a map between the domain and base space. -/
def spectralPencil (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    Domain p →L[ℂ] PairSpace p := z • domainInclusion - operator hp φ

@[simp] theorem spectralPencil_apply (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) (f : Domain p) :
    spectralPencil hp φ z f = z • domainInclusion f - operator hp φ f := rfl

end NLS.ZakharovShabat
