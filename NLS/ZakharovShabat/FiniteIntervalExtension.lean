import NLS.ZakharovShabat.IntervalExtension
import NLS.Fourier.IntervalKernelLp
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Actual coefficient-space extensions of finite Fourier input

The maps below take finitely supported period-one coefficients to the existing
period-two boundary spaces. Their coefficients equal the Fourier integrals of
the physical reflected extension. The construction works for `1 < p ≤ ∞`;
the uniform bound and completion are proved at `p=2` in
`HilbertIntervalExtension` and for every `1<p<∞` in `BoundedIntervalExtension`.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} (hp : 1 < p)

/-- The normalized interval kernel as an element of the sequence space. -/
def intervalKernelCoeffs : Coeff p := ⟨overlap 0, overlap_zero_memlp hp⟩

@[simp] theorem intervalKernelCoeffs_apply (n : ℤ) : intervalKernelCoeffs hp n = overlap 0 n := rfl

variable [Fact (1 ≤ p)]

/-- The half-interval coefficients of a finite period-one polynomial, as a linear map. -/
def polynomialHalfCoeffs : (ℤ →₀ ℂ) →ₗ[ℂ] Coeff p :=
  Finsupp.linearCombination ℂ (fun k => Coeff.shift (2 * k) (intervalKernelCoeffs hp))

/-- The sequence-space construction agrees with the defining physical integral. -/
theorem polynomialHalfCoeffs_apply (a : ℤ →₀ ℂ) (n : ℤ) :
    polynomialHalfCoeffs hp a n = halfCoefficient (polynomial a) n := by
  rw [polynomialHalfCoeffs, Finsupp.linearCombination_apply, halfCoefficient_polynomial]
  simp only [Finsupp.sum, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, Coeff.shift_apply, intervalKernelCoeffs_apply, ← overlap_shift]

end NLS.Fourier

namespace NLS.ZakharovShabat.BoundaryCondition
open NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : BoundaryCondition) (hp : 1 < p)

/-- The boundary-mode amplitudes of a finite period-one pair. -/
def finiteIntervalAmplitude : ((ℤ →₀ ℂ) × (ℤ →₀ ℂ)) →ₗ[ℂ] Coeff p :=
  (polynomialHalfCoeffs hp).comp (LinearMap.snd ℂ _ _) +
    extensionSign b • (Coeff.reflection.toLinearMap.comp (polynomialHalfCoeffs hp)).comp
      (LinearMap.fst ℂ _ _)

theorem finiteIntervalAmplitude_apply (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    finiteIntervalAmplitude b hp a n = intervalAmplitude b (periodOnePair a) n := by
  change polynomialHalfCoeffs hp a.2 n + extensionSign b * polynomialHalfCoeffs hp a.1 (-n) = _
  simp only [polynomialHalfCoeffs_apply]
  rfl

/-- The physical finite-input extension in the existing period-two pair space. -/
def finiteIntervalExtension : ((ℤ →₀ ℂ) × (ℤ →₀ ℂ)) →ₗ[ℂ] PairSpace p :=
  ((extensionSign b • Coeff.reflection.toLinearMap).comp (finiteIntervalAmplitude b hp)).prod
    (finiteIntervalAmplitude b hp)

@[simp] theorem finiteIntervalExtension_snd (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    (finiteIntervalExtension b hp a).2 = finiteIntervalAmplitude b hp a := rfl

@[simp] theorem finiteIntervalExtension_fst (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    (finiteIntervalExtension b hp a).1 = extensionSign b • Coeff.reflection (finiteIntervalAmplitude b hp a) := rfl

/-- Finite input lands in the selected Dirichlet or Neumann space. -/
theorem finiteIntervalExtension_mem (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteIntervalExtension b hp a ∈ space b := by
  cases b <;> simp [space, mem_dirichletSubspace, mem_neumannSubspace,
    finiteIntervalExtension_fst, extensionSign]

/-- The actual second-component Fourier integrals equal the constructed `ℓp` coefficients. -/
theorem finiteIntervalExtension_coefficient_snd (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).2) n =
      (finiteIntervalExtension b hp a).2 n := by
  rw [intervalExtension_coefficient_snd b _ (continuous_periodOnePair a),
    finiteIntervalExtension_snd, finiteIntervalAmplitude_apply]

/-- The actual first-component Fourier integrals equal the constructed `ℓp` coefficients. -/
theorem finiteIntervalExtension_coefficient_fst (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) (n : ℤ) :
    periodTwoCoefficient (fun x => (intervalExtension b (periodOnePair a) x).1) n =
      (finiteIntervalExtension b hp a).1 n := by
  rw [intervalExtension_coefficient_fst b _ (continuous_periodOnePair a)]
  change _ = extensionSign b * finiteIntervalAmplitude b hp a (-n)
  rw [finiteIntervalAmplitude_apply]

/-- The endpoint failure already occurs for the constant input `(0,1)`. -/
theorem not_memlp_intervalAmplitude_oneSided :
    ¬Memℓp (intervalAmplitude b (fun _ => ((0 : ℂ), 1))) 1 := by
  rw [show intervalAmplitude b (fun _ => ((0 : ℂ), 1)) = overlap 0 from
    funext (intervalAmplitude_oneSided b)]
  exact not_memlp_overlap_zero_one

/-- The endpoint obstruction concerns the physical Fourier coefficients themselves. -/
theorem not_memlp_intervalExtension_oneSided :
    ¬Memℓp (fun n => periodTwoCoefficient
      (fun x => (intervalExtension b (fun _ => ((0 : ℂ), 1)) x).2) n) 1 := by
  simpa only [intervalExtension_coefficient_snd b _ continuous_const] using
    not_memlp_intervalAmplitude_oneSided b

end NLS.ZakharovShabat.BoundaryCondition
