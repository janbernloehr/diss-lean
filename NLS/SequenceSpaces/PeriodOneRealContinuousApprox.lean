import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity
import NLS.SequenceSpaces.PeriodDoubling
import NLS.Fourier.ContinuousSynthesisReality

/-! # Literal continuous real representatives of the H-minus-one truncations

The finite approximants use the same raw unit-period coefficients as the
existing H-minus-one density proof. Their physical continuous period-two
realizations have exactly the doubled coefficients, without renormalization.
-/
noncomputable section
set_option autoImplicit false
open Complex Set
open scoped ComplexConjugate ENNReal Classical
namespace NLS

def periodOneFiniteL1Approx (q : PeriodOneHminusOne) (S : Finset ℤ) : Coeff 1 :=
  Coeff.ofFinsupp (Finsupp.onFinset S (WeightedCoeff.truncate (Weight.sobolev (-1)) 2 S q).val
    (by intro k hk; by_contra h; exact hk (by simp [h])))

@[simp] theorem periodOneFiniteL1Approx_apply (q : PeriodOneHminusOne) (S : Finset ℤ) (k : ℤ) :
    periodOneFiniteL1Approx q S k = if k ∈ S then q.val k else 0 := by
  simp [periodOneFiniteL1Approx, Coeff.ofFinsupp_apply]

theorem periodOneFiniteL1Approx_real (q : PeriodOneRealHminusOne) (S : Finset ℤ) :
    ∀ k : ℤ, periodOneFiniteL1Approx q.val (periodOneSymmetricSupport S) (-k) =
      conj (periodOneFiniteL1Approx q.val (periodOneSymmetricSupport S) k) := by
  intro k
  by_cases hk : k ∈ periodOneSymmetricSupport S <;> simp [hk,q.property k]

def periodOneFiniteContinuousApprox (q : PeriodOneHminusOne) (S : Finset ℤ) :
    C(AddCircle (2 : ℝ), ℂ) :=
  Fourier.continuousSynthesis (Coeff.periodDouble (periodOneFiniteL1Approx q S))

theorem continuousFourierCLM_periodOneFiniteContinuousApprox
    (q : PeriodOneHminusOne) (S : Finset ℤ) :
    Fourier.continuousFourierCLM (periodOneFiniteContinuousApprox q S) =
      Coeff.periodDouble (periodOneFiniteL2Approx q S) := by
  ext k
  rw [Fourier.continuousFourierCLM_apply, periodOneFiniteContinuousApprox,
    Fourier.fourierCoeff_continuousSynthesis]
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he, Coeff.periodDouble_even, Coeff.periodDouble_even]
    simp
  · have he : k = 2*(k/2)+1 := by omega
    rw [he, Coeff.periodDouble_odd, Coeff.periodDouble_odd]

theorem periodOneFiniteContinuousApprox_im_eq_zero
    (q : PeriodOneRealHminusOne) (S : Finset ℤ) (x : ℝ) :
    (periodOneFiniteContinuousApprox q.val (periodOneSymmetricSupport S)
      (x : AddCircle (2 : ℝ))).im = 0 := by
  apply Fourier.continuousSynthesis_im_eq_zero_of_reflection
  intro k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,show -(2*(k/2)) = 2*(-(k/2)) by ring,
      Coeff.periodDouble_even,Coeff.periodDouble_even]
    exact periodOneFiniteL1Approx_real q S (k/2)
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,show -(2*(k/2)+1) = 2*(-(k/2)-1)+1 by ring,
      Coeff.periodDouble_odd,Coeff.periodDouble_odd,map_zero]

end NLS
