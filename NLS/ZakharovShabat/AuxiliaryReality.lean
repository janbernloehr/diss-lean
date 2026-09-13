import NLS.Fourier.HalfIntervalReality
import NLS.ZakharovShabat.RealType
import NLS.ZakharovShabat.AuxiliaryEigenvalueAsymptotics

/-!
# Real source potentials and the auxiliary spectrum

The completed source Neumann potential extension preserves real type at every
`1 < p < ∞`. Proposition 5.2(iv) follows for both actual auxiliary restrictions
from their eigenvector characterization and the full operator's symmetry.
-/

noncomputable section
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
open NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The potential phase preserves the physical conjugation relation in Fourier coordinates. -/
theorem IsRealType.auxiliaryPotential (φ : PairSpace p) (hφ : IsRealType φ) :
    IsRealType (auxiliaryPotential φ) := by
  intro n
  change -Complex.I * φ.2 n = (starRingEnd ℂ) (Complex.I * φ.1 (-n))
  rw [hφ n, map_mul, Complex.conj_I]

namespace BoundaryCondition

/-- Both completed signed source extensions preserve real type. -/
theorem isRealType_intervalExtensionCLM (b : BoundaryCondition) (hp : 1 < p) (hptop : p ≠ ⊤)
    (φ : PairSpace p) (hφ : IsRealType φ) : IsRealType (intervalExtensionCLM b hp hptop φ) := by
  intro n
  change intervalAmplitudeCLM b hp hptop φ n =
    (starRingEnd ℂ) (extensionSign b * intervalAmplitudeCLM b hp hptop φ (-(-n)))
  rw [neg_neg]
  change halfIntervalCoeffs hp hptop φ.2 n +
    extensionSign b * halfIntervalCoeffs hp hptop φ.1 (-n) =
    (starRingEnd ℂ) (extensionSign b * (halfIntervalCoeffs hp hptop φ.2 n +
      extensionSign b * halfIntervalCoeffs hp hptop φ.1 (-n)))
  rw [halfIntervalCoeffs_conj hp hptop φ.1 φ.2 hφ n]
  cases b <;> simp [extensionSign, add_comm]

/-- Every actual auxiliary spectral value of a real-type reflected potential is real. -/
theorem auxiliarySpectrum_im_eq_zero_of_realType (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (hr : IsRealType φ)
    (z : ℂ) (hz : z ∈ auxiliarySpectrum b hp φ hφ) : z.im = 0 := by
  obtain ⟨f, _, hf, he⟩ := (mem_auxiliarySpectrum_iff_exists_eigenvector b hp φ hφ z).mp hz
  exact eigenvalue_im_eq_zero_of_realType hp φ hr z f hf he

/-- Nonreal parameters belong to the actual auxiliary resolvent set. -/
theorem mem_auxiliaryResolventSet_of_realType_of_im_ne_zero (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ neumannSubspace) (hr : IsRealType φ)
    (z : ℂ) (hz : z.im ≠ 0) : z ∈ auxiliaryResolventSet b hp φ hφ := by
  by_contra h
  exact hz (auxiliarySpectrum_im_eq_zero_of_realType b hp φ hφ hr z h)

end BoundaryCondition

/-- The source Neumann potential extension used for both starred problems preserves real type. -/
theorem isRealType_auxiliaryPeriodOnePotential (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    IsRealType (auxiliaryPeriodOnePotential hp hp1 φ).val :=
  BoundaryCondition.isRealType_intervalExtensionCLM .neumann hp1 hp _ hφ

/-- Proposition 5.2(iv) for original period-one coefficient potentials at every `1 < p < ∞`. -/
theorem auxiliaryPeriodOneSpectrum_im_eq_zero_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ b.auxiliarySpectrum hp (auxiliaryPeriodOnePotential hp hp1 φ).val
      (auxiliaryPeriodOnePotential hp hp1 φ).property) : z.im = 0 :=
  b.auxiliarySpectrum_im_eq_zero_of_realType hp _ _
    (isRealType_auxiliaryPeriodOnePotential hp hp1 φ hφ) z hz

end NLS.ZakharovShabat
