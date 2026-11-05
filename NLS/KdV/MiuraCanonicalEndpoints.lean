import NLS.KdV.HillMiuraL2Discriminant
import NLS.ZakharovShabat.PeriodicEndpointGlobalMultiplicity
import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity

/-! Literal canonical endpoint definitions and diagonal reality,
separated from the native singular-operator multiplicity comparison. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- Actual left Dirac endpoint of the fixed diagonal L2 potential. -/
def hillMiuraDiracLeft (u : Coeff 2) (n : ℤ) : ℂ :=
  canonicalPeriodicLeft (by norm_num) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _) n

/-- Actual right Dirac endpoint of the fixed diagonal L2 potential. -/
def hillMiuraDiracRight (u : Coeff 2) (n : ℤ) : ℂ :=
  canonicalPeriodicRight (by norm_num) (by norm_num)
    (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _) n

/-- The original real diagonal source has the actual Dirac real form. -/
theorem isRealType_hillMiuraDiagonal (u : PeriodOneRealL2) :
    IsRealType (CoeffPair.toMax 2 (hillMiuraDiagonal u.val)) := by
  intro n
  change (hillMiuraDiagonal u.val).snd n=conj ((hillMiuraDiagonal u.val).fst (-n))
  rw [hillMiuraDiagonal_snd,hillMiuraDiagonal_fst]
  simpa only [neg_neg] using u.property (-n)

end NLS.KdV
