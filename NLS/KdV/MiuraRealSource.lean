import NLS.KdV.HminusOneMiuraHighPairs

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The actual original real diagonal Dirac source of a real scalar lift. -/
def hillMiuraRealSource (u : PeriodOneRealL2) : realTypeSourceSubmodule 2 :=
  ⟨hillMiuraDiagonal u.val,isRealType_hillMiuraDiagonal u⟩

/-- A nonzero scalar characteristic at the translated zero frequency
excludes zero from the actual Dirac spectrum. -/
theorem zero_not_mem_periodicSpectrum_of_shifted_miura_of_radicand_ne_zero
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (hc : hillHminusRadicand q (-c) ≠ 0) :
    (0:ℂ) ∉ periodicSpectrum (by norm_num) (periodOnePotential (hillMiuraDiagonal u)) := by
  intro hz
  have hd := (canonicalDiscriminant_sq_eq_four_iff
    (periodOnePotential (hillMiuraDiagonal u)) (periodOnePotential_mem _) 0).mpr hz
  have ht := hillHminusDiscriminant_shifted_miura_square q u c 0 himage
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub] at ht
  apply hc
  rw [hillHminusRadicand,ht,hd,sub_self]

end NLS.KdV
