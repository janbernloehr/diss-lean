import NLS.KdV.HillHminusPhysicalPeriodicLabels

/-! # Literal original even Fourier source in the rough Hill family -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

def hillOriginalHminusSource :
    WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp ((Fourier.paritySample 0).comp SpectralWeight.one.toCoeff)

theorem hillOriginalHminusSource_apply
    (q : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    (hillOriginalHminusSource q).val k=q.val (2*k) := by
  change (periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q))).val k=_
  rw [periodOneL2Inclusion_apply,hillUnitSample_apply,SpectralWeight.toCoeff_apply]

theorem hillOriginalHminusSource_eq_physical (p : RealPeriodOneHillPotential) :
    hillOriginalHminusSource p.val=(hillPhysicalHminusEmbedding p).val := rfl

theorem hillHminusDiscriminant_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ) :
    hillHminusDiscriminant (hillOriginalHminusSource q) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff q) E := by
  change hillHminusDiscriminant
    (periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q))) E=_
  rw [hillHminusDiscriminant_eq_hillL2,hillPeriodDouble_unitSample _ hq]

end NLS.KdV
