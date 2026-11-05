import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.KdV.HillHminusOneDirichlet
import NLS.KdV.HillL2Dirichlet

/-! # The literal original derivative-one characteristic in rough coordinates -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem hillHminusDirichlet_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ) :
    hillHminusDirichlet (hillOriginalHminusSource q) E=
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E := by
  change hillHminusDirichlet (periodOneL2Inclusion
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q))) E=_
  rw [hillHminusDirichlet_eq_hillL2,hillPeriodDouble_unitSample _ hq]
  exact hillL2Dirichlet_eq_characteristic _ _

end NLS.KdV
