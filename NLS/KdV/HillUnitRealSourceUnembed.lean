import NLS.KdV.HillUnitRealSourceCoordinates
import NLS.Fourier.PeriodTwoRestriction

/-! # Exact continuous inverse of the physical unit-weight source embedding -/
noncomputable section
open Set Complex
open scoped ComplexConjugate
namespace NLS.KdV

@[simp] theorem hillUnitSample_apply (v : Coeff 2) (j : ℤ) :
    Fourier.paritySample 0 v j = v (2*j) := by
  rw [Fourier.paritySample_apply,add_zero]

theorem hillUnitSample_periodDouble (u : Coeff 2) :
    Fourier.paritySample 0 (Coeff.periodDouble u) = u := by ext j; simp

theorem hillPeriodDouble_unitSample (v : Coeff 2) (hv : v ∈ Coeff.paritySubspace 0) :
    Coeff.periodDouble (Fourier.paritySample 0 v) = v := by
  have he : Fourier.paritySample 0 v = Coeff.periodHalve v := by ext j; simp
  rw [he,Coeff.periodDouble_periodHalve,(Coeff.parityProjection_eq_self_iff 0 v).mpr hv]

def hillUnitRealSourceUnembed (p : RealPeriodOneHillPotential) :
    RealHillWeightedPotential SpectralWeight.one :=
  hillUnitRealSourceLift (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))
    ((periodOneL2Conjugation_fixed_iff _).mpr (by
      intro j
      simp only [hillUnitSample_apply,show 2*(-j) = -(2*j) by ring]
      exact p.property.2 (2*j)))

theorem hillUnitRealSourceUnembed_toCoeff (p : RealPeriodOneHillPotential) :
    SpectralWeight.one.doubleIndex.toCoeff (hillUnitRealSourceUnembed p).val =
      Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val) :=
  hillUnitRealSourceLift_toCoeff _ _

theorem hillRealWeightedEmbedding_toCoeff (p : RealHillWeightedPotential SpectralWeight.one) :
    SpectralWeight.one.toCoeff (hillRealWeightedEmbedding SpectralWeight.one p).val =
      Coeff.periodDouble (SpectralWeight.one.doubleIndex.toCoeff p.val) := by
  exact (toCoeff_hillPeriodOneUnitPotential SpectralWeight.one p.val).trans
    (toCoeff_hillPeriodOnePotential SpectralWeight.one p.val)

theorem hillRealWeightedEmbedding_unitUnembed (p : RealPeriodOneHillPotential) :
    hillRealWeightedEmbedding SpectralWeight.one (hillUnitRealSourceUnembed p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  have he : SpectralWeight.one.toCoeff
      (hillRealWeightedEmbedding SpectralWeight.one (hillUnitRealSourceUnembed p)).val =
      SpectralWeight.one.toCoeff p.val := by
    rw [hillRealWeightedEmbedding_toCoeff,hillUnitRealSourceUnembed_toCoeff]
    exact hillPeriodDouble_unitSample _ p.property.1
  simpa only [SpectralWeight.toCoeff_apply] using congrArg (fun a : Coeff 2 => a j) he

theorem hillUnitUnembed_realWeightedEmbedding (p : RealHillWeightedPotential SpectralWeight.one) :
    hillUnitRealSourceUnembed (hillRealWeightedEmbedding SpectralWeight.one p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  have he : SpectralWeight.one.doubleIndex.toCoeff
      (hillUnitRealSourceUnembed (hillRealWeightedEmbedding SpectralWeight.one p)).val =
      SpectralWeight.one.doubleIndex.toCoeff p.val := by
    rw [hillUnitRealSourceUnembed_toCoeff,hillRealWeightedEmbedding_toCoeff,hillUnitSample_periodDouble]
  simpa only [SpectralWeight.toCoeff_apply] using congrArg (fun a : Coeff 2 => a j) he

theorem continuous_hillUnitRealSourceUnembed : Continuous hillUnitRealSourceUnembed := by
  apply Continuous.subtype_mk
  exact hillUnitSourceLift.continuous.comp
    ((Fourier.paritySample (p := 2) 0).continuous.comp
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val))

end NLS.KdV
