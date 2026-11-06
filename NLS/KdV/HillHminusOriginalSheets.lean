import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- The actual H-minus-one radicand retains the original even-source normalization. -/
theorem hillHminusRadicand_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ) :
    hillHminusRadicand (hillOriginalHminusSource q) E=
      hillL2Radicand (SpectralWeight.one.toCoeff q) E := by
  rw [hillHminusRadicand,hillL2Radicand,hillHminusDiscriminant_original_source_agreement q hq]

/-- The original physical continuation domain is exactly the restriction
of the actual H-minus-one source continuation domain. -/
theorem hillHminusContinuationDomain_original_source_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ) :
    (E,hillOriginalHminusSource q)∈hillHminusContinuationDomain ↔
      (E,SpectralWeight.one.toCoeff q)∈hillL2ContinuationDomain := by
  change (E,periodOneL2Inclusion (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q)))∈hillHminusContinuationDomain ↔ _
  rw [hillHminusContinuationDomain_L2_iff,hillPeriodDouble_unitSample (SpectralWeight.one.toCoeff q) hq]

/-- The source-continued square root has exactly its original physical sign. -/
theorem hillHminusContinuedRoot_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ)
    (ht : (E,SpectralWeight.one.toCoeff q)∈hillL2ContinuationDomain) :
    hillHminusContinuedRoot (E,hillOriginalHminusSource q)=
      hillL2ContinuedRoot (E,SpectralWeight.one.toCoeff q) := by
  have ht' : (E,Coeff.periodDouble (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q)))∈hillL2ContinuationDomain := by
    rw [hillPeriodDouble_unitSample (SpectralWeight.one.toCoeff q) hq]
    exact ht
  have h := hillHminusContinuedRoot_eq_hillL2 E
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q)) ht'
  rw [hillPeriodDouble_unitSample (SpectralWeight.one.toCoeff q) hq] at h
  exact h

/-- The continued primitive agrees literally, with its original logarithm
period; equality is stronger than equality of its exponential or square. -/
theorem hillHminusContinuedPrimitive_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ)
    (ht : (E,SpectralWeight.one.toCoeff q)∈hillL2ContinuationDomain) :
    hillHminusContinuedPrimitive (E,hillOriginalHminusSource q)=
      hillL2ContinuedPrimitive (E,SpectralWeight.one.toCoeff q) := by
  have ht' : (E,Coeff.periodDouble (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q)))∈hillL2ContinuationDomain := by
    rw [hillPeriodDouble_unitSample (SpectralWeight.one.toCoeff q) hq]
    exact ht
  have h := hillHminusContinuedPrimitive_eq_hillL2 E
    (Fourier.paritySample 0 (SpectralWeight.one.toCoeff q)) ht'
  rw [hillPeriodDouble_unitSample (SpectralWeight.one.toCoeff q) hq] at h
  exact h

/-- Literal original Fourier reality is retained by the H-minus-one source adapter. -/
theorem hillOriginalHminusSource_real
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    IsRealPeriodOneHminusOne (hillOriginalHminusSource q) := by
  intro k
  simp only [hillOriginalHminusSource_apply,mul_neg]
  simpa only [SpectralWeight.toCoeff_apply] using hr (2*k)

end NLS.KdV
