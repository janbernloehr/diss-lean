import NLS.KdV.HillHminusOneDiscriminant
import NLS.KdV.HillHminusOneDirichlet
import NLS.KdV.HillNativeCotangentExtension
import NLS.KdV.HillPeriodOneRestrictionInverse

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical
namespace NLS.KdV

/-- The native Hilbert direction adapter is the literal original even-index
insertion, with no source-dependent or norm-compatible replacement. -/
theorem hillNativeHilbertDirection_eq_periodDouble :
    hillNativeHilbertDirection=(Coeff.periodDouble (p := 2)).toContinuousLinearMap := rfl

/-- The spectral extension and scalar Gardner calculus use the same literal
coefficient-preserving Hilbert inclusion into H-minus-one. -/
theorem periodOneL2Inclusion_eq_hilbertToHminus :
    periodOneL2Inclusion=NLS.Poisson.hilbertToHminus := by
  apply ContinuousLinearMap.ext
  intro q
  apply Subtype.ext
  funext k
  rw [periodOneL2Inclusion_apply,NLS.Poisson.hilbertToHminus_apply]

/-- The actual entire H-minus-one discriminant restricts to this worktree's
original physical Hill discriminant on every complex Hilbert source and
at every complex energy, including zero. -/
theorem hillHminusDiscriminant_native_hilbert_agreement (q : Coeff 2) (E : ℂ) :
    hillHminusDiscriminant (NLS.Poisson.hilbertToHminus q) E=
      hillL2Discriminant (hillNativeHilbertDirection q) E := by
  rw [←periodOneL2Inclusion_eq_hilbertToHminus,hillNativeHilbertDirection_eq_periodDouble]
  exact hillHminusDiscriminant_eq_hillL2 q E

/-- The actual entire H-minus-one Dirichlet family has exactly the original
rough Hill characteristic, including its fixed derivative-one initial data. -/
theorem hillHminusDirichlet_native_hilbert_agreement (q : Coeff 2) (E : ℂ) :
    hillHminusDirichlet (NLS.Poisson.hilbertToHminus q) E=
      hillL2DirichletCharacteristic (hillNativeHilbertDirection q) E := by
  rw [←periodOneL2Inclusion_eq_hilbertToHminus,hillNativeHilbertDirection_eq_periodDouble,
    hillHminusDirichlet_eq_hillL2,hillL2Dirichlet_eq_characteristic]
  rfl

/-- The actual original weighted source, in literal native H-minus-one
coordinates, obtained by its original even-index restriction. -/
def hillOriginalHminusSource :
    WeightedCoeff SpectralWeight.one.toWeight 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp (SpectralWeight.one.doubleIndex.toCoeff.comp
    (hillPeriodOneRestriction SpectralWeight.one))

theorem hillOriginalHminusSource_apply (q : WeightedCoeff SpectralWeight.one.toWeight 2) (k : ℤ) :
    (hillOriginalHminusSource q).val k=q.val (2*k) := by
  change (periodOneL2Inclusion (SpectralWeight.one.doubleIndex.toCoeff
    (hillPeriodOneRestriction SpectralWeight.one q))).val k=_
  rw [periodOneL2Inclusion_apply,SpectralWeight.toCoeff_apply,hillPeriodOneRestriction_apply]

/-- The actual source mean is unchanged by the native H-minus-one adapter. -/
theorem hillOriginalHminusSource_zero_mode (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    (hillOriginalHminusSource q).val 0=q.val 0 := by
  rw [hillOriginalHminusSource_apply,mul_zero]

private theorem double_restriction_even (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) :
    Coeff.periodDouble (SpectralWeight.one.doubleIndex.toCoeff
      (hillPeriodOneRestriction SpectralWeight.one q))=SpectralWeight.one.toCoeff q := by
  ext k
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he,Coeff.periodDouble_even,SpectralWeight.toCoeff_apply,hillPeriodOneRestriction_apply,
      SpectralWeight.toCoeff_apply]
  · have he : k=2*(k/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd]
    exact ((Coeff.mem_paritySubspace 0 _).mp hq _ (by omega)).symm

/-- All-energy exact agreement of the H-minus-one extension with the
literal original rough Hill discriminant on its entire even source domain. -/
theorem hillHminusDiscriminant_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ) :
    hillHminusDiscriminant (hillOriginalHminusSource q) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff q) E := by
  change hillHminusDiscriminant (periodOneL2Inclusion (SpectralWeight.one.doubleIndex.toCoeff
    (hillPeriodOneRestriction SpectralWeight.one q))) E=_
  rw [hillHminusDiscriminant_eq_hillL2,double_restriction_even q hq]

/-- All-energy exact agreement of the H-minus-one extension with the
original derivative-one Dirichlet characteristic, for all even rough sources. -/
theorem hillHminusDirichlet_original_source_agreement
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0) (E : ℂ) :
    hillHminusDirichlet (hillOriginalHminusSource q) E=
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E := by
  change hillHminusDirichlet (periodOneL2Inclusion (SpectralWeight.one.doubleIndex.toCoeff
    (hillPeriodOneRestriction SpectralWeight.one q))) E=_
  rw [hillHminusDirichlet_eq_hillL2,hillL2Dirichlet_eq_characteristic,double_restriction_even q hq]

end NLS.KdV
