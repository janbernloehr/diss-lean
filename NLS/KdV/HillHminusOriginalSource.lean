import NLS.KdV.HillHminusOneDiscriminant
import NLS.KdV.HillHminusOriginalDirichletSourceAdapter
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

/-- The actual source mean is unchanged by the native H-minus-one adapter. -/
theorem hillOriginalHminusSource_zero_mode (q : WeightedCoeff SpectralWeight.one.toWeight 2) :
    (hillOriginalHminusSource q).val 0=q.val 0 := by
  rw [hillOriginalHminusSource_apply,mul_zero]

-- The original-source discriminant and Dirichlet agreements are reused
-- from the previously verified literal parity-sampling source adapter.

end NLS.KdV
