import NLS.KdV.SingularDirichletForcedRows
import NLS.KdV.SingularDirichletCharacteristicSufficiency

/-! # Inhomogeneous physical rows for every original complex source

The actual shifted Miura chart is chosen from the original potential. Its
constant energy shift cancels in every associated-vector equation; forcing
is the unchanged preceding native vector.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat

/-- Translating potential and energy together leaves every inhomogeneous
native equation unchanged, including its forcing vector. -/
theorem singularDirichlet_source_forced_add_constant_iff
    (q : PeriodOneHminusOne) (lambda c : ℂ) (f g : UnitDirichletH1) :
    singularDirichletOperator (periodOneOriginal (q+periodOneL2Inclusion (lp.single 2 0 c))) f-
      (lambda+c) • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g ↔
    singularDirichletOperator (periodOneOriginal q) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g := by
  rw [singularDirichletOperator_source_add_constant]
  have he : singularDirichletOperator (periodOneOriginal q) f+c • singularDirichletDomainInclusion f-
      (lambda+c) • singularDirichletDomainInclusion f =
      singularDirichletOperator (periodOneOriginal q) f-lambda • singularDirichletDomainInclusion f := by
    module
  exact Iff.of_eq (congrArg (fun v : UnitDirichletHminus => v = singularDirichletDomainInclusion g) he)

/-- The chosen shifted Miura chart preserves every actual chain equation. -/
theorem singularDirichlet_forced_iff_shiftedMiura (q : PeriodOneHminusOne)
    (lambda : ℂ) (f g : UnitDirichletH1) :
    singularDirichletOperator (periodOneOriginal q) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g ↔
    singularDirichletOperator (periodOneOriginal (periodOneMiura ((hillHminusMiuraChartAt q).lift q))) f-
      (lambda+(hillHminusMiuraChartAt q).energyShift) • singularDirichletDomainInclusion f =
        singularDirichletDomainInclusion g := by
  rw [(hillHminusMiuraChartAt q).image q (mem_hillHminusMiuraChartAt q)]
  exact (singularDirichlet_source_forced_add_constant_iff q lambda
    (hillHminusMiuraChartAt q).energyShift f g).symm

/-- Exact inhomogeneous physical row criterion at EVERY complex original
H-minus-one source and EVERY complex energy, including zero. -/
theorem singularDirichlet_source_forced_iff_physical_rows (q : PeriodOneHminusOne)
    (lambda : ℂ) (f g : UnitDirichletH1) :
    singularDirichletOperator (periodOneOriginal q) f-
      lambda • singularDirichletDomainInclusion f = singularDirichletDomainInclusion g ↔
    let u := (hillHminusMiuraChartAt q).lift q
    let mu := lambda+(hillHminusMiuraChartAt q).energyShift
    ∃ G : ℝ → ℂ, Continuous G ∧ AbsolutelyContinuousOnInterval G 0 1 ∧
      MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (unitDirichletRepresentative f)
        (unitL2SynthesisEquiv u x*unitDirichletRepresentative f x+G x) x) ∧
      (∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt G
        (-mu*unitDirichletRepresentative f x-unitL2SynthesisEquiv u x*G x-
          unitDirichletRepresentative g x) x) := by
  rw [singularDirichlet_forced_iff_shiftedMiura]
  exact singularDirichletMiura_forced_iff_physical_rows
    ((hillHminusMiuraChartAt q).lift q) (lambda+(hillHminusMiuraChartAt q).energyShift) f g

end NLS.KdV
