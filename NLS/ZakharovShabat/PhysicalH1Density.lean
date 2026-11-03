import NLS.ZakharovShabat.SourceLemmaG2Unit
import NLS.ZakharovShabat.SourcePhysicalL2Equiv
import NLS.Fourier.UnitIntervalSobolevRealization

/-! Exact physical realization and density of unit-period H1 potentials
in the ENTIRE ordinary physical L2 source space on the unit interval. -/
noncomputable section
open Set MeasureTheory
open NLS.Fourier
namespace NLS.ZakharovShabat

/-- The physical H1 class is the IDENTICAL Fourier L2 synthesis, with no
norm change, period rescaling or restriction on the physical L2 target. -/
theorem sourcePeriodicH1L2Class_eq_sourcePhysical (a : ScalarDomain 2 × ScalarDomain 2) :
    sourcePeriodicH1L2Class a = sourcePhysicalL2 (sobolevSourceInclusion a) := by
  apply intervalL2Representative_injective
  have hleft := intervalL2Representative_ofFunction (sourcePeriodicH1Potential a)
    (memLp_sourcePeriodicH1Potential a)
  have h1 := unitL2Synthesis_scalarInclusion a.1
  have h2 := unitL2Synthesis_scalarInclusion a.2
  rw [← sourcePhysicalL2Equiv_apply]
  change intervalL2Representative (sourcePeriodicH1L2Class a) =ᵐ[volume.restrict (Ioc 0 1)]
    (fun x => (unitL2SynthesisEquiv (scalarInclusion a.1) x,
      unitL2SynthesisEquiv (scalarInclusion a.2) x))
  filter_upwards [hleft,h1,h2] with x hx hx1 hx2
  exact hx.trans (Prod.ext hx1 hx2).symm

/-- Physical H1 potentials are dense in ALL physical L2 potentials. -/
theorem denseRange_sourcePeriodicH1L2Class : DenseRange sourcePeriodicH1L2Class := by
  have hd : DenseRange sobolevSourceInclusion :=
    (CoeffPair.toMax 2).symm.surjective.denseRange.comp
      ((scalarInclusion_denseRange (p := 2) (by simp)).prodMap
        (scalarInclusion_denseRange (p := 2) (by simp))) (CoeffPair.toMax 2).symm.continuous
  have h : sourcePeriodicH1L2Class = sourcePhysicalL2 ∘ sobolevSourceInclusion :=
    funext sourcePeriodicH1L2Class_eq_sourcePhysical
  rw [h]
  exact sourcePhysicalL2_bijective.surjective.denseRange.comp hd sourcePhysicalL2.continuous

end NLS.ZakharovShabat
