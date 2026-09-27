import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing
import NLS.SequenceSpaces.UniformTailContinuity

/-!
# Sequence-norm continuity of periodic midpoint and gap data

The canonical periodic endpoints are continuous at every real-type
source one index at a time. Their locally uniform `ℓᵖ` tails upgrade
this to continuity of the complete midpoint and gap displacement
sequences. In particular, all source gaps can be made simultaneously
small near the free potential.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The source periodic-midpoint displacement is continuous in `ℓᵖ`
at each real-type source. -/
theorem continuousAt_sourcePeriodicMidpointDisplacement_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ContinuousAt (sourcePeriodicMidpointDisplacement hp hp1) φ := by
  apply Coeff.continuousAt_of_coordinatewise_of_uniform_tails
  · intro n
    have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      hp hp1 φ hφ n
    have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType
      hp hp1 φ hφ n
    simp only [sourcePeriodicMidpointDisplacement_apply,
      canonicalPeriodicMidpoint]
    change ContinuousAt (fun ψ : CoeffPair p =>
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n +
        canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n)/2 - (Real.pi : ℂ)*n) φ
    convert ((hL.add hR).div_const (2 : ℂ)).sub continuousAt_const using 1
    funext ψ
    rfl
  · intro ε hε
    obtain ⟨N,_,V,hVopen,hφV,R,hR,hdata⟩ :=
      exists_uniform_small_sourcePeriodicMidpointDisplacement
        hp hp1 φ hε
    refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ),V,hVopen,hφV,?_⟩
    intro ψ hψ
    exact (hdata ψ hψ).2 N le_rfl

/-- The source periodic-gap displacement is continuous in `ℓᵖ` at
each real-type source. -/
theorem continuousAt_sourcePeriodicGapDisplacement_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ContinuousAt (sourcePeriodicGapDisplacement hp hp1) φ := by
  apply Coeff.continuousAt_of_coordinatewise_of_uniform_tails
  · intro n
    have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      hp hp1 φ hφ n
    have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType
      hp hp1 φ hφ n
    simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
    change ContinuousAt (fun ψ : CoeffPair p =>
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n -
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) φ
    convert hR.sub hL using 1
    funext ψ
    rfl
  · intro ε hε
    obtain ⟨N,_,V,hVopen,hφV,R,hR,hdata⟩ :=
      exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hε
    refine ⟨Finset.Icc (-(N : ℤ)) (N : ℤ),V,hVopen,hφV,?_⟩
    intro ψ hψ
    exact (hdata ψ hψ).2 N le_rfl

end NLS.ZakharovShabat
