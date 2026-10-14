import NLS.ZakharovShabat.SourceSimpleSpectralDomain
import NLS.ZakharovShabat.SourceLemma8_5
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-! # The full critical displacement is analytic on the retained domain

Analyticity of every actual coordinate and the locally uniform original
ℓᵖ norm bound assemble into Banach-space analyticity. This permits the
critical sequence to be substituted into the deleted product jointly.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire ℓᵖ displacement map is analytic, including at non-real sources. -/
theorem SourceSimpleSpectralDomainData.criticalDisplacement_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSimpleSpectralDomainData hp hp1 W) (hW : IsOpen W) :
    AnalyticOnNhd ℂ (sourceCriticalDisplacement hp hp1) W := by
  intro φ hφ
  obtain ⟨U,hU,_,hφU,_,R,_,hbound⟩ := sourceLemma8_5 hp hp1 φ
  have hcoord (n : ℤ) : AnalyticOnNhd ℂ
      (fun ψ : CoeffPair p => sourceCriticalDisplacement hp hp1 ψ n) (U ∩ W) := by
    intro ψ hψ
    simpa only [sourceCriticalDisplacement,canonicalCriticalDisplacement_apply] using!
      (H.critical ψ hψ.2 n).1.sub analyticAt_const
  exact Coeff.analyticOnNhd_of_bounded_coordinatewise (sourceCriticalDisplacement hp hp1)
    (hU.inter hW) hcoord R (fun ψ hψ => (hbound ψ hψ.1).1) φ ⟨hφU,hφ⟩

end NLS.ZakharovShabat
