import NLS.ZakharovShabat.SourceHigherSobolevFiniteGapDensity
import NLS.ZakharovShabat.SourceHolomorphicRealGerm

/-! # Analytic uniqueness on every integer Sobolev real form

The coefficient-preserving normalized coordinates transfer real-form analytic
uniqueness to the original Hˢ topology, for Banach-valued maps.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat
variable (s : ℕ)

/-- Analytic Hˢ maps agreeing on all real sources have identical complex germs. -/
theorem eventuallyEq_higherSobolev_of_analyticAt_of_real_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (a : realTypeHigherSobolevSourceLocus s) (f g : (SobolevSource s) → F)
    (hf : AnalyticAt ℂ f a.val) (hg : AnalyticAt ℂ g a.val)
    (hreal : ∀ b : realTypeHigherSobolevSourceLocus s, f b.val = g b.val) :
    f =ᶠ[𝓝 a.val] g := by
  let E := higherSobolevNormalizedCoordinates s
  let φ : realTypeSourceLocus 2 :=
    ⟨E a.val,(higherSobolevNormalizedCoordinates_realType_iff s a.val).mpr a.property⟩
  have hf' : AnalyticAt ℂ (f ∘ E.symm) φ.val := by
    apply AnalyticAt.comp (x := φ.val) (f := E.symm)
    · simpa only [φ,ContinuousLinearEquiv.symm_apply_apply] using hf
    · exact E.symm.analyticAt _
  have hg' : AnalyticAt ℂ (g ∘ E.symm) φ.val := by
    apply AnalyticAt.comp (x := φ.val) (f := E.symm)
    · simpa only [φ,ContinuousLinearEquiv.symm_apply_apply] using hg
    · exact E.symm.analyticAt _
  have he := eventuallyEq_source_of_analyticAt_of_real_agreement (by simp) φ
    (f ∘ E.symm) (g ∘ E.symm) hf' hg' (fun ψ => by
      have hr : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s (E.symm ψ.val))) :=
        (higherSobolevNormalizedCoordinates_realType_iff s _).mp (by
          change IsRealType (CoeffPair.toMax 2 (E (E.symm ψ.val)))
          rw [E.apply_symm_apply]
          exact ψ.property)
      exact hreal ⟨E.symm ψ.val,hr⟩)
  have ht : Tendsto E (𝓝 a.val) (𝓝 φ.val) := E.continuous.continuousAt.tendsto
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using he.comp_tendsto ht

end NLS.ZakharovShabat
