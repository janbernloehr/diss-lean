import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! # The derivative criterion for two-sided analytic local inverses -/
noncomputable section
open Filter Topology
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Differentiating both inverse identities gives an invertible derivative.
This supplies the invertible seed from a genuine local analytic inverse. -/
theorem isUnit_fderiv_of_localInverse
    {F G : E → E} {x : E} (hF : AnalyticAt ℂ F x) (hG : AnalyticAt ℂ G (F x))
    (hGx : G (F x) = x) (hleft : ∀ᶠ y in 𝓝 x, G (F y) = y)
    (hright : ∀ᶠ z in 𝓝 (F x), F (G z) = z) : IsUnit (fderiv ℂ F x) := by
  have hl : (G ∘ F) =ᶠ[𝓝 x] id := hleft
  have hr : (F ∘ G) =ᶠ[𝓝 (F x)] id := hright
  have hlD := hl.fderiv_eq (𝕜 := ℂ)
  have hrD := hr.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_comp x hG.differentiableAt hF.differentiableAt,fderiv_id] at hlD
  rw [fderiv_comp (F x) (by simpa only [hGx] using hF.differentiableAt)
    hG.differentiableAt,fderiv_id,hGx] at hrD
  exact ⟨⟨fderiv ℂ F x,fderiv ℂ G (F x),hrD,hlD⟩,rfl⟩

/-- Invertible derivative is equivalent to an analytic two-sided local inverse. -/
theorem isUnit_fderiv_iff_localInverse {F : E → E} {x : E} (hF : AnalyticAt ℂ F x) :
    IsUnit (fderiv ℂ F x) ↔ ∃ G : E → E, AnalyticAt ℂ G (F x) ∧ G (F x) = x ∧
      (∀ᶠ y in 𝓝 x, G (F y) = y) ∧ (∀ᶠ z in 𝓝 (F x), F (G z) = z) := by
  constructor
  · intro hu
    obtain ⟨G,hG,hGx,hl,hr,_⟩ := exists_localInverse_of_isUnit_fderiv hF hu
    exact ⟨G,hG,hGx,hl,hr⟩
  · rintro ⟨G,hG,hGx,hl,hr⟩
    exact isUnit_fderiv_of_localInverse hF hG hGx hl hr

end NLS.ComplexAnalysis
