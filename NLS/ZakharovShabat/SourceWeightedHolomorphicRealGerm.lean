import NLS.ZakharovShabat.SourceWeightedRealSpaces
import NLS.ZakharovShabat.SourceHolomorphicRealGerm

/-! # Complex weighted source germs determined by the original real form -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Transport source real-form uniqueness through an arbitrary complex Banach
coordinate equivalence. Keeping this transport abstract avoids unfolding the
concrete weighted normalization in the analytic identity proof. -/
theorem eventuallyEq_of_source_real_coordinates
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hp : p ≠ ⊤) (E : V ≃L[ℂ] CoeffPair p) (a : V)
    (ha : E a ∈ realTypeSourceSubmodule p) (f g : V → F)
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a)
    (hreal : ∀ ψ : realTypeSourceSubmodule p, f (E.symm ψ.val) = g (E.symm ψ.val)) :
    f =ᶠ[𝓝 a] g := by
  let φ : realTypeSourceSubmodule p := ⟨E a,ha⟩
  have hf' : AnalyticAt ℂ (f ∘ E.symm) φ.val := by
    apply AnalyticAt.comp (f := E.symm) (x := φ.val)
    · simpa only [φ,ContinuousLinearEquiv.symm_apply_apply] using hf
    · exact E.symm.analyticAt _
  have hg' : AnalyticAt ℂ (g ∘ E.symm) φ.val := by
    apply AnalyticAt.comp (f := E.symm) (x := φ.val)
    · simpa only [φ,ContinuousLinearEquiv.symm_apply_apply] using hg
    · exact E.symm.analyticAt _
  have he := eventuallyEq_source_of_analyticAt_of_real_agreement hp φ
    (f ∘ E.symm) (g ∘ E.symm) hf' hg' hreal
  have ht : Tendsto E (𝓝 a) (𝓝 φ.val) := E.continuous.continuousAt.tendsto
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using he.comp_tendsto ht

private theorem normalized_source_real_mem (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (sourcePairWeightCoordinates (p := p) w).toContinuousLinearEquiv a.val ∈ realTypeSourceSubmodule p :=
  (weightedRealSourceEquiv w a).property

private theorem normalized_source_inverse_real (w : SpectralWeight)
    (ψ : realTypeSourceSubmodule p) :
    (sourcePairWeightCoordinates (p := p) w).toContinuousLinearEquiv.symm ψ.val =
      ((weightedRealSourceEquiv w).symm ψ).val := rfl

/-- Normalization transports real-form analytic uniqueness to every original
weighted source, without changing its raw real subspace. -/
theorem eventuallyEq_weightedSource_of_analyticAt_of_real_agreement
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hp : p ≠ ⊤) (w : SpectralWeight) (a : weightedRealSourceSubmodule (p := p) w)
    (f g : WeightedCoeffPair (sourceFrequencyWeight w) p → F)
    (hf : AnalyticAt ℂ f a.val) (hg : AnalyticAt ℂ g a.val)
    (hreal : ∀ b : weightedRealSourceSubmodule (p := p) w, f b.val = g b.val) :
    f =ᶠ[𝓝 a.val] g := by
  let E := (sourcePairWeightCoordinates (p := p) w).toContinuousLinearEquiv
  apply eventuallyEq_of_source_real_coordinates hp E a.val (normalized_source_real_mem w a) f g hf hg
  intro ψ
  rw [normalized_source_inverse_real]
  exact hreal ((weightedRealSourceEquiv w).symm ψ)

/-- The original weighted real form determines an entire complex cotangent.
Agreement is required on all real directions, not just on one coordinate slice. -/
theorem weightedSourceCLM_ext_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (hp : p ≠ ⊤) (w : SpectralWeight)
    (L M : WeightedCoeffPair (sourceFrequencyWeight w) p →L[ℂ] F)
    (hreal : ∀ b : weightedRealSourceSubmodule (p := p) w, L b.val = M b.val) : L = M := by
  have he := (eventuallyEq_weightedSource_of_analyticAt_of_real_agreement hp w 0 L M
    (L.analyticAt _) (M.analyticAt _) hreal).fderiv_eq (𝕜 := ℂ)
  simpa only [ContinuousLinearMap.fderiv] using he

end NLS.ZakharovShabat
