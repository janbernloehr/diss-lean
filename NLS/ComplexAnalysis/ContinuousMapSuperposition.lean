import NLS.ComplexAnalysis.ContinuousMapAnalytic

/-! # Analytic pointwise composition on compact function spaces

An analytic map induces an analytic map on continuous functions whose
ranges stay in its open domain. The fallback in `mkD` is irrelevant on
this open range domain; the exact pointwise formula is proved there.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ComplexAnalysis
variable {K E F : Type} [TopologicalSpace K] [CompactSpace K]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Pointwise composition, using a zero fallback only when the composite is not continuous. -/
def superposition (f : E → F) (g : C(K,E)) : C(K,F) :=
  ContinuousMap.mkD (fun k => f (g k)) 0

omit [CompactSpace K] [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace F] in
/-- The exact composition formula on every continuous image inside the domain. -/
theorem superposition_apply {f : E → F} {U : Set E} (hf : ContinuousOn f U)
    {g : C(K,E)} (hg : range g ⊆ U) (k : K) : superposition f g k = f (g k) :=
  ContinuousMap.mkD_apply_of_continuous
    (hf.comp_continuous g.continuous (fun k => hg ⟨k,rfl⟩))

omit [NormedSpace ℂ E] [NormedSpace ℂ F] [CompleteSpace F] in
/-- Compact-open continuity gives uniform-norm continuity of pointwise composition. -/
theorem continuousOn_superposition {f : E → F} {U : Set E} (hf : ContinuousOn f U) :
    ContinuousOn (superposition (K := K) f) {g : C(K,E) | range g ⊆ U} := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  exact hf.comp continuous_eval.continuousOn (fun x hx => hx.1 ⟨x.2,rfl⟩)

/-- An analytic map acts analytically on compact continuous-function spaces. -/
theorem analyticOnNhd_superposition {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U) :
    AnalyticOnNhd ℂ (superposition (K := K) f) {g : C(K,E) | range g ⊆ U} := by
  have hD : IsOpen {g : C(K,E) | range g ⊆ U} := ContinuousMap.isOpen_setOfPred_range_subset hU
  apply analyticOnNhd_continuousMap_of_eval _ hD (continuousOn_superposition hf.continuousOn)
  intro k g hg
  have ha := (hf (g k) (hg ⟨k,rfl⟩)).comp (f := fun a : C(K,E) => a k)
    ((ContinuousMap.evalCLM ℂ k).analyticAt g)
  apply ha.congr
  filter_upwards [hD.mem_nhds hg] with a ha
  exact (superposition_apply hf.continuousOn ha k).symm

/-- The derivative of composition is pointwise application of the original derivative. -/
theorem fderiv_superposition_apply {f : E → F} {U : Set E}
    (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (g v : C(K,E)) (hg : range g ⊆ U) (k : K) :
    fderiv ℂ (superposition f) g v k = fderiv ℂ f (g k) (v k) := by
  have hD : IsOpen {g : C(K,E) | range g ⊆ U} := ContinuousMap.isOpen_setOfPred_range_subset hU
  have he : (fun a : C(K,E) => superposition f a k) =ᶠ[𝓝 g] (fun a => f (a k)) := by
    filter_upwards [hD.mem_nhds hg] with a ha
    exact superposition_apply hf.continuousOn ha k
  have hl := (ContinuousMap.evalCLM ℂ k).hasFDerivAt.comp g
    (analyticOnNhd_superposition hU hf g hg).differentiableAt.hasFDerivAt
  have hr := (hf (g k) (hg ⟨k,rfl⟩)).differentiableAt.hasFDerivAt.comp g
    (ContinuousMap.evalCLM ℂ k).hasFDerivAt
  have hd := (hl.congr_of_eventuallyEq he.symm).unique hr
  exact congrArg (fun L : C(K,E) →L[ℂ] F => L v) hd

end NLS.ComplexAnalysis
