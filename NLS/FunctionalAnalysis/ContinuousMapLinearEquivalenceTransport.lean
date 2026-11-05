import NLS.ComplexAnalysis.ContinuousMapSuperposition

/-! Analyticity in the uniform trajectory norm transports through a
continuous real linear equivalence of the target Banach spaces. -/
noncomputable section
open Set NLS.ComplexAnalysis
namespace NLS.FunctionalAnalysis
variable {K E S F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem analyticAt_superposition_of_linearEquiv (L : S ≃L[ℝ] F)
    (f : E → S) (hf : Continuous f) (a : C(K,E))
    (ha : AnalyticAt ℝ (superposition (K := K) (fun x => L (f x))) a) :
    AnalyticAt ℝ (superposition (K := K) f) a := by
  let D := L.symm.toContinuousLinearMap.compLeftContinuous ℝ K
  have hD : AnalyticAt ℝ D (superposition (fun x => L (f x)) a) := D.analyticAt _
  apply (hD.comp (f := superposition (fun x => L (f x))) ha).congr
  apply Filter.Eventually.of_forall
  intro b
  apply ContinuousMap.ext
  intro t
  change L.symm (superposition (fun x => L (f x)) b t)=superposition f b t
  calc
    _ = L.symm (L (f (b t))) := congrArg L.symm
      (superposition_apply (g := b) (U := univ) (L.continuous.comp hf).continuousOn (subset_univ _) t)
    _ = f (b t) := L.symm_apply_apply _
    _ = _ := (superposition_apply (g := b) (U := univ) hf.continuousOn (subset_univ _) t).symm

end NLS.FunctionalAnalysis
