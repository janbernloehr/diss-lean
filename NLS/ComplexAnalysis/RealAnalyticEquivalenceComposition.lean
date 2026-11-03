import NLS.ComplexAnalysis.RealAnalyticNativeInverseNeighborhoods

/-! # Actual derivatives after a bounded real source equivalence -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {A B C : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

theorem fderiv_real_comp_equiv_zero (f : B → C) (e : A ≃L[ℝ] B) (L : B ≃L[ℝ] C)
    (ha : AnalyticAt ℝ f 0) (hd : fderiv ℝ f 0 = L.toContinuousLinearMap) :
    fderiv ℝ (fun a => f (e a)) 0 = (e.trans L).toContinuousLinearMap := by
  have hf := ha.differentiableAt.hasFDerivAt
  rw [hd] at hf
  have he : HasFDerivAt f L.toContinuousLinearMap (e 0) := by simpa only [map_zero] using hf
  exact (he.comp (0 : A) e.toContinuousLinearMap.hasFDerivAt).fderiv

end NLS.ComplexAnalysis
