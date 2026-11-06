import NLS.ComplexAnalysis.SourceLemmaE2

/-! # Appendix B, Lemma 14: the real-slice identity principle

The real slice must be nonempty to start analytic continuation. This
condition is explicit in the source proof and is required in the statement:
a nonempty connected complex domain need not meet its real form.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma14 {R E : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : RealComplexification R E) (U : Set E) (hU : IsOpen U) (hc : IsConnected U)
    (hr : (U ∩ c.realLocus).Nonempty) (f : E → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hz : EqOn f 0 (U ∩ c.realLocus)) : EqOn f 0 U :=
  sourceLemmaE2 c U hU hc hr f hf hz

theorem lemma14_of_real_point {R E : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R] [CompleteSpace R]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (c : RealComplexification R E) (U : Set E) (hU : IsOpen U) (hc : IsConnected U)
    (x : R) (hx : c.equiv (x,0) ∈ U) (f : E → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hz : EqOn f 0 (U ∩ c.realLocus)) : EqOn f 0 U :=
  sourceLemmaE2_of_real_point c U hU hc x hx f hf hz

theorem lemma14_real_slice_hypothesis_needed :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧
      AnalyticOnNhd ℂ (fun _ : ℂ => (1:ℂ)) U ∧
      EqOn (fun _ : ℂ => (1:ℂ)) 0 (U ∩ scalarRealComplexification.realLocus) ∧
      ¬ EqOn (fun _ : ℂ => (1:ℂ)) 0 U :=
  sourceLemmaE2_realSlice_condition_needed

end NLS.Articles.MKdVNLSHierarchies
