import NLS.ComplexAnalysis.RealComplexificationIdentity

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.Articles.KdVEstimates

/-- Appendix D.1 with the nonempty real slice used by its printed proof
made explicit. The normed-space formulation includes the Banach case. -/
theorem lemmaD1_corrected
    {R E : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E]
    (c : NLS.ComplexAnalysis.RealComplexification R E)
    (U : Set E) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hreal : (U ∩ c.realLocus).Nonempty) (f : E → ℂ)
    (hf : AnalyticOnNhd ℂ f U) (hzero : EqOn f 0 (U ∩ c.realLocus)) :
    EqOn f 0 U :=
  c.eqOn_zero_of_nonempty_real_slice U hU hconn hreal f hf hzero

/-- Nonempty connected open domains can have empty real slice. Thus D.1
cannot omit the existence of a real point: the constant function one on
the ball of radius one half about i is a counterexample to that omission. -/
theorem lemmaD1_nonempty_real_slice_is_necessary :
    ∃ (U : Set ℂ) (f : ℂ → ℂ), IsOpen U ∧ IsConnected U ∧
      U ∩ NLS.ComplexAnalysis.scalarRealComplexification.realLocus = ∅ ∧
      AnalyticOnNhd ℂ f U ∧
      EqOn f 0 (U ∩ NLS.ComplexAnalysis.scalarRealComplexification.realLocus) ∧
      ¬ EqOn f 0 U := by
  let U : Set ℂ := Metric.ball I (1/2 : ℝ)
  have hI : I ∈ U := by simp [U]
  have hempty : U ∩ NLS.ComplexAnalysis.scalarRealComplexification.realLocus = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz,hr⟩
    have him : z.im = 0 := by
      simpa only [NLS.ComplexAnalysis.scalarRealComplexification_realLocus,
        Set.mem_ofPred_eq] using hr
    have hb : ‖z-I‖ < (1/2 : ℝ) := by simpa only [U,Metric.mem_ball,dist_eq_norm] using hz
    have hi := Complex.abs_im_le_norm (z-I)
    simp only [sub_im,him,I_im,zero_sub,abs_neg,abs_one] at hi
    linarith
  refine ⟨U,fun _ => 1,Metric.isOpen_ball,(convex_ball I (1/2 : ℝ)).isConnected ⟨I,hI⟩,
    hempty,?_,?_,?_⟩
  · intro z _
    exact analyticAt_const
  · rw [hempty]
    simp
  · intro h
    have he := h hI
    norm_num at he

end NLS.Articles.KdVEstimates
