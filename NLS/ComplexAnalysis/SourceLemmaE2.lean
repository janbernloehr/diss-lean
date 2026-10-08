import NLS.ComplexAnalysis.RealComplexification

/-! # Lemma E.2: identity from the real slice of a complexification

The source's neighborhood is taken to meet the included real space, as
its proof and applications require. Mere nonemptiness of the complex
domain cannot replace this condition. Connectedness suffices; no
convexity or projection norm bound is imposed.
-/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

variable {R E F : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- E.2 for any continuous complexification and any complete complex target.
The nonempty real slice is the point needed to initiate the source proof. -/
theorem sourceLemmaE2 (c : RealComplexification R E) (U : Set E)
    (hU : IsOpen U) (hconn : IsConnected U) (hreal : (U ∩ c.realLocus).Nonempty)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U) (hzero : EqOn f 0 (U ∩ c.realLocus)) :
    EqOn f 0 U :=
  AnalyticOnNhd.eqOn_zero_of_continuous_real_form c.realLocus
    (fun {_ _} hx hy => c.add_mem hx hy) (fun t {_} hx => c.real_smul_mem t hx) c.re c.im c.re_mem c.im_mem c.decomp
    c.continuous_re.continuousAt c.re_zero c.continuous_im.continuousAt c.im_zero
    U hU hconn.isPreconnected hreal f hf (fun _ hx hr => hzero ⟨hx,hr⟩)

/-- The neighborhood formulation based at a specified real point. -/
theorem sourceLemmaE2_of_real_point (c : RealComplexification R E) (U : Set E)
    (hU : IsOpen U) (hconn : IsConnected U) (x : R) (hx : c.equiv (x,0) ∈ U)
    (f : E → F) (hf : AnalyticOnNhd ℂ f U) (hzero : EqOn f 0 (U ∩ c.realLocus)) :
    EqOn f 0 U :=
  sourceLemmaE2 c U hU hconn ⟨c.equiv (x,0),hx,⟨x,rfl⟩⟩ f hf hzero

/-- Agreement of two analytic functions on the real slice gives agreement on the whole domain. -/
theorem sourceLemmaE2_eq (c : RealComplexification R E) (U : Set E)
    (hU : IsOpen U) (hconn : IsConnected U) (hreal : (U ∩ c.realLocus).Nonempty)
    (f g : E → F) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (he : EqOn f g (U ∩ c.realLocus)) : EqOn f g U := by
  have hz : EqOn (f-g) 0 U := sourceLemmaE2 c U hU hconn hreal (f-g) (hf.sub hg)
    (fun x hx => sub_eq_zero.mpr (he hx))
  intro x hx
  exact sub_eq_zero.mp (hz hx)

/-- Without a real point, even a nonempty open connected complex neighborhood is insufficient.
The constant one on the half-unit ball about i vanishes on its empty real slice. -/
theorem sourceLemmaE2_realSlice_condition_needed :
    ∃ U : Set ℂ, IsOpen U ∧ IsConnected U ∧
      AnalyticOnNhd ℂ (fun _ : ℂ => (1:ℂ)) U ∧
      EqOn (fun _ : ℂ => (1:ℂ)) 0 (U ∩ scalarRealComplexification.realLocus) ∧
      ¬ EqOn (fun _ : ℂ => (1:ℂ)) 0 U := by
  refine ⟨ball Complex.I (1/2),isOpen_ball,isConnected_ball (by norm_num),analyticOnNhd_const,?_,?_⟩
  · intro z hz
    have him : z.im = 0 := by
      simpa only [scalarRealComplexification_realLocus,Set.mem_ofPred_eq] using hz.2
    have hnorm : ‖z-Complex.I‖ < 1/2 := by simpa only [mem_ball,dist_eq_norm] using hz.1
    have hle := Complex.abs_im_le_norm (z-Complex.I)
    simp only [sub_im,him,I_im,zero_sub,abs_neg,abs_one] at hle
    exfalso
    linarith
  · intro h
    have he := h (show Complex.I ∈ ball Complex.I (1/2) by simp)
    norm_num at he

end NLS.ComplexAnalysis
