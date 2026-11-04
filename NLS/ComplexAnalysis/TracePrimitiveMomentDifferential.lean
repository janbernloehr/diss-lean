import NLS.ComplexAnalysis.TracePrimitiveMoments

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis.TracePrimitiveFamily



variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (f : NLS.ComplexAnalysis.TracePrimitiveFamily A)

theorem fderiv_primitive_potential_apply (z : ℂ) (q h : A)
    (hz : (z,q)∈f.continuationDomain) :
    (fderiv ℂ (fun p : A => f.primitive (z,p)) q) h=
      (f.root (z,q))⁻¹*((fderiv ℂ (fun p : A => f.trace (z,p)) q) h) := by
  let T : A → ℂ × A := fun p => (z,p)
  have hT : HasFDerivAt T ((0 : A →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ A)) q :=
    (hasFDerivAt_const z q).prodMk (hasFDerivAt_id q)
  have hp := congrArg (fun L : A →L[ℂ] ℂ => L h)
    (((f.hasFDerivAt_primitive (z,q) hz).comp q hT).fderiv)
  have ht := congrArg (fun L : A →L[ℂ] ℂ => L h)
    ((((f.analytic_trace (z,q) (mem_univ _)).differentiableAt.hasFDerivAt).comp q hT).fderiv)
  change (fderiv ℂ (fun p : A => f.primitive (z,p)) q) h=
    (f.root (z,q))⁻¹*((fderiv ℂ f.trace (z,q)) (0,h)) at hp
  change (fderiv ℂ (fun p : A => f.trace (z,p)) q) h=((fderiv ℂ f.trace (z,q)) (0,h)) at ht
  exact hp.trans (congrArg (fun v : ℂ => (f.root (z,q))⁻¹*v) ht.symm)

/-- The actual normalized primitive moment has the source differential
of the discriminant contour, with its original factor -1/pi. -/
theorem fderiv_contourMoment_apply
    (c : ℂ) (r : ℝ) (hr : 0≤r) (m : ℕ) (q h : A)
    (hc : ∀ z∈sphere c r, (z,q)∈f.continuationDomain) :
    (fderiv ℂ (f.contourMoment c r m) q) h=
      -(Real.pi : ℂ)⁻¹*(∮ z in C(c,r),z^m*(f.root (z,q))⁻¹*
        ((fderiv ℂ (fun p : A => f.trace (z,p)) q) h)) := by
  let F : ℂ × A → ℂ := fun t => t.1^m*f.primitive t
  have hF : AnalyticOnNhd ℂ F f.continuationDomain := by
    intro t ht
    exact (analyticAt_fst.pow m).mul (f.analytic_primitive t ht)
  obtain ⟨V,hV,hqV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle
    F f.continuationDomain f.isOpen_continuationDomain hF c r q hc
  have hdom (b : A) (hb : b∈V) (θ : ℝ) : (circleMap c r θ,b)∈f.continuationDomain :=
    (hbound _ (circleMap_mem_sphere c hr θ) b hb).1
  have hbd (b : A) (hb : b∈V) (θ : ℝ) : ‖fderiv ℂ F (circleMap c r θ,b)‖≤M :=
    (hbound _ (circleMap_mem_sphere c hr θ) b hb).2
  have hdiff := differentiableAt_circleIntegral_of_jointAnalytic F f.continuationDomain
    f.isOpen_continuationDomain hF c r hr V hV q hqV M hdom hbd
  have hd := fderiv_circleIntegral_apply_of_jointAnalytic F f.continuationDomain
    f.isOpen_continuationDomain hF c r hr V hV q hqV M hdom hbd h
  have hmoment : (fderiv ℂ (f.contourMoment c r m) q) h=
      -(Real.pi : ℂ)⁻¹*((fderiv ℂ (fun p : A => ∮ z in C(c,r),F (z,p)) q) h) := by
    change (fderiv ℂ (fun p : A => -(Real.pi : ℂ)⁻¹*(∮ z in C(c,r),F (z,p))) q) h=_
    rw [fderiv_const_mul hdiff]
    rfl
  rw [hmoment,hd]
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  have hP : DifferentiableAt ℂ (fun p : A => f.primitive (z,p)) q :=
    ((f.analytic_primitive (z,q) (hc z hz)).comp
      (f := fun p : A => (z,p)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  change (fderiv ℂ (fun p : A => z^m*f.primitive (z,p)) q) h=_
  rw [fderiv_const_mul hP]
  simp only [smul_apply,smul_eq_mul]
  rw [fderiv_primitive_potential_apply f z q h (hc z hz)]
  ring

end NLS.ComplexAnalysis.TracePrimitiveFamily
