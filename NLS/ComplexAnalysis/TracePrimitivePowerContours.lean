import NLS.ComplexAnalysis.TracePrimitiveMomentDifferential

/-! # Source derivatives of powers of the actual trace primitive

The contour is fixed in energy. Only a neighborhood of its boundary is
needed; branch points in the enclosed disc impose no extra hypothesis.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology

namespace NLS.ComplexAnalysis.TracePrimitiveFamily
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]
    (f : NLS.ComplexAnalysis.TracePrimitiveFamily A)

def primitivePowerContour (c : ℂ) (r : ℝ) (m : ℕ) (q : A) : ℂ :=
  ∮ z in C(c,r), f.primitive (z,q)^m

theorem exists_analytic_primitivePowerContour (c : ℂ) (r : ℝ) (hr : 0≤r) (q : A)
    (hc : ∀ z∈sphere c r, (z,q)∈f.continuationDomain) :
    ∃ V : Set A, IsOpen V ∧ q∈V ∧
      ∀ m : ℕ, AnalyticOnNhd ℂ (f.primitivePowerContour c r m) V := by
  obtain ⟨V,hV,hqV,hsub⟩ := f.exists_continuation_neighborhood (sphere c r)
    (isCompact_sphere _ _) q hc
  refine ⟨V,hV,hqV,fun m => ?_⟩
  exact analyticOnNhd_circleIntegral_of_jointAnalytic
    (fun t => f.primitive t^m) f.isOpen_continuationDomain
    (fun t ht => (f.analytic_primitive t ht).pow m) c r hr hV
    (fun a ha z hz => hsub ⟨hz,ha⟩)

/-- Differentiating a primitive power contributes its literal degree and
the inverse canonical root. This fixes the coefficient in the quartic
energy variation before any Hamiltonian or frequency identification. -/
theorem fderiv_primitivePowerContour_apply
    (c : ℂ) (r : ℝ) (hr : 0≤r) (m : ℕ) (q h : A)
    (hc : ∀ z∈sphere c r, (z,q)∈f.continuationDomain) :
    (fderiv ℂ (f.primitivePowerContour c r m) q) h =
      ∮ z in C(c,r), (m : ℂ)*f.primitive (z,q)^(m-1)*(f.root (z,q))⁻¹*
        ((fderiv ℂ (fun p : A => f.trace (z,p)) q) h) := by
  let F : ℂ × A → ℂ := fun t => f.primitive t^m
  have hF : AnalyticOnNhd ℂ F f.continuationDomain :=
    fun t ht => (f.analytic_primitive t ht).pow m
  obtain ⟨V,hV,hqV,M,_,hbound⟩ := exists_uniform_joint_fderiv_bound_on_circle
    F f.continuationDomain f.isOpen_continuationDomain hF c r q hc
  have hdom (b : A) (hb : b∈V) (θ : ℝ) : (circleMap c r θ,b)∈f.continuationDomain :=
    (hbound _ (circleMap_mem_sphere c hr θ) b hb).1
  have hbd (b : A) (hb : b∈V) (θ : ℝ) : ‖fderiv ℂ F (circleMap c r θ,b)‖≤M :=
    (hbound _ (circleMap_mem_sphere c hr θ) b hb).2
  change (fderiv ℂ (fun p : A => ∮ z in C(c,r), F (z,p)) q) h = _
  rw [fderiv_circleIntegral_apply_of_jointAnalytic F f.continuationDomain
    f.isOpen_continuationDomain hF c r hr V hV q hqV M hdom hbd h]
  apply circleIntegral.integral_congr hr
  intro z hz
  have hP : DifferentiableAt ℂ (fun p : A => f.primitive (z,p)) q :=
    ((f.analytic_primitive (z,q) (hc z hz)).comp
      (f := fun p : A => (z,p)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  change (fderiv ℂ (fun p : A => f.primitive (z,p)^m) q) h = _
  rw [(hP.hasFDerivAt.pow m).fderiv]
  simp only [smul_apply,smul_eq_mul,nsmul_eq_mul]
  rw [fderiv_primitive_potential_apply f z q h (hc z hz)]
  ring

end NLS.ComplexAnalysis.TracePrimitiveFamily
