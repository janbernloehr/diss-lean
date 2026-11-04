import NLS.ComplexAnalysis.ParametricCircleIntegralHigher

/-! # Vanishing parameter variation of analytic contour integrals

Compactness of the actual circle supplies a uniform analytic neighborhood
and derivative bound. Pointwise parameter stationarity therefore passes to
the literal circle integral without a presumed differentiation rule.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem fderiv_circleIntegral_apply_eq_zero_of_jointAnalytic
    (F : ℂ × A → ℂ) (D : Set (ℂ × A))
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D)
    (c : ℂ) (r : ℝ) (hr : 0≤r) (a h : A)
    (hcircle : ∀ z ∈ sphere c r, (z,a)∈D)
    (hzero : ∀ z ∈ sphere c r, (fderiv ℂ (fun p : A => F (z,p)) a) h=0) :
    (fderiv ℂ (fun p : A => ∮ z in C(c,r),F (z,p)) a) h=0 := by
  obtain ⟨W,hW,haW,M,_,hb⟩ :=
    exists_uniform_joint_fderiv_bound_on_circle F D hD hF c r a hcircle
  have hdom (p : A) (hp : p∈W) (θ : ℝ) : (circleMap c r θ,p)∈D :=
    (hb _ (circleMap_mem_sphere c hr θ) p hp).1
  have hbound (p : A) (hp : p∈W) (θ : ℝ) :
      ‖fderiv ℂ F (circleMap c r θ,p)‖≤M :=
    (hb _ (circleMap_mem_sphere c hr θ) p hp).2
  rw [fderiv_circleIntegral_apply_of_jointAnalytic F D hD hF c r hr W hW a haW M hdom hbound h]
  calc
    _ = ∮ z in C(c,r),(0 : ℂ) := by
      apply circleIntegral.integral_congr hr
      intro z hz
      exact hzero z hz
    _ = 0 := by simp [circleIntegral]

end NLS.ComplexAnalysis
