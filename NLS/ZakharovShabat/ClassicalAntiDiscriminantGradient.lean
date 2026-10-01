import NLS.ZakharovShabat.ClassicalSeparatedGradient

/-! # The actual physical anti-discriminant potential gradient

The original anti-discriminant is the sum of the two off-diagonal
monodromy entries. Each is an actual linear endpoint functional, so
their proved endpoint gradients add to its unconjugated physical
potential gradient, with the original sum and component signs.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The physical gradient of the literal off-diagonal monodromy sum. -/
def classicalAntiDiscriminantGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) (s : ℝ) : ℂ × ℂ :=
  classicalEndpointGradient Φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s+
    classicalEndpointGradient Φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s

theorem continuous_classicalAntiDiscriminantGradient (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    Continuous (classicalAntiDiscriminantGradient Φ z) :=
  (continuous_classicalEndpointGradient _ _ _ _).add (continuous_classicalEndpointGradient _ _ _ _)

/-- The actual Frechet derivative of the anti-discriminant is its
constructed physical gradient integral in every continuous direction. -/
theorem fderiv_classicalAntiDiscriminant_eq_gradient_integral
    (Φ H : Curve (ℂ × ℂ)) (z : ℂ) :
    (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) => classicalAntiDiscriminant Ψ z) Φ) H =
      ∫ s in (0 : ℝ)..1, (classicalAntiDiscriminantGradient Φ z s).1*(extend H s).1+
        (classicalAntiDiscriminantGradient Φ z s).2*(extend H s).2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hs (v : ℂ × ℂ) : DifferentiableAt ℂ
      (fun Ψ : Curve (ℂ × ℂ) => classicalSolution Ψ z v t) Φ :=
    ((analyticOnNhd_classicalSolution_joint v t (z,Φ) (mem_univ _)).comp
      (f := fun Ψ : Curve (ℂ × ℂ) => (z,Ψ)) (analyticAt_const.prod analyticAt_id)).differentiableAt
  change (fderiv ℂ (fun Ψ : Curve (ℂ × ℂ) =>
    ContinuousLinearMap.fst ℂ ℂ ℂ (classicalSolution Ψ z (0,1) 1)+
      ContinuousLinearMap.snd ℂ ℂ ℂ (classicalSolution Ψ z (1,0) 1)) Φ) H = _
  have hF : DifferentiableAt ℂ (fun Ψ : Curve (ℂ × ℂ) =>
      ContinuousLinearMap.fst ℂ ℂ ℂ (classicalSolution Ψ z (0,1) 1)) Φ := by
    simpa only [ContinuousLinearMap.coe_fst'] using! (hs (0,1)).fst
  have hG : DifferentiableAt ℂ (fun Ψ : Curve (ℂ × ℂ) =>
      ContinuousLinearMap.snd ℂ ℂ ℂ (classicalSolution Ψ z (1,0) 1)) Φ := by
    simpa only [ContinuousLinearMap.coe_snd'] using! (hs (1,0)).snd
  rw [fderiv_fun_add hF hG,add_apply,
    fderiv_classicalEndpoint_eq_gradient_integral Φ H z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ),
    fderiv_classicalEndpoint_eq_gradient_integral Φ H z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)]
  have hA := continuous_classicalEndpointGradient Φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ)
  have hB := continuous_classicalEndpointGradient Φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hH := continuous_extend H
  have hiA : IntervalIntegrable (fun s : ℝ =>
      (classicalEndpointGradient Φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).1*(extend H s).1+
        (classicalEndpointGradient Φ z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s).2*(extend H s).2) volume 0 1 :=
    ((hA.fst.mul hH.fst).add (hA.snd.mul hH.snd)).intervalIntegrable 0 1
  have hiB : IntervalIntegrable (fun s : ℝ =>
      (classicalEndpointGradient Φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s).1*(extend H s).1+
        (classicalEndpointGradient Φ z (1,0) (ContinuousLinearMap.snd ℂ ℂ ℂ) s).2*(extend H s).2) volume 0 1 :=
    ((hB.fst.mul hH.fst).add (hB.snd.mul hH.snd)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_add hiA hiB]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [classicalAntiDiscriminantGradient,Prod.fst_add,Prod.snd_add]
  ring

end NLS.ZakharovShabat
