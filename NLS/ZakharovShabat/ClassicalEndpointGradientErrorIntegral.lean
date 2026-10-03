import NLS.ZakharovShabat.ClassicalEndpointGradientRemainder

/-! # The gradient error represents the actual difference of potential derivatives -/

noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The error integrates to the actual endpoint derivative minus its free reference derivative. -/
theorem fderiv_classicalEndpoint_sub_free_eq_gradient_error_integral
    (φ H : Curve (ℂ × ℂ)) (z w : ℂ) (v : ℂ × ℂ) (L : (ℂ × ℂ) →L[ℂ] ℂ) :
    (fderiv ℂ (fun ψ : Curve (ℂ × ℂ) => L (classicalSolution ψ z v 1)) φ) H-
      (fderiv ℂ (fun ψ : Curve (ℂ × ℂ) => L (classicalSolution ψ w v 1)) 0) H =
      ∫ t in (0 : ℝ)..1,
        (classicalEndpointGradientRemainder φ z w v L t).1*(extend H t).1+
        (classicalEndpointGradientRemainder φ z w v L t).2*(extend H t).2 := by
  rw [fderiv_classicalEndpoint_eq_gradient_integral,fderiv_classicalEndpoint_eq_gradient_integral]
  have hφ := continuous_classicalEndpointGradient φ z v L
  have h0 := continuous_classicalEndpointGradient 0 w v L
  have hH := continuous_extend H
  have hiφ : IntervalIntegrable (fun t => (classicalEndpointGradient φ z v L t).1*(extend H t).1+
      (classicalEndpointGradient φ z v L t).2*(extend H t).2) volume 0 1 :=
    ((hφ.fst.mul hH.fst).add (hφ.snd.mul hH.snd)).intervalIntegrable 0 1
  have hi0 : IntervalIntegrable (fun t => (classicalEndpointGradient 0 w v L t).1*(extend H t).1+
      (classicalEndpointGradient 0 w v L t).2*(extend H t).2) volume 0 1 :=
    ((h0.fst.mul hH.fst).add (h0.snd.mul hH.snd)).intervalIntegrable 0 1
  rw [← intervalIntegral.integral_sub hiφ hi0]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  dsimp only
  rw [classicalEndpointGradient_free w v L ⟨t,ht'⟩]
  simp only [classicalEndpointGradientRemainder,Prod.fst_sub,Prod.snd_sub]
  ring

/-- The diagonal free monodromy entry has zero first potential gradient. -/
theorem classicalFreeEndpointGradient_fst_first (z : ℂ) (s : ℝ) :
    classicalFreeEndpointGradient z (1,0) (ContinuousLinearMap.fst ℂ ℂ ℂ) s = 0 := by
  simp [classicalFreeEndpointGradient,endpointGradientPolynomial,classicalFreeEndpointGradientData,
    classicalFreeVector]

/-- The upper off-diagonal free gradient, in the original unconjugated potential convention. -/
theorem classicalFreeEndpointGradient_fst_second (z : ℂ) (s : ℝ) :
    classicalFreeEndpointGradient z (0,1) (ContinuousLinearMap.fst ℂ ℂ ℂ) s =
      (I*exp (-I*z)*(exp (I*z*s))^2,0) := by
  simp only [classicalFreeEndpointGradient,endpointGradientPolynomial,classicalFreeEndpointGradientData]
  change (I*((classicalFreeVector z (1,0) 1).1*(classicalFreeVector z (0,1) s).2-
      (classicalFreeVector z (0,1) 1).1*(classicalFreeVector z (1,0) s).2)*(classicalFreeVector z (0,1) s).2,
    I*((classicalFreeVector z (1,0) 1).1*(classicalFreeVector z (0,1) s).1-
      (classicalFreeVector z (0,1) 1).1*(classicalFreeVector z (1,0) s).1)*(classicalFreeVector z (0,1) s).1) = _
  simp [classicalFreeVector,pow_two,mul_assoc]

end NLS.ZakharovShabat
