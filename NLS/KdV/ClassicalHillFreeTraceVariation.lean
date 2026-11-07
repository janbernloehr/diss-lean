import NLS.KdV.ClassicalHillFreeVariation

/-! Physical trace variation with the original scalar Hill normalization.
At the free potential it is exactly sin(z)/z times the potential mean. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra
namespace NLS.KdV

theorem fderiv_classicalHillDiscriminant_potential (q h : Curve ℂ) (μ : ℂ) :
    (fderiv ℂ (fun r => classicalHillDiscriminant r μ) q) h =
      (classicalHillPotentialVariation q h μ (1,0) 1).1+
        (classicalHillPotentialVariation q h μ (0,1) 1).2 := by
  let t : Icc (0:ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  have hd1 := (analyticOnNhd_classicalHillFlow_potential μ (1,0) t q (mem_univ _)).differentiableAt.hasFDerivAt
  have hd2 := (analyticOnNhd_classicalHillFlow_potential μ (0,1) t q (mem_univ _)).differentiableAt.hasFDerivAt
  have hfd := (hd1.fst.add hd2.snd).fderiv
  change fderiv ℂ (fun r => (classicalHillFlow r μ (1,0) t).1+
    (classicalHillFlow r μ (0,1) t).2) q = _ at hfd
  have he : (fun r => classicalHillDiscriminant r μ) = fun r =>
      (classicalHillFlow r μ (1,0) t).1+(classicalHillFlow r μ (0,1) t).2 :=
    funext (fun r => (classicalHillFlow_trace r μ).symm)
  rw [he,hfd]
  change ((fderiv ℂ (fun r => classicalHillFlow r μ (1,0) t) q) h).1+
    ((fderiv ℂ (fun r => classicalHillFlow r μ (0,1) t) q) h).2 = _
  rw [fderiv_classicalHillFlow_potential,fderiv_classicalHillFlow_potential]

theorem fderiv_classicalHillDiscriminant_free (h : Curve ℂ) (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℂ (fun q => classicalHillDiscriminant q (z^2)) 0) h =
      sin z/z * ∫ s in (0:ℝ)..1, extend h s := by
  rw [fderiv_classicalHillDiscriminant_potential]
  have h1 := (classicalHillPotentialVariation_free_sq h z hz (1,0)
    ⟨1,by constructor <;> norm_num⟩).1
  have h2 := (classicalHillPotentialVariation_free_sq h z hz (0,1)
    ⟨1,by constructor <;> norm_num⟩).2
  simp only [mul_one,mul_zero,add_zero,zero_add,Complex.ofReal_one] at h1 h2
  have hext : Continuous (extend h) := continuous_extend h
  rw [h1,h2,← intervalIntegral.integral_add,← intervalIntegral.integral_const_mul]
  · apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    have hs : sin (z*(1-(s:ℂ)))*cos (z*(s:ℂ))+
        cos (z*(1-(s:ℂ)))*sin (z*(s:ℂ)) = sin z := by
      rw [← Complex.sin_add]
      congr 1
      ring
    field_simp [hz]
    linear_combination extend h s * hs
  · exact (by fun_prop : Continuous (fun s : ℝ =>
      sin (z*(1-s))/z*extend h s*cos (z*(s:ℂ)))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun s : ℝ =>
      cos (z*(1-s))*extend h s*(sin (z*(s:ℂ))/z))).intervalIntegrable _ _

end NLS.KdV
