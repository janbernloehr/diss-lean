import NLS.KdV.ClassicalHillFreeEnergyDerivative
import NLS.KdV.HillNativeTraceFirstVariation

/-! Exact entire free trace and energy derivative with the original
scalar normalization, using square descent rather than differentiating
an arbitrary square-root branch. -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusDiscriminant_free_sq (z : ℂ) :
    hillHminusDiscriminant 0 (z^2)=2*cos z := by
  rw [hillHminusDiscriminant_zero]
  rcases eq_or_eq_neg_of_sq_eq_sq (sqrt (z^2)) z (complex_sqrt_sq (z^2)) with he | he
  · rw [he]
  · rw [he,cos_neg]

theorem deriv_hillHminusDiscriminant_free_sq (z : ℂ) (hz : z ≠ 0) :
    deriv (hillHminusDiscriminant 0) (z^2) = -sin z/z := by
  have hf : DifferentiableAt ℂ (hillHminusDiscriminant 0) (z^2) :=
    ((analyticOnNhd_hillHminusDiscriminant_joint (z^2,0) (mem_univ _)).comp
      (f := fun w : ℂ => (w,(0 : PeriodOneHminusOne))) (analyticAt_id.prod analyticAt_const)).differentiableAt
  have hg : HasDerivAt (fun w : ℂ => 2*cos w) (-2*sin z) z := by
    simpa using! (Complex.hasDerivAt_cos z).const_mul 2
  have he : (fun w => hillHminusDiscriminant 0 (w^2)) =ᶠ[𝓝 z] fun w => 2*cos w :=
    Eventually.of_forall hillHminusDiscriminant_free_sq
  rw [deriv_eq_of_square_pullback _ _ z _ hz hf hg he]
  ring

theorem deriv_hillHminusDiscriminant_free_energy (μ : ℂ) (hμ : μ ≠ 0) :
    deriv (hillHminusDiscriminant 0) μ = -sin (sqrt μ)/sqrt μ := by
  have hw : sqrt μ ≠ 0 := fun he => hμ (by rw [← complex_sqrt_sq μ,he]; simp)
  have hd := deriv_hillHminusDiscriminant_free_sq (sqrt μ) hw
  simpa only [complex_sqrt_sq] using hd

end NLS.KdV
