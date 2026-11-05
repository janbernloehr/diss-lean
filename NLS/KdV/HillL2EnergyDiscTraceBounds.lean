import NLS.KdV.HillL2AnnularRadicandComparison
import NLS.ComplexAnalysis.DiscBounds

/-! # Uniform actual trace and derivative bounds on positive energy discs -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2Discriminant_freeEnergy_disc_bound (u : Coeff 2)
    (hu : ‖u‖ ≤ 1) (hs : 4*Real.exp 1*‖u‖ ≤ 1) (k : ℕ+)
    (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (2*(k : ℝ))) :
    ‖hillL2Discriminant (Coeff.periodDouble u) E‖ ≤ (2*Real.exp 1+8*(Real.exp 1)^2)^2+9 := by
  let B := (2*Real.exp 1+8*(Real.exp 1)^2)^2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hf : Differentiable ℂ (hillL2Discriminant (Coeff.periodDouble u)) :=
    fun w => (analyticOnNhd_hillL2Discriminant _ w (mem_univ _)).differentiableAt
  apply norm_le_of_sphere_bound hf (freeHillEnergy k) (by positivity : (0 : ℝ) < 2*(k : ℝ)) (B+9) _
    (mem_closedBall_iff_norm.mp hE)
  intro w hw
  have hdist := mem_sphere_iff_norm.mp hw
  have hrad := hillL2Radicand_annulus_bound u hu hs k w
    (by rw [hdist]; linarith [show (0 : ℝ) < k by positivity]) (by rw [hdist])
  have ht := norm_add_le (hillL2Radicand (Coeff.periodDouble u) w) (4 : ℂ)
  rw [show hillL2Radicand (Coeff.periodDouble u) w+4 = hillL2Discriminant (Coeff.periodDouble u) w^2 by
    simp only [hillL2Radicand]; ring,norm_pow,norm_ofNat] at ht
  change ‖hillL2Radicand (Coeff.periodDouble u) w‖ ≤ B+4 at hrad
  nlinarith [norm_nonneg (hillL2Discriminant (Coeff.periodDouble u) w)]

theorem hillL2Discriminant_freeEnergy_derivative_bound (u : Coeff 2)
    (hu : ‖u‖ ≤ 1) (hs : 4*Real.exp 1*‖u‖ ≤ 1) (k : ℕ+)
    (E : ℂ) (hE : E ∈ closedBall (freeHillEnergy k) (k : ℝ)) :
    ‖deriv (hillL2Discriminant (Coeff.periodDouble u)) E‖ ≤
      ((2*Real.exp 1+8*(Real.exp 1)^2)^2+9)/(k : ℝ) := by
  have hf : Differentiable ℂ (hillL2Discriminant (Coeff.periodDouble u)) :=
    fun w => (analyticOnNhd_hillL2Discriminant _ w (mem_univ _)).differentiableAt
  have h := norm_deriv_le_of_closedDisc_bound hf (freeHillEnergy k)
    (by linarith [show (0 : ℝ) < k by positivity] : (k : ℝ) < 2*(k : ℝ)) _
    (fun w hw => hillL2Discriminant_freeEnergy_disc_bound u hu hs k w (mem_closedBall_iff_norm.mpr hw))
    (mem_closedBall_iff_norm.mp hE)
  simpa only [two_mul,add_sub_cancel_right] using h

end NLS.KdV
