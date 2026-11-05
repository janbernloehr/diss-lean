import NLS.KdV.HillL2AnnularRadicandComparison
import NLS.KdV.HillL2AnnularSeparation
import NLS.ComplexAnalysis.AnnulusDerivativeBounds
import NLS.ComplexAnalysis.LogDerivativeComparison

/-! # Quadratic equal-mean logarithmic derivative control on all energy circles -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillL2Radicand_same_mean_logDeriv_bound (u v : Coeff 2)
    (hmean : u 0 = v 0) (hv : ‖v‖ ≤ ‖u‖) (hu : ‖u‖ ≤ 1) (hs : 4*Real.exp 1*‖u‖ ≤ 1)
    (k : ℕ+) (E : ℂ) (hE : E ∈ sphere (freeHillEnergy k) (k : ℝ))
    (b : ℝ) (hb : 0 < b)
    (huB : b ≤ ‖hillL2Radicand (Coeff.periodDouble u) E‖)
    (hvB : b ≤ ‖hillL2Radicand (Coeff.periodDouble v) E‖) :
    ‖logDeriv (hillL2Radicand (Coeff.periodDouble u)) E-
      logDeriv (hillL2Radicand (Coeff.periodDouble v)) E‖ ≤
      (4*(32*(Real.exp 1)^3*(4*Real.exp 1+16*(Real.exp 1)^2))/b+
        4*((2*Real.exp 1+8*(Real.exp 1)^2)^2+4)*
          (32*(Real.exp 1)^3*(4*Real.exp 1+16*(Real.exp 1)^2))/b^2)*‖u‖^2/(k : ℝ)^3 := by
  let A := 32*(Real.exp 1)^3*(4*Real.exp 1+16*(Real.exp 1)^2)
  let B := (2*Real.exp 1+8*(Real.exp 1)^2)^2+4
  let f := hillL2Radicand (Coeff.periodDouble u)
  let g := hillL2Radicand (Coeff.periodDouble v)
  have hf : Differentiable ℂ f := fun w => (analyticOnNhd_hillL2Radicand _ w (mem_univ _)).differentiableAt
  have hg : Differentiable ℂ g := fun w => (analyticOnNhd_hillL2Radicand _ w (mem_univ _)).differentiableAt
  have hk : (0 : ℝ) < k := by positivity
  have hdiff (w : ℂ) (hlo : (k : ℝ)/2 ≤ ‖w-freeHillEnergy k‖)
      (hhi : ‖w-freeHillEnergy k‖ ≤ 2*(k : ℝ)) : ‖f w-g w‖ ≤ A*‖u‖^2/(k : ℝ)^2 :=
    hillL2Radicand_same_mean_annulus_bound u v hmean hv hu hs k w hlo hhi
  have hder := norm_deriv_le_of_annulus_bound (hf.sub hg) (freeHillEnergy k) hk _ hdiff hE
  rw [deriv_sub hf.differentiableAt hg.differentiableAt] at hder
  have hgder := norm_deriv_le_of_annulus_bound hg (freeHillEnergy k) hk B
    (hillL2Radicand_annulus_bound v (hv.trans hu)
      ((mul_le_mul_of_nonneg_left hv (by positivity)).trans hs) k) hE
  have hdist := mem_sphere_iff_norm.mp hE
  have hlo : (k : ℝ)/2 ≤ ‖E-freeHillEnergy k‖ := by rw [hdist]; linarith
  have hhi : ‖E-freeHillEnergy k‖ ≤ 2*(k : ℝ) := by rw [hdist]; linarith
  apply (norm_logDeriv_sub_le E hb huB hvB (hdiff E hlo hhi) hder hgder).trans_eq
  dsimp only [A,B]
  field_simp

end NLS.KdV
