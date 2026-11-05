import NLS.KdV.ClassicalHillDirichletBorn
import NLS.ComplexAnalysis.CosineFourierIntegral

/-! # Comparing the actual Dirichlet residual to its Fourier frequency -/
noncomputable section
open Set Metric Complex MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem classicalHillDirichlet_frequency_residual_bound (q : Curve ℂ)
    (z : ℂ) (hz : z ≠ 0) (r H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
      ((∫ s in (0 : ℝ)..1,cos ((r : ℂ)*((2*s-1 : ℝ) : ℂ))*NLS.LinearVolterra.extend q s)-
        cos z*(∫ s in (0 : ℝ)..1,NLS.LinearVolterra.extend q s))‖ ≤
      4*(Real.exp H)^3*(classicalHillPotentialMass q)^2/‖z‖+
        Real.exp ‖z-r‖*‖z-r‖*classicalHillPotentialMass q := by
  let Q := NLS.LinearVolterra.extend q
  let L := fun w : ℂ => ∫ s in (0 : ℝ)..1,cos (w*((2*s-1 : ℝ) : ℂ))*Q s
  have hc (w : ℂ) : Continuous (fun s : ℝ => cos (w*((2*s-1 : ℝ) : ℂ))*Q s) := by
    have ht : Continuous (fun s : ℝ => cos (w*((2*s-1 : ℝ) : ℂ))) := by fun_prop
    exact ht.mul (continuous_extend q)
  have hsplit : (∫ s in (0 : ℝ)..1,(cos (z*((2*s-1 : ℝ) : ℂ))-cos z)*Q s) =
      L z-cos z*(∫ s in (0 : ℝ)..1,Q s) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (f := fun s => cos (z*((2*s-1 : ℝ) : ℂ))*Q s)
        (g := fun s => cos z*Q s) ((hc z).intervalIntegrable 0 1)
        ((continuous_const.mul (continuous_extend q)).intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have hdiff : L z-L r = ∫ s in (0 : ℝ)..1,
      (cos (z*((2*s-1 : ℝ) : ℂ))-cos ((r : ℂ)*((2*s-1 : ℝ) : ℂ)))*Q s := by
    rw [← intervalIntegral.integral_sub (f := fun s => cos (z*((2*s-1 : ℝ) : ℂ))*Q s)
      (g := fun s => cos ((r : ℂ)*((2*s-1 : ℝ) : ℂ))*Q s)
      ((hc z).intervalIntegrable 0 1) ((hc r).intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  have h := classicalHillDirichlet_cosine_residual_bound q z hz H hH hsmall
  change ‖2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
    (∫ s in (0 : ℝ)..1,(cos (z*((2*s-1 : ℝ) : ℂ))-cos z)*Q s)‖ ≤ _ at h
  rw [hsplit] at h
  have hd : ‖L z-L r‖ ≤ Real.exp ‖z-r‖*‖z-r‖*classicalHillPotentialMass q := by
    rw [hdiff]
    exact norm_cosine_frequency_integral_sub_le Q (continuous_extend q) z r
  have he : 2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
      (L r-cos z*(∫ s in (0 : ℝ)..1,Q s)) =
      (2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
        (L z-cos z*(∫ s in (0 : ℝ)..1,Q s)))+(L z-L r) := by ring
  change ‖2*z^2*(classicalHillFlow q (z^2) (0,1) 1).1-2*z*sin z-
    (L r-cos z*(∫ s in (0 : ℝ)..1,Q s))‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add h hd)

end NLS.KdV
