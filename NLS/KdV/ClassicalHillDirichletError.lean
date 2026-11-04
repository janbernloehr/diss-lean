import NLS.KdV.ClassicalHillSmallPotential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem classicalHillDirichlet_free_error_small (q : Curve ℂ) (z : ℂ) (hz : z ≠ 0)
    (H : ℝ) (hH : |z.im| ≤ H)
    (hsmall : Real.exp H/‖z‖*classicalHillPotentialMass q ≤ 1/2) :
    ‖(classicalHillFlow q (z^2) (0,1) 1).1-sin z/z‖ ≤
      2*(Real.exp H)^2*classicalHillPotentialMass q/‖z‖^2 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  have hS (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖(classicalHillFlow q (z^2) (0,1) s).1‖ ≤ 2*Real.exp H/‖z‖ := by
    have h := classicalHillFlow_position_bound_small q z hz H hH hsmall (0,1) ⟨s,hs⟩
    simpa only [norm_one,norm_zero,zero_add,mul_one_div] using h
  have hs := norm_sine_duhamel_integral_le (NLS.LinearVolterra.extend q)
    (fun s => (classicalHillFlow q (z^2) (0,1) s).1) z H (2*Real.exp H/‖z‖) 1
    (continuous_extend q) hH ⟨by norm_num,le_rfl⟩ hS
  have hse : (classicalHillFlow q (z^2) (0,1) 1).1-sin z/z =
      ∫ s in (0 : ℝ)..1,sin (z*((1-s : ℝ) : ℂ))/z*NLS.LinearVolterra.extend q s*
        (classicalHillFlow q (z^2) (0,1) s).1 := by
    have h := classicalHillFlow_sine_duhamel q z hz (0,1) t
    simpa only [t,ofReal_one,mul_one,mul_zero,zero_add,add_sub_cancel_left] using
      congrArg (fun x : ℂ => x-sin z/z) h
  rw [hse]
  apply hs.trans_eq
  change (Real.exp H/‖z‖*(2*Real.exp H/‖z‖))*classicalHillPotentialMass q = _
  ring

end NLS.KdV
