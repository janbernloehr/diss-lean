import NLS.KdV.HillFullProductDataVariation
import NLS.KdV.HillFrequencyDataVariation
import NLS.ZakharovShabat.SourcePsiFullProductVariation

/-! Differentiating the FULL balanced frequency-product identity gives
the full Hill energy variation, with no omitted-coordinate constraint.
The differentiated square identity recovers every energy direction. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillFrequencyDataVariation_positive_square (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi) (m : ℕ+) :
    2*hillIndependentFrequency (c,d) ((m:ℕ):ℤ)*hillIndependentFrequencyDataVariation c d h ((m:ℕ):ℤ) = (m:ℕ)*h m := by
  have hl : HasDerivAt (fun w : ℂ => hillIndependentFrequency (c,d+w • h) ((m:ℕ):ℤ)^2)
      (2*hillIndependentFrequency (c,d) ((m:ℕ):ℤ)*hillIndependentFrequencyDataVariation c d h ((m:ℕ):ℤ)) 0 := by
    simpa only [Pi.pow_apply,zero_smul,add_zero,Nat.reduceSub,pow_one] using!
      (hasDerivAt_hillFrequencyScalarDataLine c d h hd ((m:ℕ):ℤ)).pow 2
  have hv := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const h))
  have hr : HasDerivAt (fun w : ℂ => ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*(d+w • h) m+c) (((m:ℕ):ℂ)*h m) 0 := by
    simpa only [zero_add,one_smul] using!
      (((hv.const_mul ((m:ℕ):ℂ)).const_add (((Real.pi:ℂ)*(m:ℕ))^2)).add_const c)
  have he : (fun w : ℂ => hillIndependentFrequency (c,d+w • h) ((m:ℕ):ℤ)^2) =
      (fun w : ℂ => ((Real.pi:ℂ)*(m:ℕ))^2+(m:ℕ)*(d+w • h) m+c) :=
    funext (fun w => hillIndependentFrequency_positive_sq (c,d+w • h) m)
  rw [he] at hl
  exact hl.unique hr

theorem hillEnergyFullProductDataVariation_frequency (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi) (z : ℂ) :
    sourcePsiFullProductVariation (hillIndependentFrequencyDisplacement (c,d))
      (hillIndependentFrequencyDataVariation c d h) z = -2*z*hillEnergyFullProductDataVariation d h (z^2-c) := by
  have hp := ((analyticOnNhd_jointSingleSpectralProduct (by norm_num) (by norm_num)
    (z,hillIndependentFrequencyDisplacement (c,d)) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (z,b)) (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt
  have hl := hp.comp_hasDerivAt_of_eq 0 (hasDerivAt_hillFrequencyDataLine c d h hd) (by simp)
  have hr := (hasDerivAt_hillEnergyFullProductDataLine (z^2-c) d h).const_mul (-2*z)
  have he : (fun w : ℂ => jointSingleSpectralProduct (z,hillIndependentFrequencyDisplacement (c,d+w • h))) =
      (fun w : ℂ => -2*z*hillEnergySequenceFullProduct (z^2-c,d+w • h)) :=
    funext (fun w => jointSingleSpectralProduct_eq_full_Hill_product c (d+w • h) z)
  change HasDerivAt (fun w : ℂ => jointSingleSpectralProduct (z,hillIndependentFrequencyDisplacement (c,d+w • h)))
    (sourcePsiFullProductVariation (hillIndependentFrequencyDisplacement (c,d)) (hillIndependentFrequencyDataVariation c d h) z) 0 at hl
  rw [he] at hl
  exact hl.unique hr

theorem hillFrequencyDataVariation_zero_imp_direction_zero (c : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2)
    (hd : (c,d) ∈ LpSequence.quadraticFrequencyDomain Real.pi)
    (hb : hillIndependentFrequencyDataVariation c d h = 0) : h = 0 := by
  ext m
  have hs := hillFrequencyDataVariation_positive_square c d h hd m
  rw [hb] at hs
  simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero] at hs
  exact (mul_eq_zero.mp hs.symm).resolve_left (by exact_mod_cast m.ne_zero)

end NLS.KdV
