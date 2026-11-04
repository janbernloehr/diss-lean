import NLS.KdV.HillProductCoordinateVariation
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! The entire variation of the literal Hill product in an arbitrary
full l2 data direction, including evaluation at a retained root. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyProductDataVariation (n : ℕ+) (d h : lp (fun _ : ℕ+ => ℂ) 2) (E : ℂ) : ℂ :=
  fderiv ℂ (hillEnergySequenceProduct n) (E,d) (0,h)

theorem hillEnergyProductDataVariation_eq_section (n : ℕ+) (d h : lp (fun _ : ℕ+ => ℂ) 2) (E : ℂ) :
    hillEnergyProductDataVariation n d h E = fderiv ℂ (fun b => hillEnergySequenceProduct n (E,b)) d h := by
  rw [NLS.ComplexAnalysis.fderiv_source_section_eq_joint (hillEnergySequenceProduct n) E d
    (analyticAt_hillEnergySequenceProduct n (E,d)).differentiableAt]
  rfl

theorem analyticOnNhd_hillEnergyProductDataVariation (n : ℕ+) (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticOnNhd ℂ (hillEnergyProductDataVariation n d h) univ := by
  let ev : ((ℂ × lp (fun _ : ℕ+ => ℂ) 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  have hP : AnalyticOnNhd ℂ (hillEnergySequenceProduct n) univ := fun t _ => analyticAt_hillEnergySequenceProduct n t
  have hd := ev.comp_analyticOnNhd hP.fderiv
  intro E _
  exact (hd (E,d) (mem_univ _)).comp (f := fun w : ℂ => (w,d)) (analyticAt_id.prod analyticAt_const)

theorem hasDerivAt_hillEnergyDataLine (E : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    HasDerivAt (fun w : ℂ => (E,d+w • h)) (0,h) 0 := by
  simpa only [zero_add,one_smul] using! (hasDerivAt_const (0:ℂ) E).prodMk
    ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const h))

theorem hasDerivAt_hillEnergyProductDataLine (n : ℕ+) (E : ℂ) (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    HasDerivAt (fun w : ℂ => hillEnergySequenceProduct n (E,d+w • h))
      (hillEnergyProductDataVariation n d h E) 0 := by
  have hp := (analyticAt_hillEnergySequenceProduct n (E,d)).differentiableAt.hasFDerivAt
  simpa only [zero_smul,add_zero] using!
    hp.comp_hasDerivAt_of_eq 0 (hasDerivAt_hillEnergyDataLine E d h) (by simp)

theorem hillEnergyProductDataVariation_at_retained_root (n m : ℕ+) (hmn : m ≠ n)
    (d h : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductDataVariation n d h (hillEnergySequenceZero m d) =
      hillEnergyProductCoordinateDerivative n m (hillEnergySequenceZero m d,d)*h m := by
  let E := hillEnergySequenceZero m d
  have hσ : HasDerivAt (fun w : ℂ => hillEnergySequenceZero m (d+w • h)-E) (((m:ℕ):ℂ)*h m) 0 := by
    have hv := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const h))
    simpa only [hillEnergySequenceZero,zero_add,one_smul] using!
      ((hv.const_mul ((m:ℕ):ℂ)).const_add (((Real.pi:ℂ)*(m:ℕ))^2)).sub_const E
  have hd := (analyticAt_hillEnergyProductCoordinateDerivative n m (E,d)).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq
    0 (hasDerivAt_hillEnergyDataLine E d h) (by simp)
  have hl : HasDerivAt (fun w : ℂ => (hillEnergySequenceZero m (d+w • h)-E)*
      hillEnergyProductCoordinateDerivative n m (E,d+w • h))
      (((m:ℕ):ℂ)*h m*hillEnergyProductCoordinateDerivative n m (E,d)) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero,E,sub_self,zero_mul,add_zero] using! hσ.mul hd
  have hr := (hasDerivAt_hillEnergyProductDataLine n E d h).const_mul ((m:ℕ):ℂ)
  have he : (fun w : ℂ => (hillEnergySequenceZero m (d+w • h)-E)*
      hillEnergyProductCoordinateDerivative n m (E,d+w • h)) =
      (fun w : ℂ => (m:ℕ)*hillEnergySequenceProduct n (E,d+w • h)) :=
    funext (fun w => hillEnergyProductCoordinateDerivative_restore n m hmn E (d+w • h))
  rw [he] at hl
  have hh := hl.unique hr
  dsimp only [E] at hh
  have hm : ((m:ℕ):ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  apply mul_left_cancel₀ hm
  linear_combination -hh

end NLS.KdV
