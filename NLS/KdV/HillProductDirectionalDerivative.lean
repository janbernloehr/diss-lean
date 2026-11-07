import NLS.KdV.HillProductCoordinateVariation

/-! Actual joint Fréchet derivatives of the literal Hill product.
The moving-root chain rule fixes the exact inverse-index coordinate
weight at every retained root, without dividing by its zero factor. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem fderiv_hillEnergySequenceProduct_coordinate (n m : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillEnergySequenceProduct n) (E,d) (0,lp.single 2 m 1) =
      hillEnergyProductCoordinateDerivative n m (E,d) := by
  have hline : HasDerivAt (fun w : ℂ => (E,hillZeroCoordinateShift m d w))
      (0,(lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2)) 0 := by
    simpa only [hillZeroCoordinateShift,zero_add,one_smul] using!
      (hasDerivAt_const (0:ℂ) E).prodMk
        ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const
          (lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2)))
  have hF : HasFDerivAt (hillEnergySequenceProduct n)
      (fderiv ℂ (hillEnergySequenceProduct n) (E,d)) (E,hillZeroCoordinateShift m d 0) := by
    simpa only [hillZeroCoordinateShift,zero_smul,add_zero] using
      (analyticAt_hillEnergySequenceProduct n (E,d)).differentiableAt.hasFDerivAt
  have hc : HasDerivAt (fun w : ℂ => hillEnergySequenceProduct n (E,hillZeroCoordinateShift m d w))
      (fderiv ℂ (hillEnergySequenceProduct n) (E,d) (0,lp.single 2 m 1)) 0 := by
    simpa only [Function.comp_def] using! hF.comp_hasDerivAt 0 hline
  exact hc.unique (hasDerivAt_hillEnergySequenceProduct_coordinate n m E d 0)

theorem fderiv_hillEnergySequenceProduct_energy (n : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillEnergySequenceProduct n) (E,d) (1,0) =
      deriv (fun w : ℂ => hillEnergySequenceProduct n (w,d)) E := by
  have hline : HasDerivAt (fun w : ℂ => (w,d)) (1,0) E :=
    (hasDerivAt_id E).prodMk (hasDerivAt_const E d)
  exact ((analyticAt_hillEnergySequenceProduct n (E,d)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    E hline).deriv.symm

theorem hillEnergySequenceZero_shift_selected (m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillEnergySequenceZero m (hillZeroCoordinateShift m d z) = hillEnergySequenceZero m d+(m:ℕ)*z := by
  unfold hillEnergySequenceZero
  rw [hillZeroCoordinateShift_apply,if_pos rfl]
  ring

theorem hillEnergyProductCoordinateDerivative_at_retained_root (n m : ℕ+) (hmn : m ≠ n)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductCoordinateDerivative n m (hillEnergySequenceZero m d,d) =
      -(m:ℕ)*deriv (fun E : ℂ => hillEnergySequenceProduct n (E,d)) (hillEnergySequenceZero m d) := by
  let E := hillEnergySequenceZero m d
  let v : lp (fun _ : ℕ+ => ℂ) 2 := lp.single 2 m 1
  have hline : HasDerivAt (fun w : ℂ => (E+(m:ℕ)*w,hillZeroCoordinateShift m d w))
      ((m:ℕ),v) 0 := by
    simpa only [hillZeroCoordinateShift,zero_add,mul_one,one_smul,v,id_eq,Pi.add_apply] using!
      ((hasDerivAt_const (0:ℂ) E).add ((hasDerivAt_id (0:ℂ)).const_mul ((m:ℕ):ℂ))).prodMk
        ((hasDerivAt_const (0:ℂ) d).add ((hasDerivAt_id (0:ℂ)).smul_const v))
  have hF : HasFDerivAt (hillEnergySequenceProduct n) (fderiv ℂ (hillEnergySequenceProduct n) (E,d))
      (E+(m:ℕ)*(0:ℂ),hillZeroCoordinateShift m d 0) := by
    simpa only [mul_zero,add_zero,hillZeroCoordinateShift,zero_smul] using
      (analyticAt_hillEnergySequenceProduct n (E,d)).differentiableAt.hasFDerivAt
  have hzero : (fun w : ℂ => hillEnergySequenceProduct n (E+(m:ℕ)*w,hillZeroCoordinateShift m d w)) =
      fun _ : ℂ => 0 := by
    funext w
    rw [show E+(m:ℕ)*w = hillEnergySequenceZero m (hillZeroCoordinateShift m d w) from
      (hillEnergySequenceZero_shift_selected m d w).symm]
    exact hillEnergySequenceProduct_retained_root n m hmn _
  have hc := hF.comp_hasDerivAt 0 hline
  dsimp only [Function.comp_def] at hc
  rw [hzero] at hc
  have hz := hc.unique (hasDerivAt_const (0:ℂ) (0:ℂ))
  have hsplit : (((m:ℕ):ℂ),v) = ((m:ℕ):ℂ) • ((1:ℂ),(0:lp (fun _ : ℕ+ => ℂ) 2))+(0,v) := by
    ext <;> simp
  rw [hsplit,map_add,map_smul,smul_eq_mul,fderiv_hillEnergySequenceProduct_energy,
    show (fderiv ℂ (hillEnergySequenceProduct n) (E,d)) (0,v) =
      hillEnergyProductCoordinateDerivative n m (E,d) from fderiv_hillEnergySequenceProduct_coordinate n m E d] at hz
  change hillEnergyProductCoordinateDerivative n m (E,d) = _
  linear_combination hz

end NLS.KdV
