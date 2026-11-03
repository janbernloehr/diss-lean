import NLS.KdV.HillFreePeriodOperator
import NLS.ZakharovShabat.SourceFreeCanonicalResidue

/-! At the free source, actual Hill product periods evaluate the
ENTIRE independently placed product at the selected free energy.
The exact original weights factor each retained row by d_m. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergyProductFixedPeriod_free_evaluation (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergyProductFixedPeriod n 0 (0:CoeffPair 2) D d =
      -((Real.pi:ℂ)*(m:ℕ))*hillEnergySequenceProduct n ((((Real.pi:ℂ)*(m:ℕ))^2),d)/
        cos ((Real.pi:ℂ)*(m:ℕ)) := by
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => 2*z*hillEnergySequenceProduct n (z^2,d)) univ := by
    intro z _
    exact (analyticAt_const.mul analyticAt_id).mul
      ((analyticAt_hillEnergySequenceProduct n (z^2,d)).comp
        (f := fun w : ℂ => (w^2,d)) ((analyticAt_id.pow 2).prod analyticAt_const))
  have h := D.freeCanonicalRoot_residue ((m:ℕ):ℤ) _ (hf.mono (subset_univ _))
  simp only [Int.cast_natCast] at h
  unfold hillEnergyProductFixedPeriod hillEnergyProductPeriodIntegrand
  simp only [sub_zero]
  rw [h]
  ring

theorem hillEnergySequenceProduct_freeEnergy_factor (n m : ℕ+) (hmn : m ≠ n)
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillEnergySequenceProduct n ((((Real.pi:ℂ)*(m:ℕ))^2),d) =
      d m*hillEnergyProductCoordinateDerivative n m ((((Real.pi:ℂ)*(m:ℕ))^2),d) := by
  have h := hillEnergyProductCoordinateDerivative_restore n m hmn (((Real.pi:ℂ)*(m:ℕ))^2) d
  simp only [hillEnergySequenceZero,add_sub_cancel_left] at h
  apply mul_left_cancel₀ (show ((m:ℕ):ℂ) ≠ 0 by exact_mod_cast m.ne_zero)
  calc
    _ = (((m:ℕ):ℂ)*d m)*hillEnergyProductCoordinateDerivative n m ((((Real.pi:ℂ)*(m:ℕ))^2),d) := h.symm
    _ = _ := by ring

def hillFreePeriodMultiplier (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  if m = n then 1 else hillPeriodEquationWeight n m*
    (-((Real.pi:ℂ)*(m:ℕ))/cos ((Real.pi:ℂ)*(m:ℕ)))*
      hillEnergyProductCoordinateDerivative n m ((((Real.pi:ℂ)*(m:ℕ))^2),d)

theorem hillFreePeriodEquationRow_factor (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (d : lp (fun _ : ℕ+ => ℂ) 2) :
    hillFreePeriodEquationRow n m D d = d m*hillFreePeriodMultiplier n m d := by
  by_cases hmn : m = n
  · subst m
    simp only [hillFreePeriodEquationRow,hillFreePeriodMultiplier,ite_true,mul_one]
  · simp only [hillFreePeriodEquationRow,hillFreePeriodMultiplier,if_neg hmn]
    rw [hillEnergyProductFixedPeriod_free_evaluation,hillEnergySequenceProduct_freeEnergy_factor n m hmn]
    ring

theorem analyticAt_hillFreePeriodMultiplier (n m : ℕ+) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    AnalyticAt ℂ (hillFreePeriodMultiplier n m) d := by
  unfold hillFreePeriodMultiplier
  split_ifs
  · exact analyticAt_const
  · exact analyticAt_const.mul ((analyticAt_hillEnergyProductCoordinateDerivative n m _).comp
      (f := fun e : lp (fun _ : ℕ+ => ℂ) 2 => ((((Real.pi:ℂ)*(m:ℕ))^2),e))
      (analyticAt_const.prod analyticAt_id))

theorem hillFreePeriodMultiplier_zero (n m : ℕ+) :
    hillFreePeriodMultiplier n m 0 = 1 := by
  let D := hillFreePeriodCircle m
  have hmul := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).hasFDerivAt.mul
    (analyticAt_hillFreePeriodMultiplier n m 0).differentiableAt.hasFDerivAt
  have he : hillFreePeriodEquationRow n m D = fun d => d m*hillFreePeriodMultiplier n m d :=
    funext (hillFreePeriodEquationRow_factor n m D)
  change HasFDerivAt (fun d : lp (fun _ : ℕ+ => ℂ) 2 => d m*hillFreePeriodMultiplier n m d) _ 0 at hmul
  rw [← he] at hmul
  have h := congrArg (fun L : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] ℂ => L (lp.single 2 m 1)) hmul.fderiv
  rw [hillFreePeriodEquationRow_fderiv_single,if_pos rfl] at h
  change 1 = (0:ℂ)*(fderiv ℂ (hillFreePeriodMultiplier n m) 0 (lp.single 2 m 1))+
    hillFreePeriodMultiplier n m 0*(lp.single 2 m 1 : lp (fun _ : ℕ+ => ℂ) 2) m at h
  simpa only [zero_mul,zero_add,lp.single_apply,Pi.single_eq_same,mul_one] using h.symm

end NLS.KdV
