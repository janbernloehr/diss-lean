import NLS.ZakharovShabat.L2SolutionVariation
import NLS.ZakharovShabat.ClassicalPotentialVariation

/-! # Physical L2 potential derivatives and their endpoint values -/
noncomputable section
open Set Complex
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The potential section is analytic in the norm of the entire solution curve. -/
theorem analyticOnNhd_l2SolutionCurve_potential (z : ℂ) (v : ℂ × ℂ) :
    AnalyticOnNhd ℂ (fun u : IntervalPairL2 => l2SolutionCurve u z v) univ := by
  intro u _
  exact (analyticOnNhd_l2SolutionCurve_joint v (z,u) (mem_univ _)).comp
    (f := fun w : IntervalPairL2 => (z,w)) (analyticAt_const.prod analyticAt_id)

/-- Every physical L2 direction gives the zero-initial potential variation. -/
theorem fderiv_l2SolutionCurve_potential (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    (fderiv ℂ (fun w : IntervalPairL2 => l2SolutionCurve w z v) u) h =
      l2VariationCurve (z,u) (0,h) v := by
  have hd := (analyticOnNhd_l2SolutionCurve_joint v (z,u) (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hd.comp u (hasFDerivAt_prodMk_right z u)
  have he := hc.fderiv
  change fderiv ℂ (fun w : IntervalPairL2 => l2SolutionCurve w z v) u = _ at he
  rw [he,ContinuousLinearMap.comp_apply]
  exact fderiv_l2SolutionCurve_joint_apply (z,u) (0,h) v

/-- Evaluation at every physical time commutes with the actual potential derivative. -/
theorem fderiv_l2SolutionCurve_potential_eval (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    (fderiv ℂ (fun w : IntervalPairL2 => l2SolutionCurve w z v t) u) h =
      l2VariationCurve (z,u) (0,h) v t := by
  have hd := (analyticOnNhd_l2SolutionCurve_potential z v u (mem_univ _)).differentiableAt.hasFDerivAt
  let ev : Curve (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := ContinuousMap.evalCLM ℂ t
  have hc := ev.hasFDerivAt.comp u hd
  have he := hc.fderiv
  change fderiv ℂ (fun w : IntervalPairL2 => l2SolutionCurve w z v t) u = _ at he
  rw [he,ContinuousLinearMap.comp_apply,fderiv_l2SolutionCurve_potential]
  rfl

/-- The forcing has exactly the original off-diagonal signs, even for rough directions. -/
theorem l2PotentialVariation_eq_integral (u h : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    l2VariationCurve (z,u) (0,h) v t =
      (I*(∫ s in (0 : ℝ)..t.val, h.ofLp.1 s*l2BoundedSecond (l2SolutionCurve u z v) s),
       -I*(∫ s in (0 : ℝ)..t.val, h.ofLp.2 s*l2BoundedFirst (l2SolutionCurve u z v) s))+
      l2ODEIntegral u z (l2VariationCurve (z,u) (0,h) v) t := by
  rw [l2VariationCurve_eq_integral,l2ODEIntegral_eq h 0]
  simp

/-- A global bound in the physical L2 norm, linear in the perturbation. -/
theorem norm_l2VariationCurve_le (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ) :
    ‖l2VariationCurve q d v‖ ≤
      Real.exp (‖q.1‖+‖q.2‖)*((‖d.1‖+‖d.2‖)*(‖v‖*Real.exp (‖q.1‖+‖q.2‖))) := by
  apply (l2SolutionOperator q).le_of_opNorm_le (norm_l2SolutionOperator_le q) _ |>.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply ((l2Volterra d).le_of_opNorm_le (norm_l2Volterra_le d) _).trans
  exact mul_le_mul_of_nonneg_left (norm_l2SolutionCurve_le q.2 q.1 v)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The new variation recovers the original continuous-potential variation exactly. -/
theorem l2PotentialVariation_of_continuous (Φ H : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    l2VariationCurve (z,continuousPotentialL2Class Φ) (0,continuousPotentialL2Class H) v =
      classicalPotentialVariationCurve Φ H z v := by
  rw [l2VariationCurve,l2SolutionOperator_of_continuous,l2Volterra_of_continuous,
    l2SolutionCurve_of_continuous]
  simp only [classicalPotentialVariationCurve,forcedSolutionCurve,
    show ContinuousMap.const (Icc (0 : ℝ) 1) (0 : ℂ × ℂ) = 0 from rfl,
    zero_add,classicalPotentialVariationSource,primitive_coefficientVariationSource]
  rfl

end NLS.ZakharovShabat
