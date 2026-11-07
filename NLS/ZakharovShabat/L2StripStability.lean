import NLS.ZakharovShabat.ClassicalL2StripStability
import NLS.ZakharovShabat.L2FundamentalAnalytic

/-! Actual physical L2 fundamental solutions are uniformly stable on
horizontal frequency strips, with no growth in the real spectral parameter. -/
noncomputable section
open Set Metric Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The actual whole solution curve has a physical L2 growth estimate
controlled only by imaginary height. -/
theorem norm_l2SolutionCurve_le_exp_im (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    ‖l2SolutionCurve u z v‖ ≤ ‖v‖*Real.exp (|z.im|+‖u‖) := by
  have hsol : Continuous (fun w : IntervalPairL2 => l2SolutionCurve w z v) := by
    have hp : Continuous (fun w : IntervalPairL2 => (z,w)) := continuous_const.prodMk continuous_id
    convert! (continuous_l2SolutionCurve_joint v).comp hp
  refine denseRange_continuousPotentialL2Class.induction_on u
    (isClosed_le hsol.norm (by fun_prop)) ?_
  intro phi
  rw [l2SolutionCurve_of_continuous,norm_continuousPotentialL2Class]
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  rw [classicalSolutionCurve_apply]
  exact norm_classicalSolution_le_exp_im_L2 phi z v t

/-- The exact physical L2 distance controls the ACTUAL complete solution
curves uniformly over arbitrary real frequency, at every complex potential. -/
theorem norm_l2SolutionCurve_sub_le_im (u w : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    ‖l2SolutionCurve u z v-l2SolutionCurve w z v‖ ≤
      ‖v‖*Real.exp (2*|z.im|+‖u‖+‖w‖)*‖u-w‖ := by
  have hsol : Continuous (fun a : IntervalPairL2 => l2SolutionCurve a z v) := by
    have hp : Continuous (fun w : IntervalPairL2 => (z,w)) := continuous_const.prodMk continuous_id
    convert! (continuous_l2SolutionCurve_joint v).comp hp
  have hleft : Continuous (fun p : IntervalPairL2 × IntervalPairL2 =>
      ‖l2SolutionCurve p.1 z v-l2SolutionCurve p.2 z v‖) :=
    ((hsol.comp continuous_fst).sub (hsol.comp continuous_snd)).norm
  refine (denseRange_continuousPotentialL2Class.prodMap denseRange_continuousPotentialL2Class).induction_on
    (p := fun p : IntervalPairL2 × IntervalPairL2 =>
      ‖l2SolutionCurve p.1 z v-l2SolutionCurve p.2 z v‖ ≤
        ‖v‖*Real.exp (2*|z.im|+‖p.1‖+‖p.2‖)*‖p.1-p.2‖)
    (u,w) (isClosed_le hleft (by fun_prop)) ?_
  rintro ⟨phi,psi⟩
  change ‖l2SolutionCurve (continuousPotentialL2Class phi) z v-
    l2SolutionCurve (continuousPotentialL2Class psi) z v‖ ≤
      ‖v‖*Real.exp (2*|z.im|+‖continuousPotentialL2Class phi‖+‖continuousPotentialL2Class psi‖)*
        ‖continuousPotentialL2Class phi-continuousPotentialL2Class psi‖
  rw [l2SolutionCurve_of_continuous,l2SolutionCurve_of_continuous]
  rw [← continuousPotentialL2Class_sub,norm_continuousPotentialL2Class,
    norm_continuousPotentialL2Class,norm_continuousPotentialL2Class]
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg (norm_nonneg _)
    (Real.exp_nonneg _)) (Real.sqrt_nonneg _))).mpr
  intro t
  change ‖classicalSolutionCurve phi z v t-classicalSolutionCurve psi z v t‖ ≤ _
  rw [classicalSolutionCurve_apply,classicalSolutionCurve_apply]
  exact norm_classicalSolution_sub_le_im_L2 phi psi z v t

/-- On each physical L2 norm ball and horizontal frequency strip, ONE
Lipschitz constant works for ALL real frequencies and all initial vectors. -/
theorem norm_l2SolutionCurve_sub_le_of_strip_bounds
    (u w : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) (R H : ℝ)
    (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ R) (hz : |z.im| ≤ H) :
    ‖l2SolutionCurve u z v-l2SolutionCurve w z v‖ ≤
      (‖v‖*Real.exp (2*H+2*R))*‖u-w‖ := by
  apply (norm_l2SolutionCurve_sub_le_im u w z v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  linarith

end NLS.ZakharovShabat
