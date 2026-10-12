import NLS.ZakharovShabat.L2FundamentalAnalytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # The actual variation of physical L2 solutions

Differentiating the invertible Volterra equation in frequency and the
physical L2 potential gives its unique linearized integral solution.
No continuous representative or smallness hypothesis is required.
-/
noncomputable section
open Set Complex
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The variation has zero initial data and is forced by the perturbed coefficient. -/
def l2VariationCurve (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ) : Curve (ℂ × ℂ) :=
  l2SolutionOperator q (l2Volterra d (l2SolutionCurve q.2 q.1 v))

/-- The joint Fréchet derivative is the actual linearized Volterra solution. -/
theorem fderiv_l2SolutionCurve_joint_apply (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ) :
    (fderiv ℂ (fun r : ℂ × IntervalPairL2 => l2SolutionCurve r.2 r.1 v) q) d =
      l2VariationCurve q d v := by
  let u : (ℂ × IntervalPairL2) → Curve (ℂ × ℂ) := fun r => l2SolutionCurve r.2 r.1 v
  have hd : HasFDerivAt u (fderiv ℂ u q) q :=
    (analyticOnNhd_l2SolutionCurve_joint v q (mem_univ _)).differentiableAt.hasFDerivAt
  have hV : HasFDerivAt l2VolterraCoefficientMap l2VolterraCoefficientMap q :=
    by convert! (ContinuousLinearMap.hasFDerivAt (𝕜 := ℂ)
      (E := ℂ × IntervalPairL2) (F := Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ))
      l2VolterraCoefficientMap (x := q))
  have hprod : HasFDerivAt (fun r => l2VolterraCoefficientMap r (u r))
      ((l2Volterra q).comp (fderiv ℂ u q)+l2VolterraCoefficientMap.flip (u q)) q :=
    HasFDerivAt.clm_apply (𝕜 := ℂ) (E := ℂ × IntervalPairL2)
      (G := Curve (ℂ × ℂ)) (H := Curve (ℂ × ℂ)) hV hd
  have hdiff := hd.sub hprod
  have heq : (fun r : ℂ × IntervalPairL2 => u r-l2VolterraCoefficientMap r (u r)) =
      (fun _ => ContinuousMap.const _ v) := by
    funext r
    change (1-l2Volterra r) (l2SolutionCurve r.2 r.1 v) = _
    rw [l2SolutionCurve_eq_l2SolutionOperator,← mul_apply_eq_comp,mul_l2SolutionOperator,one_apply_eq_self]
  have hzero := congrArg (fun L => L d) hdiff.fderiv
  change (fderiv ℂ (fun r => u r-l2VolterraCoefficientMap r (u r)) q) d = _ at hzero
  rw [heq] at hzero
  simp only [fderiv_fun_const] at hzero
  change (0 : Curve (ℂ × ℂ)) = (fderiv ℂ u q) d-
    (l2Volterra q ((fderiv ℂ u q) d)+l2Volterra d (u q)) at hzero
  have hlin : (1-l2Volterra q) ((fderiv ℂ u q) d) = l2Volterra d (u q) := by
    have h := sub_eq_zero.mp hzero.symm
    change (fderiv ℂ u q) d-l2Volterra q ((fderiv ℂ u q) d) = _
    exact sub_eq_iff_eq_add.mpr (h.trans (add_comm _ _))
  have h := congrArg (fun w => l2SolutionOperator q w) hlin
  rw [← mul_apply_eq_comp,l2SolutionOperator_mul,one_apply_eq_self] at h
  exact h

/-- The physical integral equation, with both original coefficient signs. -/
theorem l2VariationCurve_eq_integral (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    l2VariationCurve q d v t =
      l2ODEIntegral d.2 d.1 (l2SolutionCurve q.2 q.1 v) t+
      l2ODEIntegral q.2 q.1 (l2VariationCurve q d v) t := by
  have h := (l2SolutionOperator_eq_iff q
    (l2Volterra d (l2SolutionCurve q.2 q.1 v)) (l2VariationCurve q d v)).mp rfl t
  simpa only [l2Volterra_apply] using h

@[simp] theorem l2VariationCurve_zero (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ) :
    l2VariationCurve q d v ⟨0,by norm_num⟩ = 0 := by
  rw [l2VariationCurve_eq_integral]
  simp [l2ODEIntegral]

/-- Uniqueness uses the integral equation; an a.e. differential equation alone is insufficient. -/
theorem l2VariationCurve_unique (q d : ℂ × IntervalPairL2) (v : ℂ × ℂ)
    (w : Curve (ℂ × ℂ))
    (h : ∀ t, w t = l2ODEIntegral d.2 d.1 (l2SolutionCurve q.2 q.1 v) t+
      l2ODEIntegral q.2 q.1 w t) : w = l2VariationCurve q d v := by
  apply (l2SolutionOperator_eq_iff q (l2Volterra d (l2SolutionCurve q.2 q.1 v)) w).mpr
  simpa only [l2Volterra_apply] using h

end NLS.ZakharovShabat
