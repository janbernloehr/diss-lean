import NLS.ZakharovShabat.L2VolterraOperator

/-! # Global invertibility of the actual physical L2 Volterra equation

A continuous approximation has an inverse bounded in the L2 norm.
A sufficiently small L2 perturbation is therefore invertible. The resulting
inverse recovers the existing approximation-independent solution exactly.
-/
noncomputable section
open Set Complex Metric
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The actual Volterra equation is invertible for every frequency and L2 potential. -/
theorem isUnit_one_sub_l2Volterra (q : ℂ × IntervalPairL2) : IsUnit (1-l2Volterra q) := by
  let B := Real.exp (‖q.1‖+‖q.2‖+1)
  have hB : 0 < B := Real.exp_pos _
  let δ := min 1 (1/(2*B))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨φ,hφ⟩ := exists_continuousPotential_L2_approximation q.2 δ hδ
  let A := classicalCoefficientCurveCLM (q.1,φ)
  let S := solutionOperator A
  let D := l2Volterra q-volterra A
  have hφnorm : ‖continuousPotentialL2Class φ‖ ≤ ‖q.2‖+1 := by
    rw [dist_comm] at hφ
    exact (norm_le_norm_add_const_of_dist_le hφ.le).trans
      (add_le_add (le_refl _) (min_le_left _ _))
  have hS : ‖S‖ ≤ B := by
    apply (norm_classicalSolutionOperator_le_L2 φ q.1).trans
    rw [← norm_continuousPotentialL2Class]
    apply Real.exp_le_exp.mpr
    linarith
  have hD : ‖D‖ < δ := by
    have h := norm_l2Volterra_sub_le q.2 (continuousPotentialL2Class φ) q.1
    rw [l2Volterra_of_continuous] at h
    exact h.trans_lt (by simpa only [dist_eq_norm] using hφ)
  have hsmall : ‖S*D‖ < 1 := by
    apply (norm_mul_le S D).trans_lt
    have hBD : B*‖D‖ < 1/2 := by
      have hd' := hD.trans_le (min_le_right (1 : ℝ) (1/(2*B)))
      have hh := (lt_div_iff₀ (by positivity : 0 < 2*B)).mp hd'
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hS (norm_nonneg D)]
  have he : (1-volterra A)*(1-S*D) = 1-l2Volterra q := by
    rw [mul_sub,mul_one,← mul_assoc,mul_solutionOperator,one_mul]
    dsimp [D]
    abel
  rw [← he]
  exact (isUnit_one_sub_volterra A).mul (isUnit_one_sub_of_norm_lt_one (R := Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ)) hsmall)

/-- The full inverse accepts arbitrary continuous forcing. -/
def l2SolutionOperator (q : ℂ × IntervalPairL2) : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  Ring.inverse (1-l2Volterra q)

theorem l2SolutionOperator_mul (q : ℂ × IntervalPairL2) :
    l2SolutionOperator q*(1-l2Volterra q) = 1 :=
  Ring.inverse_mul_cancel _ (isUnit_one_sub_l2Volterra q)

theorem mul_l2SolutionOperator (q : ℂ × IntervalPairL2) :
    (1-l2Volterra q)*l2SolutionOperator q = 1 :=
  Ring.mul_inverse_cancel _ (isUnit_one_sub_l2Volterra q)

/-- Arbitrary continuous forcing has exactly one solution of the actual L2 integral equation. -/
theorem l2SolutionOperator_eq_iff (q : ℂ × IntervalPairL2)
    (f w : Curve (ℂ × ℂ)) :
    w = l2SolutionOperator q f ↔ ∀ t, w t = f t+l2ODEIntegral q.2 q.1 w t := by
  have he : (∀ t, w t = f t+l2ODEIntegral q.2 q.1 w t) ↔ (1-l2Volterra q) w = f := by
    constructor
    · intro h
      apply ContinuousMap.ext
      intro t
      simp only [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,l2Volterra_apply]
      rw [h t]
      exact add_sub_cancel_right _ _
    · intro h t
      have ht := congrArg (fun g : Curve (ℂ × ℂ) => g t) h
      simp only [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,l2Volterra_apply] at ht
      exact eq_add_of_sub_eq ht
  rw [he]
  constructor
  · rintro rfl
    change ((1-l2Volterra q)*l2SolutionOperator q) f = f
    rw [mul_l2SolutionOperator,one_apply_eq_self]
  · intro h
    calc
      w = (l2SolutionOperator q*(1-l2Volterra q)) w := by
        rw [l2SolutionOperator_mul,one_apply_eq_self]
      _ = _ := by rw [mul_apply_eq_comp,h]

/-- The inverse construction is the previously defined actual L2 initial-value solution. -/
theorem l2SolutionCurve_eq_l2SolutionOperator (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ) :
    l2SolutionCurve u z v = l2SolutionOperator (z,u) (ContinuousMap.const _ v) := by
  have h : (1-l2Volterra (z,u)) (l2SolutionCurve u z v) = ContinuousMap.const _ v := by
    apply ContinuousMap.ext
    intro t
    simp only [sub_apply,one_apply_eq_self,ContinuousMap.sub_apply,l2Volterra_apply,ContinuousMap.const_apply]
    rw [l2SolutionCurve_eq_integral]
    exact add_sub_cancel_right _ _
  calc
    _ = (l2SolutionOperator (z,u)*(1-l2Volterra (z,u))) (l2SolutionCurve u z v) := by
      rw [l2SolutionOperator_mul,one_apply_eq_self]
    _ = _ := by rw [mul_apply_eq_comp,h]

/-- Uniqueness for the original physical L2 initial-value integral equation. -/
theorem l2SolutionCurve_unique_integral (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (w : Curve (ℂ × ℂ)) (h : ∀ t, w t = v+l2ODEIntegral u z w t) :
    w = l2SolutionCurve u z v := by
  rw [l2SolutionCurve_eq_l2SolutionOperator]
  exact (l2SolutionOperator_eq_iff (z,u) (ContinuousMap.const _ v) w).mpr h

end NLS.ZakharovShabat
