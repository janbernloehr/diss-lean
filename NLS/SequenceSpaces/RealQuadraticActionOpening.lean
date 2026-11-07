import NLS.SequenceSpaces.NonnegativeActions

/-! Two real pairs on one action fiber can open the same closed
coordinate simultaneously, with equal actions and arbitrarily small
perturbations in the original Hilbert pair norm. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

def realCoordinateOpening (j : ℤ) (z : Coeff 2 × Coeff 2) (t : ℝ) : Coeff 2 × Coeff 2 :=
  (z.1+lp.single 2 j (t : ℂ),z.2)

theorem realCoordinateOpening_zero (j : ℤ) (z : Coeff 2 × Coeff 2) :
    realCoordinateOpening j z 0=z := by
  ext k <;> simp [realCoordinateOpening]

theorem continuous_realCoordinateOpening (j : ℤ) (z : Coeff 2 × Coeff 2) :
    Continuous (realCoordinateOpening j z) :=
  (continuous_const.add ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).continuous.comp
    Complex.continuous_ofReal)).prodMk continuous_const

theorem realCoordinateOpening_real (j : ℤ) (z : Coeff 2 × Coeff 2) (hz : z∈realPairLocus 2) (t : ℝ) :
    realCoordinateOpening j z t∈realPairLocus 2 := by
  refine ⟨?_,hz.2⟩
  intro k
  change (z.1 k+(lp.single 2 j (t : ℂ) : Coeff 2) k).im=0
  simp only [lp.single_apply,Pi.single_apply,Complex.add_im,hz.1 k,zero_add]
  split_ifs <;> rfl

theorem real_pair_coordinates_zero_of_action_zero
    (z : Coeff 2 × Coeff 2) (hz : z∈realPairLocus 2) (j : ℤ)
    (h0 : quadraticActionsExponent (q := 1) z j=0) : z.1 j=0 ∧ z.2 j=0 := by
  have hs : (z.1 j)^2+(z.2 j)^2=0 := by
    have h := congrArg (fun v : ℂ => 2*v) h0
    rw [quadraticActionsExponent_apply] at h
    simpa only [mul_div_cancel₀ _ (by norm_num : (2 : ℂ)≠0),mul_zero] using h
  have hr : (z.1 j).re^2+(z.2 j).re^2=0 := by
    simpa only [pow_two,Complex.add_re,Complex.mul_re,hz.1 j,hz.2 j,mul_zero,sub_zero,Complex.zero_re] using congrArg Complex.re hs
  have hx : (z.1 j).re=0 := by nlinarith [sq_nonneg (z.2 j).re]
  have hy : (z.2 j).re=0 := by nlinarith [sq_nonneg (z.1 j).re]
  exact ⟨Complex.ext hx (hz.1 j),Complex.ext hy (hz.2 j)⟩

theorem realCoordinateOpening_actions_eq
    (j : ℤ) (z w : Coeff 2 × Coeff 2) (hz : z∈realPairLocus 2) (hw : w∈realPairLocus 2)
    (ha : quadraticActionsExponent (q := 1) w=quadraticActionsExponent z)
    (h0 : quadraticActionsExponent (q := 1) z j=0) (t : ℝ) :
    quadraticActionsExponent (q := 1) (realCoordinateOpening j w t)=
      quadraticActionsExponent (q := 1) (realCoordinateOpening j z t) := by
  obtain ⟨hz1,hz2⟩ := real_pair_coordinates_zero_of_action_zero z hz j h0
  obtain ⟨hw1,hw2⟩ := real_pair_coordinates_zero_of_action_zero w hw j (by rw [ha];exact h0)
  ext k
  by_cases hk : k=j
  · subst k
    simp [realCoordinateOpening,quadraticActionsExponent_apply,lp.single_apply,hz1,hz2,hw1,hw2]
  · have he := congrArg (fun a : Coeff 1 => a k) ha
    simpa only [realCoordinateOpening,quadraticActionsExponent_apply,lp.coeFn_add,Pi.add_apply,
      lp.single_apply,Pi.single_apply,if_neg hk,add_zero] using he

theorem realCoordinateOpening_action_ne_zero
    (j : ℤ) (z : Coeff 2 × Coeff 2) (hz : z∈realPairLocus 2)
    (h0 : quadraticActionsExponent (q := 1) z j=0) (t : ℝ) (ht : t≠0) :
    quadraticActionsExponent (q := 1) (realCoordinateOpening j z t) j≠0 := by
  obtain ⟨hz1,hz2⟩ := real_pair_coordinates_zero_of_action_zero z hz j h0
  simp only [realCoordinateOpening,quadraticActionsExponent_apply,lp.coeFn_add,Pi.add_apply,
    lp.single_apply,Pi.single_apply,hz1,hz2,zero_add,zero_pow (by norm_num : (2 : ℕ)≠0),add_zero]
  exact div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr ht)) (by norm_num)

end NLS.Coeff
