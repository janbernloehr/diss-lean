import NLS.ComplexAnalysis.QuantitativeAnalyticInverse
import NLS.SequenceSpaces.NearbyInverse

/-!
# Quantitative analytic inversion near the identity

The Neumann estimate constructs every required derivative inverse from
its distance to the identity. The resulting analytic inverse theorem
has uniform source and image radii depending only on the domain radius
and derivative Lipschitz constant, with inverse norm bound two.
-/

noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A full operator within one half of the identity is a continuous
linear equivalence, with inverse norm at most two. -/
theorem exists_continuousLinearEquiv_of_norm_sub_id_le_half
    (T : E →L[ℂ] E) (h : ‖T-ContinuousLinearMap.id ℂ E‖ ≤ (1/2 : ℝ)) :
    ∃ e : E ≃L[ℂ] E, (e : E →L[ℂ] E) = T ∧ ‖(e.symm : E →L[ℂ] E)‖ ≤ 2 := by
  have hnear : ‖ContinuousLinearMap.id ℂ E‖*‖ContinuousLinearMap.id ℂ E-T‖ ≤ (1/2 : ℝ) := by
    calc
      _ ≤ 1*‖T-ContinuousLinearMap.id ℂ E‖ := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ ≤ 1/2 := by simpa only [one_mul] using h
  obtain ⟨R,hTR,hRT,_⟩ := NLS.exists_inverse_norm_le_two_mul_of_near T
    (ContinuousLinearMap.id ℂ E) (ContinuousLinearMap.id ℂ E) (by simp) (by simp) hnear
  have hbij : Function.Bijective T := ContinuousLinearMap.isUnit_iff_bijective.mp
    ⟨⟨T,R,hTR,hRT⟩,rfl⟩
  let e := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have he : (e : E →L[ℂ] E) = T := rfl
  have hTe : T.comp (e.symm : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E := by
    ext x
    exact e.apply_symm_apply x
  refine ⟨e,he,?_⟩
  exact (NLS.inverse_norm_le_two_mul_of_near T (ContinuousLinearMap.id ℂ E)
    (e.symm : E →L[ℂ] E) (ContinuousLinearMap.id ℂ E) hTe (by simp) hnear).trans
      (by linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)])

/-- Actual derivative closeness to the identity constructs an analytic
inverse on explicit common balls. No supplied derivative equivalence
or pointwise bijectivity replaces the smallness hypothesis. -/
theorem exists_analytic_inverse_of_derivative_near_id
    (f : E → E) (a : E) (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hnear : ∀ x ∈ ball a R,
      ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/2 : ℝ))
    (hLip : ∀ x ∈ ball a R, ∀ y ∈ ball a R,
      ‖fderiv ℂ f x-fderiv ℂ f y‖ ≤ L*‖x-y‖) :
    ∃ g : E → E,
      AnalyticOnNhd ℂ g (ball (f a) (quantitativeInverseImageRadius R 2 L)) ∧
      g (f a) = a ∧
      ∀ y ∈ ball (f a) (quantitativeInverseImageRadius R 2 L),
        g y ∈ ball a (quantitativeInverseJointRadius R 2 L) ∧ f (g y) = y ∧
        ∀ x ∈ ball a (quantitativeInverseJointRadius R 2 L), f x = y → x = g y := by
  obtain ⟨T,hT,hTB⟩ := exists_continuousLinearEquiv_of_norm_sub_id_le_half
    (fderiv ℂ f a) (hnear a (mem_ball_self hR))
  apply exists_analytic_inverse_on_uniform_ball f a R 2 L hR (by norm_num) hL hf T hT hTB hLip
  intro x hx
  obtain ⟨e,he,_⟩ := exists_continuousLinearEquiv_of_norm_sub_id_le_half (fderiv ℂ f x) (hnear x hx)
  rw [← he]
  exact e.bijective

omit [CompleteSpace E] in
/-- A derivative uniformly within one half of the identity gives a
lower distance bound on the whole convex ball. Inverse images can
therefore differ by at most twice the distance of their targets. -/
theorem norm_sub_le_two_mul_norm_image_sub_of_derivative_near_id
    (f : E → E) (a : E) (R : ℝ)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (hnear : ∀ x ∈ ball a R,
      ‖fderiv ℂ f x-ContinuousLinearMap.id ℂ E‖ ≤ (1/2 : ℝ))
    (x y : E) (hx : x ∈ ball a R) (hy : y ∈ ball a R) :
    ‖x-y‖ ≤ 2*‖f x-f y‖ := by
  let k : E → E := fun z => f z-z
  have hk (z : E) (hz : z ∈ ball a R) : DifferentiableAt ℂ k z :=
    (hf z hz).differentiableAt.sub differentiableAt_id
  have hder (z : E) (hz : z ∈ ball a R) : ‖fderiv ℂ k z‖ ≤ (1/2 : ℝ) := by
    have he : fderiv ℂ k z = fderiv ℂ f z-ContinuousLinearMap.id ℂ E :=
      ((hf z hz).differentiableAt.hasFDerivAt.sub (hasFDerivAt_id z)).fderiv
    rw [he]
    exact hnear z hz
  have hLip := (convex_ball a R).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ) (f := k) hk hder hy hx
  have hbound : ‖x-y‖ ≤ ‖f x-f y‖+(1/2 : ℝ)*‖x-y‖ := by
    calc
      _ = ‖(f x-f y)-(k x-k y)‖ := by congr 1; dsimp [k]; abel
      _ ≤ ‖f x-f y‖+‖k x-k y‖ := norm_sub_le _ _
      _ ≤ ‖f x-f y‖+(1/2 : ℝ)*‖x-y‖ := add_le_add le_rfl hLip
  nlinarith

end NLS.ComplexAnalysis
