import NLS.ComplexAnalysis.QuantitativeAnalyticInverse
import NLS.FunctionalAnalysis.NeumannCompositionBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.ComplexAnalysis



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A quantitative derivative neighborhood on which the base inverse
remains a valid Neumann reference operator. -/
def quantitativeNeumannRadius (R B L : ℝ) : ℝ :=
  min R (1/(4*B*(L+1)))

theorem quantitativeNeumannRadius_pos {R B L : ℝ} (hR : 0<R) (hB : 1≤B) (hL : 0≤L) :
    0<quantitativeNeumannRadius R B L := by
  unfold quantitativeNeumannRadius
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  positivity

/-- Base inverse bounds and a common derivative Lipschitz constant give
common analytic inverse radii. All nearby derivative inverses are proved
by Neumann perturbation, rather than supplied as a separate hypothesis. -/
theorem exists_analytic_inverse_on_neumann_ball
    (f : E → E) (a : E) (R B L : ℝ) (hR : 0<R) (hB : 1≤B) (hL : 0≤L)
    (hf : AnalyticOnNhd ℂ f (ball a R))
    (T : E ≃L[ℂ] E) (hT : (T : E →L[ℂ] E)=fderiv ℂ f a)
    (hTB : ‖(T.symm : E →L[ℂ] E)‖≤B)
    (hLip : ∀ x∈ball a R, ∀ y∈ball a R,
      ‖fderiv ℂ f x-fderiv ℂ f y‖≤L*‖x-y‖) :
    ∃ g : E → E,
      AnalyticOnNhd ℂ g (ball (f a) (quantitativeInverseImageRadius (quantitativeNeumannRadius R B L) B L)) ∧
      g (f a)=a ∧
      ∀ y∈ball (f a) (quantitativeInverseImageRadius (quantitativeNeumannRadius R B L) B L),
        g y∈ball a (quantitativeInverseJointRadius (quantitativeNeumannRadius R B L) B L) ∧
        f (g y)=y ∧ ∀ x∈ball a (quantitativeInverseJointRadius (quantitativeNeumannRadius R B L) B L),
          f x=y → x=g y := by
  let r := quantitativeNeumannRadius R B L
  have hr : 0<r := quantitativeNeumannRadius_pos hR hB hL
  have hrR : r≤R := min_le_left _ _
  have hsub : ball a r ⊆ ball a R := ball_subset_ball hrR
  have hBp : 0<B := lt_of_lt_of_le zero_lt_one hB
  have hsmall : B*(L*r)≤1/2 := by
    have hh : r≤1/(4*B*(L+1)) := min_le_right _ _
    have hm := (le_div_iff₀ (by positivity : 0<4*B*(L+1))).mp hh
    nlinarith [mul_nonneg hBp.le hr.le]
  have hTR : (T : E →L[ℂ] E).comp (T.symm : E →L[ℂ] E)=ContinuousLinearMap.id ℂ E := by
    ext x
    exact T.apply_symm_apply x
  have hRT : (T.symm : E →L[ℂ] E).comp (T : E →L[ℂ] E)=ContinuousLinearMap.id ℂ E := by
    ext x
    exact T.symm_apply_apply x
  have hbij (x : E) (hx : x∈ball a r) : Function.Bijective (fderiv ℂ f x) := by
    have hxnorm : ‖a-x‖≤r := by
      rw [norm_sub_rev]
      exact (show ‖x-a‖<r by simpa only [mem_ball,dist_eq_norm] using hx).le
    have hdiff : ‖(T : E →L[ℂ] E)-fderiv ℂ f x‖≤L*r := by
      rw [hT]
      exact (hLip a (mem_ball_self hR) x (hsub hx)).trans
        (mul_le_mul_of_nonneg_left hxnorm hL)
    have hnear : ‖(T.symm : E →L[ℂ] E).comp ((T : E →L[ℂ] E)-fderiv ℂ f x)‖≤1/2 :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul hTB hdiff (norm_nonneg _) hBp.le).trans hsmall)
    obtain ⟨S,hDS,hSD,_⟩ := NLS.exists_inverse_norm_le_two_mul_of_composition_near
      (fderiv ℂ f x) (T : E →L[ℂ] E) (T.symm : E →L[ℂ] E) hTR hRT hnear
    exact ContinuousLinearMap.isUnit_iff_bijective.mp ⟨⟨fderiv ℂ f x,S,hDS,hSD⟩,rfl⟩
  exact exists_analytic_inverse_on_uniform_ball f a r B L hr hB hL (hf.mono hsub) T hT hTB
    (fun x hx y hy => hLip x (hsub hx) y (hsub hy)) hbij

end NLS.ComplexAnalysis
