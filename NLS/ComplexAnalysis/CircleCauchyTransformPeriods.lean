import NLS.ComplexAnalysis.CircleCauchyTransform

/-!
# Periods of circle Cauchy transforms

Fubini exchanges the two contour integrals. The Cauchy transform has
the negative of its density's period on an enclosing circle and zero
period on a circle whose closed disc avoids the density circle. These
identities keep track of the individual holes in contour decomposition.
-/

noncomputable section
open Set Complex Metric
namespace NLS.ComplexAnalysis

private theorem circleIntegral_circleCauchyTransform_swap
    (f : ℂ → ℂ) (c d : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c r))
    (hsep : ∀ w ∈ sphere c r, ∀ z ∈ sphere d R, w ≠ z) :
    (∮ z in C(d,R), circleCauchyTransform f c r z) =
      (2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(c,r), f w*(∮ z in C(d,R), (w-z)⁻¹) := by
  have hjoint : ContinuousOn
      (Function.uncurry (fun z w : ℂ => f w/(w-z))) (sphere d R ×ˢ sphere c r) := by
    exact (hf.comp continuousOn_snd (fun _ h => h.2)).div
      (continuousOn_snd.sub continuousOn_fst)
      (fun t ht => sub_ne_zero.mpr (hsep t.2 ht.2 t.1 ht.1))
  simp only [circleCauchyTransform]
  rw [circleIntegral.integral_const_mul, NLS.CircleIntegral.swap hR hr hjoint]
  congr 1
  apply circleIntegral.integral_congr hr
  intro w _
  simp only [div_eq_mul_inv, circleIntegral.integral_const_mul]

/-- An enclosing circle receives the negative of the original density
period. The centers need not coincide. -/
theorem circleIntegral_circleCauchyTransform_of_enclosed
    (f : ℂ → ℂ) (c d : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c r)) (henclosed : sphere c r ⊆ ball d R) :
    (∮ z in C(d,R), circleCauchyTransform f c r z) = -(∮ w in C(c,r), f w) := by
  have hsep : ∀ w ∈ sphere c r, ∀ z ∈ sphere d R, w ≠ z := by
    intro w hw z hz he
    exact sphere_disjoint_ball.le_bot ⟨he ▸ hz, henclosed hw⟩
  rw [circleIntegral_circleCauchyTransform_swap f c d r R hr hR hf hsep]
  have hpole (w : ℂ) (hw : w ∈ sphere c r) :
      (∮ z in C(d,R), (w-z)⁻¹) = -(2*Real.pi*I : ℂ) := by
    have he : (fun z : ℂ => (w-z)⁻¹) = fun z => (-1 : ℂ)*(z-w)⁻¹ := by
      funext z
      rw [show w-z = -(z-w) by ring, inv_neg, neg_one_mul]
    rw [he, circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (henclosed hw), neg_one_mul]
  have heq : (∮ w in C(c,r), f w*(∮ z in C(d,R), (w-z)⁻¹)) =
      (∮ w in C(c,r), f w)*(-(2*Real.pi*I : ℂ)) := by
    calc
      _ = ∮ w in C(c,r), f w*(-(2*Real.pi*I : ℂ)) :=
        circleIntegral.integral_congr hr (fun w hw => by rw [hpole w hw])
      _ = _ := circleIntegral.integral_smul_const _ _ _ _
  rw [heq]
  have hπ : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  field_simp

/-- A circle whose closed disc avoids the density circle receives no
period from its Cauchy transform. -/
theorem circleIntegral_circleCauchyTransform_of_exterior
    (f : ℂ → ℂ) (c d : ℂ) (r R : ℝ) (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c r))
    (hexterior : ∀ w ∈ sphere c r, w ∉ closedBall d R) :
    (∮ z in C(d,R), circleCauchyTransform f c r z) = 0 := by
  have hsep : ∀ w ∈ sphere c r, ∀ z ∈ sphere d R, w ≠ z := by
    intro w hw z hz he
    exact hexterior w hw (he ▸ sphere_subset_closedBall hz)
  rw [circleIntegral_circleCauchyTransform_swap f c d r R hr hR hf hsep]
  have hpole (w : ℂ) (hw : w ∈ sphere c r) : (∮ z in C(d,R), (w-z)⁻¹) = 0 := by
    have he : (fun z : ℂ => (w-z)⁻¹) = fun z => (-1 : ℂ)*(z-w)⁻¹ := by
      funext z
      rw [show w-z = -(z-w) by ring, inv_neg, neg_one_mul]
    rw [he, circleIntegral.integral_const_mul,
      circleIntegral_inv_sub_eq_zero_of_notMem_closedBall d w R hR (hexterior w hw), mul_zero]
  have heq : (∮ w in C(c,r), f w*(∮ z in C(d,R), (w-z)⁻¹)) = 0 := by
    calc
      _ = ∮ _w in C(c,r), (0 : ℂ) :=
        circleIntegral.integral_congr hr (fun w hw => by rw [hpole w hw, mul_zero])
      _ = 0 := by simp [circleIntegral]
  rw [heq, mul_zero]

end NLS.ComplexAnalysis
