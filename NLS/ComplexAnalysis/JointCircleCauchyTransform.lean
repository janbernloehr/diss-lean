import NLS.ComplexAnalysis.CircleCauchyTransform

/-! # A jointly analytic filled quotient from its contour values

Cauchy reconstruction is jointly analytic in energy and Banach parameters
when the density is jointly analytic near the fixed circle. Only values on
that circle are used; any analytic interior filling is recovered exactly.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

def jointCircleCauchyTransform (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (t : ℂ × A) : ℂ :=
  circleCauchyTransform (fun w => F (w,t.2)) c R t.1

theorem analyticOnNhd_jointCircleCauchyTransform
    (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (V : Set A) (hV : IsOpen V)
    (hF : AnalyticOnNhd ℂ F (sphere c R ×ˢ V)) :
    AnalyticOnNhd ℂ (jointCircleCauchyTransform F c R) ((sphere c R)ᶜ ×ˢ V) := by
  let D : Set (ℂ × (ℂ × A)) :=
    {t | AnalyticAt ℂ F (t.1,t.2.2) ∧ t.1 ≠ t.2.1}
  have hD : IsOpen D :=
    ((isOpen_analyticAt ℂ F).preimage (by fun_prop)).inter
      (isOpen_ne_fun continuous_fst (continuous_fst.comp continuous_snd))
  let G : ℂ × (ℂ × A) → ℂ := fun t => F (t.1,t.2.2)/(t.1-t.2.1)
  have hG : AnalyticOnNhd ℂ G D := by
    intro t ht
    have ha : AnalyticAt ℂ (fun s : ℂ × (ℂ × A) => s.2.2) t :=
      (analyticAt_snd (p := t.2)).comp (analyticAt_snd (p := t))
    have hz : AnalyticAt ℂ (fun s : ℂ × (ℂ × A) => s.2.1) t :=
      (analyticAt_fst (p := t.2)).comp (analyticAt_snd (p := t))
    exact (ht.1.comp (f := fun s : ℂ × (ℂ × A) => (s.1,s.2.2))
      (analyticAt_fst.prod ha)).div
      (analyticAt_fst.sub hz) (sub_ne_zero.mpr ht.2)
  have hcircle : ∀ t ∈ (sphere c R)ᶜ ×ˢ V, ∀ w ∈ sphere c R, (w,t) ∈ D := by
    intro t ht w hw
    exact ⟨hF (w,t.2) ⟨hw,ht.2⟩,fun he => ht.1 (he ▸ hw)⟩
  have hi := analyticOnNhd_circleIntegral_of_jointAnalytic G hD hG c R hR
    (isClosed_sphere.isOpen_compl.prod hV) hcircle
  intro t ht
  exact analyticAt_const.mul (hi t ht)

omit [NormedAddCommGroup A] [NormedSpace ℂ A] in
/-- A boundary density determines every analytic interior filling. -/
theorem jointCircleCauchyTransform_eq_filling
    (F : ℂ × A → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (a : A) (Q : ℂ → ℂ) (hQ : AnalyticOnNhd ℂ Q (closedBall c R))
    (he : ∀ w ∈ sphere c R, F (w,a) = Q w)
    (z : ℂ) (hz : z ∈ ball c R) :
    jointCircleCauchyTransform F c R (z,a) = Q z := by
  have hi : (∮ w in C(c,R), F (w,a)/(w-z)) = (2*Real.pi*I : ℂ)*Q z := by
    calc
      _ = ∮ w in C(c,R), Q w/(w-z) := by
        apply circleIntegral.integral_congr hR.le
        intro w hw
        change F (w,a)/(w-z) = Q w/(w-z)
        rw [he w hw]
      _ = _ := by
        simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
          hQ.differentiableOn.circleIntegral_sub_inv_smul hz
  change (2*Real.pi*I : ℂ)⁻¹ * (∮ w in C(c,R), F (w,a)/(w-z)) = _
  rw [hi, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]

end NLS.ComplexAnalysis
