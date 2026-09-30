import NLS.ComplexAnalysis.CircleLogarithmicPrimitive

/-! # Differentiating an annular density's Cauchy transform

The density need only be analytic near the integrating circle. Its
Cauchy transform has the usual differentiated kernel throughout both
components of the circle complement.
-/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem hasDerivAt_circleCauchyTransform
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (sphere c R))
    (z : ℂ) (hz : z ∉ sphere c R) :
    HasDerivAt (circleCauchyTransform f c R)
      ((2*Real.pi*I : ℂ)⁻¹ * ∮ w in C(c,R), f w/(w-z)^2) z := by
  let D : Set (ℂ × ℂ) := {q | AnalyticAt ℂ f q.1 ∧ q.1 ≠ q.2}
  let G : ℂ × ℂ → ℂ := fun q => f q.1/(q.1-q.2)
  have hD : IsOpen D :=
    ((isOpen_analyticAt ℂ f).preimage continuous_fst).inter
      (isOpen_ne_fun continuous_fst continuous_snd)
  have hG : AnalyticOnNhd ℂ G D := by
    intro q hq
    exact (hq.1.comp analyticAt_fst).div (analyticAt_fst.sub analyticAt_snd)
      (sub_ne_zero.mpr hq.2)
  have hcircle : ∀ v ∈ (sphere c R)ᶜ, ∀ w ∈ sphere c R, (w,v) ∈ D := by
    intro v hv w hw
    exact ⟨hf w hw,fun he => by
      change w = v at he
      exact hv (he ▸ hw)⟩
  have hg (w : ℂ) (hw : w ∈ sphere c R) :
      HasDerivAt (fun v : ℂ => G (w,v)) (f w/(w-z)^2) z := by
    have hne : w-z ≠ 0 := sub_ne_zero.mpr (fun he => hz (he ▸ hw))
    convert (hasDerivAt_const z (f w)).fun_div ((hasDerivAt_id z).const_sub w) hne using 1 <;> try rfl
    simp only [id_eq,mul_neg,zero_mul,zero_sub,neg_neg,mul_one]
  exact (hasDerivAt_circleIntegral_parameter G D hD hG c R hR (sphere c R)ᶜ
    isClosed_sphere.isOpen_compl hcircle z hz _ hg).const_mul (2*Real.pi*I : ℂ)⁻¹

end NLS.ComplexAnalysis
