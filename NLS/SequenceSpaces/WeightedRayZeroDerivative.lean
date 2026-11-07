import NLS.SequenceSpaces.OperatorBasisExt
import NLS.ComplexAnalysis.ActionRayDerivative

/-! Exact scalar derivative normalization transfers between different
sequence norms through the ORIGINAL weighted positive coordinate rays.
No bounded inverse between the full Banach spaces is assumed. -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Coeff

theorem fderiv_zero_of_weighted_ray_agreement
    (F : Coeff 1 → Coeff 1) (H : Coeff 2 → Coeff 2)
    (hF : AnalyticAt ℂ F 0) (hH : AnalyticAt ℂ H 0)
    (w : ℤ → ℂ) (hw : ∀ j, w j≠0) (c : ℂ)
    (hdH : fderiv ℂ H 0=c • ContinuousLinearMap.id ℂ (Coeff 2))
    (he : ∀ i j : ℤ, ∀ t : ℝ, 0≤t →
      F ((t : ℂ) • lp.single 1 j 1) i=
        w i*H (((t : ℂ)/w j) • lp.single 2 j 1) i) :
    fderiv ℂ F 0=c • ContinuousLinearMap.id ℂ (Coeff 1) := by
  apply continuousLinearMap_eq_of_single (by norm_num)
  intro j
  ext i
  let E₁ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 i
  let E₂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i
  have hdF := (E₁.hasFDerivAt.comp 0 hF.differentiableAt.hasFDerivAt).fderiv
  have hdG := (E₂.hasFDerivAt.comp 0 hH.differentiableAt.hasFDerivAt).fderiv
  have hfrow : DifferentiableAt ℂ (fun a => F a i) 0 :=
    (E₁.differentiableAt.comp 0 hF.differentiableAt)
  have hgrow : DifferentiableAt ℂ (fun a => H a i) 0 :=
    (E₂.differentiableAt.comp 0 hH.differentiableAt)
  have hdf := NLS.ComplexAnalysis.hasDerivAt_comp_real_action_line
    (fun a => F a i) 0 (lp.single 1 j 1) hfrow
  have hdg := (NLS.ComplexAnalysis.hasDerivAt_comp_real_action_line
    (fun a => H a i) 0 ((w j)⁻¹ • lp.single 2 j 1) hgrow).const_mul (w i)
  change HasDerivAt (fun t : ℝ => F (0+(t : ℂ) • lp.single 1 j 1) i)
    ((fderiv ℂ (E₁ ∘ F) 0) (lp.single 1 j 1)) 0 at hdf
  rw [hdF] at hdf
  change HasDerivAt (fun t : ℝ => w i*H (0+(t : ℂ) • ((w j)⁻¹ • lp.single 2 j 1)) i)
    (w i*((fderiv ℂ (E₂ ∘ H) 0) ((w j)⁻¹ • lp.single 2 j 1))) 0 at hdg
  rw [hdG] at hdg
  have heR (t : ℝ) (ht : 0≤t) :
      F (0+(t : ℂ) • lp.single 1 j 1) i=
        w i*H (0+(t : ℂ) • ((w j)⁻¹ • lp.single 2 j 1)) i := by
    simpa only [zero_add,smul_smul,div_eq_mul_inv] using he i j t ht
  have hdeq : (fderiv ℂ F 0) (lp.single 1 j 1) i=
      w i*(fderiv ℂ H 0 ((w j)⁻¹ • lp.single 2 j 1)) i := by
    exact (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ hdf.hasDerivWithinAt
      (hdg.hasDerivWithinAt.congr (fun t ht => heR t ht) (heR 0 le_rfl))
  rw [hdH] at hdeq
  change (fderiv ℂ F 0) (lp.single 1 j 1) i=
    w i*(c*((w j)⁻¹*(lp.single (E := fun _ : ℤ => ℂ) 2 j 1) i)) at hdeq
  change (fderiv ℂ F 0) (lp.single 1 j 1) i=
    c*(lp.single (E := fun _ : ℤ => ℂ) 1 j 1) i
  by_cases hij : i=j
  · subst i
    simpa [lp.single_apply,hw j,mul_assoc,mul_comm,mul_left_comm] using hdeq
  · simpa [lp.single_apply,hij] using hdeq

end NLS.Coeff
