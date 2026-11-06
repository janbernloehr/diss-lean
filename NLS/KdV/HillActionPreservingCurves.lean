import NLS.KdV.HillMeanZeroActionTraceKernel
import NLS.KdV.HillOriginalMeanZeroSpectralDerivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Actual mean-zero L2 curves preserving all original Hill actions

The proved complete action-kernel theorem applies to the literal tangent
of every differentiable curve in the original real mean-zero L2 space.
Consequently every such action-preserving curve is genuinely isospectral
at all complex energies, including at collapsed gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The literal complex Fourier coefficients of the original real
mean-zero source, as a bounded REAL linear map. -/
def hillMeanZeroSourceCoeff : hillRealMeanZeroSourceSubmodule →L[ℝ] Coeff 2 :=
  (SpectralWeight.one.toCoeff.restrictScalars ℝ).comp
    (hillRealSourceSubmodule.subtypeL.comp hillRealMeanZeroSourceSubmodule.subtypeL)

/-- Every actual action-preserving real mean-zero L2 curve has zero
fixed-energy discriminant derivative, with no finite-gap hypothesis. -/
theorem hasDerivAt_hillDiscriminant_of_actions_constant
    (γ : ℝ → hillRealMeanZeroSourceSubmodule) (v : hillRealMeanZeroSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ v t)
    (hI : ∀ n : ℕ+, ∀ τ : ℝ,
      hillRealGapIntegral (γ τ).val.val (γ τ).val.property.1 (γ τ).val.property.2 n 0=
        hillRealGapIntegral (γ t).val.val (γ t).val.property.1 (γ t).val.property.2 n 0)
    (E : ℂ) :
    HasDerivAt (fun τ => hillL2Discriminant (hillMeanZeroSourceCoeff (γ τ)) E) 0 t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val.val,(γ t).val.property⟩
  let P := hillMeanZeroSourceCoeff
  have hc : Continuous (fun p : hillRealMeanZeroSourceSubmodule =>
      (⟨p.val.val,p.val.property⟩ : RealPeriodOneHillPotential)) :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hker (n : ℕ+) :
      (fderiv ℂ (hillRealSourceMoment q.val q.property.1 q.property.2 n 0)
        (SpectralWeight.one.toCoeff q.val)) (P v)=0 := by
    have ha := analyticAt_hillRealSourceMoment q.val q.property.1 q.property.2 n n.pos 0
    have hd := (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (P.hasFDerivAt.comp_hasDerivAt t hγ)
    obtain ⟨V,hV,hqV,hmatch⟩ := exists_hillRealSourceMoments_physical_neighborhood
      q.val q.property.1 q.property.2 n n.pos
    have hn := (hc.continuousAt.comp hγ.continuousAt).tendsto.eventually (hV.mem_nhds hqV)
    have he : (fun τ => hillRealSourceMoment q.val q.property.1 q.property.2 n 0 (P (γ τ)))
        =ᶠ[𝓝 t] (fun _ => (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ)) := by
      filter_upwards [hn] with τ hτ
      exact (hmatch _ hτ 0).trans (congrArg (fun r : ℝ => (r : ℂ)) (hI n τ))
    have hz := (hasDerivAt_const t (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ)).congr_of_eventuallyEq he
    exact hd.unique hz
  have hzero : P v 0=0 := by
    change SpectralWeight.one.toCoeff v.val.val 0=0
    rw [SpectralWeight.toCoeff_apply]
    exact (mem_hillRealMeanZeroSourceSubmodule v.val).mp v.property
  have hz := hillOriginalTrace_variation_zero_of_mean_zero_action_kernel q (P v)
    v.val.property.1 hzero hker E
  have ha : AnalyticAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (P (γ t)) :=
    (analyticOnNhd_hillL2Discriminant_joint (E,P (γ t)) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have hd := (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (P.hasFDerivAt.comp_hasDerivAt t hγ)
  change HasDerivAt (fun τ => hillL2Discriminant (P (γ τ)) E)
    ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (P (γ t))) (P v)) t at hd
  change (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (P (γ t))) (P v)=0 at hz
  rw [hz] at hd
  exact hd

/-- The complete ORIGINAL action sequence is constant along a real C1
curve only if the ACTUAL discriminant is constant at EVERY energy. -/
theorem hillDiscriminant_eq_on_action_preserving_curve
    (γ : ℝ → hillRealMeanZeroSourceSubmodule) (hγ : Differentiable ℝ γ)
    (hI : ∀ n : ℕ+, ∀ t : ℝ,
      hillRealGapIntegral (γ t).val.val (γ t).val.property.1 (γ t).val.property.2 n 0=
        hillRealGapIntegral (γ 0).val.val (γ 0).val.property.1 (γ 0).val.property.2 n 0)
    (E : ℂ) (t u : ℝ) :
    hillL2Discriminant (hillMeanZeroSourceCoeff (γ t)) E=
      hillL2Discriminant (hillMeanZeroSourceCoeff (γ u)) E := by
  have hd (τ : ℝ) := hasDerivAt_hillDiscriminant_of_actions_constant γ (deriv γ τ) τ
    (hγ τ).hasDerivAt (fun n s => (hI n s).trans (hI n τ).symm) E
  exact is_const_of_deriv_eq_zero (fun τ => (hd τ).differentiableAt) (fun τ => (hd τ).deriv) t u

end NLS.KdV
