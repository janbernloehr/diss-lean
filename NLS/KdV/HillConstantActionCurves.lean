import NLS.KdV.HillHminusActionTraceStationarity
import NLS.KdV.HillOriginalSequencePhysicalDifferential
import NLS.KdV.HillOriginalMeanZeroSpectralDerivative

/-! # Discriminant constancy along actual physical constant-action curves -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The full kernel of the original actions annihilates every fixed-energy
rough trace derivative on actual even mean-zero physical directions. -/
theorem hillHminusTrace_variation_zero_of_original_action_germ_kernel
    (q : RealPeriodOneHillPotential) (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h ∈ Coeff.paritySubspace 0)
    (hzero : h.val 0 = 0)
    (A : ℕ+ → PeriodOneHminusOne → ℂ)
    (hA : ∀ n, AnalyticAt ℂ (A n) (hillOriginalHminusSource q.val))
    (hAM : ∀ n : ℕ+, ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      A n (hillOriginalHminusSource p.val) =
        (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ))
    (hker : ∀ n, fderiv ℂ (A n) (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource h) = 0) (E : ℂ) :
    fderiv ℂ (fun a => hillHminusDiscriminant a E) (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource h) = 0 := by
  have hk (n : ℕ+) :
      fderiv ℂ (hillRealSourceMoment q.val q.property.1 q.property.2 n 0)
        (SpectralWeight.one.toCoeff q.val) (SpectralWeight.one.toCoeff h) = 0 := by
    rw [hillRealSourceMoment_gradient q.val q.property.1 q.property.2 n n.pos 0]
    rw [←hillOriginalAction_hminus_fderiv_original q n (A n) (hA n) (hAM n) h heven]
    exact hker n
  have ht := hillOriginalTrace_variation_zero_of_mean_zero_action_kernel q
    (SpectralWeight.one.toCoeff h) heven (by simpa only [SpectralWeight.toCoeff_apply] using hzero) hk E
  rw [hillHminusPhysicalGerm_fderiv_original q
    (fun a => hillHminusDiscriminant a E) (fun a => hillL2Discriminant a E)
    (analyticAt_hillHminusDiscriminant_source _ E)
    ((analyticOnNhd_hillL2Discriminant_joint (E,SpectralWeight.one.toCoeff q.val) (mem_univ _)).comp
      (f := fun a : Coeff 2 => (E,a)) (analyticAt_const.prod analyticAt_id))
    (Eventually.of_forall fun p => hillHminusDiscriminant_original_source_agreement p.val p.property.1 E)
    h heven]
  exact ht

/-- Every differentiable actual physical curve with constant Hill actions
has zero trace derivative at every complex energy. -/
theorem hillOriginalTrace_derivative_zero_on_constant_action_curve
    (γ : ℝ → hillRealMeanZeroSourceSubmodule) (t : ℝ)
    (hγ : DifferentiableAt ℝ γ t)
    (hact : ∀ n : ℕ+, ∀ s : ℝ,
      hillRealGapIntegral (γ s).val.val (γ s).val.property.1 (γ s).val.property.2 n 0 =
      hillRealGapIntegral (γ t).val.val (γ t).val.property.1 (γ t).val.property.2 n 0)
    (E : ℂ) :
    HasDerivAt (fun s => hillHminusDiscriminant (hillOriginalHminusSource (γ s).val.val) E) 0 t := by
  let Q : RealPeriodOneHillPotential := ⟨(γ t).val.val,(γ t).val.property⟩
  let L : hillRealMeanZeroSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    hillOriginalRealHminusInclusion.comp hillRealMeanZeroSourceSubmodule.subtypeL
  let v := deriv γ t
  have hdγ : HasDerivAt γ v t := hγ.hasDerivAt
  have hdsource : HasDerivAt (fun s => L (γ s)) (L v) t :=
    L.hasFDerivAt.comp_hasDerivAt t hdγ
  choose A hA hAM using exists_hillOriginal_action_hminus_physical_germ Q
  have hker (n : ℕ+) :
      fderiv ℂ (A n) (hillOriginalHminusSource Q.val) (hillOriginalHminusSource v.val.val) = 0 := by
    have hd := ((hA n).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hdsource
    let V : hillRealMeanZeroSourceSubmodule →L[ℝ] WeightedCoeff SpectralWeight.one.toWeight 2 :=
      hillRealSourceSubmodule.subtypeL.comp hillRealMeanZeroSourceSubmodule.subtypeL
    have hc : ContinuousAt (fun s : ℝ =>
        (⟨(γ s).val.val,(γ s).val.property⟩ : RealPeriodOneHillPotential)) t :=
      tendsto_subtype_rng.mpr (V.continuous.continuousAt.comp hγ.continuousAt)
    have he : (fun s => A n (L (γ s))) =ᶠ[𝓝 t]
        (fun _ => (hillRealGapIntegral Q.val Q.property.1 Q.property.2 n 0 : ℂ)) := by
      filter_upwards [hc.tendsto.eventually (hAM n)] with s hs
      exact hs.trans (congrArg Complex.ofReal (hact n s))
    have hzero := (hasDerivAt_const t
      (hillRealGapIntegral Q.val Q.property.1 Q.property.2 n 0 : ℂ)).congr_of_eventuallyEq he
    exact hd.unique hzero
  have ht := hillHminusTrace_variation_zero_of_original_action_germ_kernel Q v.val.val
    v.val.property.1 ((mem_hillRealMeanZeroSourceSubmodule v.val).mp v.property)
    A hA hAM hker E
  have hd := ((analyticAt_hillHminusDiscriminant_source (L (γ t)) E).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hdsource
  change HasDerivAt (fun s => hillHminusDiscriminant (hillOriginalHminusSource (γ s).val.val) E)
    ((fderiv ℂ (fun a => hillHminusDiscriminant a E) (L (γ t))) (L v)) t at hd
  rwa [show fderiv ℂ (fun a => hillHminusDiscriminant a E) (L (γ t)) (L v) = 0 from ht] at hd

/-- The entire Hill discriminant is constant on every differentiable real
mean-zero original L2 curve preserving all original actions. -/
theorem hillOriginalTrace_eq_on_constant_action_curve
    (γ : ℝ → hillRealMeanZeroSourceSubmodule) (hγ : Differentiable ℝ γ)
    (hact : ∀ n : ℕ+, ∀ s : ℝ,
      hillRealGapIntegral (γ s).val.val (γ s).val.property.1 (γ s).val.property.2 n 0 =
      hillRealGapIntegral (γ 0).val.val (γ 0).val.property.1 (γ 0).val.property.2 n 0)
    (t : ℝ) (E : ℂ) :
    hillHminusDiscriminant (hillOriginalHminusSource (γ t).val.val) E =
      hillHminusDiscriminant (hillOriginalHminusSource (γ 0).val.val) E := by
  have hd (s : ℝ) := hillOriginalTrace_derivative_zero_on_constant_action_curve γ s
    (hγ s) (fun n r => (hact n r).trans (hact n s).symm) E
  exact is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0

end NLS.KdV
