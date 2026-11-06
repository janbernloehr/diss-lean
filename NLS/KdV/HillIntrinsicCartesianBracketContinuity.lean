import NLS.KdV.HillIntrinsicCartesianGardnerBracket

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.Poisson
namespace NLS.KdV

/-- The intrinsic normalized ORIGINAL Cartesian bracket is continuous
in the original L2 topology at every open selected pair of gaps. -/
theorem continuousAt_hillIntrinsicNormalizedCartesianBracket
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0) :
    ContinuousAt (hillIntrinsicNormalizedCartesianBracket n m σ τ) q := by
  obtain ⟨F,hF,hFM⟩ := exists_hillSignedCartesian_hminus_physical_germ q n σ hgapn
  obtain ⟨G,hG,hGM⟩ := exists_hillSignedCartesian_hminus_physical_germ q m τ hgapm
  let D : PeriodOneHminusOne → ℂ := fun a => hminusGardnerBracket F G a/(F a*G a)
  have hB : AnalyticAt ℂ (hminusGardnerBracket F G) (hillOriginalHminusSource q.val) :=
    (gardnerBivector.analyticAt_bilinear _).comp₂
      ((hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  have hFn : F (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hFM.self_of_nhds]
    exact hillSignedSpectralCartesian_ne_zero_open q n σ hgapn
  have hGn : G (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hGM.self_of_nhds]
    exact hillSignedSpectralCartesian_ne_zero_open q m τ hgapm
  have hD : AnalyticAt ℂ D (hillOriginalHminusSource q.val) := hB.div (hF.mul hG) (mul_ne_zero hFn hGn)
  have hc : ContinuousAt (fun p : RealPeriodOneHillPotential => D (hillOriginalHminusSource p.val)) q :=
    hD.continuousAt.comp (f := fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
  have he := hillIntrinsicNormalizedCartesianBracket_eventually_eq_germs q n m σ τ
    hgapn hgapm F G hF hG hFM hGM
  exact hc.congr_of_eventuallyEq he

end NLS.KdV
