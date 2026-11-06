import NLS.KdV.HillIntrinsicCartesianGardnerBracket
import NLS.KdV.HillSingleEndpointTransport

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.Poisson
namespace NLS.KdV

/-- The actual intrinsic normalized Cartesian bracket has zero derivative
along every genuine original indexed trajectory, at each open selected gap. -/
theorem hasDerivAt_hillIntrinsicNormalizedCartesianBracket_indexedCurve
    (n m k : ℕ+) (σ τ : Bool) (γ : ℝ → hillRealSourceSubmodule) (t : ℝ)
    (hγ : HasDerivAt γ (hillRealIndexedDiscriminantField k k.pos (γ t)) t)
    (hgapn : hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 m ≠ 0) :
    HasDerivAt (fun s => hillIntrinsicNormalizedCartesianBracket n m σ τ
      (⟨(γ s).val,(γ s).property⟩ : RealPeriodOneHillPotential)) 0 t := by
  let q : RealPeriodOneHillPotential := ⟨(γ t).val,(γ t).property⟩
  let F := hillSignedCartesianHminusGerm q n σ
  let G := hillSignedCartesianHminusGerm q m τ
  obtain ⟨hF,hFM⟩ := hillSignedCartesianHminusGerm_spec q n σ hgapn
  obtain ⟨hG,hGM⟩ := hillSignedCartesianHminusGerm_spec q m τ hgapm
  let D : PeriodOneHminusOne → ℂ := fun a => hminusGardnerBracket F G a/(F a*G a)
  have hB : AnalyticAt ℂ (hminusGardnerBracket F G) (hillOriginalHminusSource q.val) :=
    (gardnerBivector.analyticAt_bilinear _).comp₂
      ((hminusCotangentCLM.analyticAt _).comp hF.fderiv)
      ((hminusCotangentCLM.analyticAt _).comp hG.fderiv)
  have hFn : F (hillOriginalHminusSource q.val) ≠ 0 := by
    change hillSignedCartesianHminusGerm q n σ (hillOriginalHminusSource q.val) ≠ 0
    rw [hFM.self_of_nhds]
    exact hillSignedSpectralCartesian_ne_zero_open q n σ hgapn
  have hGn : G (hillOriginalHminusSource q.val) ≠ 0 := by
    change hillSignedCartesianHminusGerm q m τ (hillOriginalHminusSource q.val) ≠ 0
    rw [hGM.self_of_nhds]
    exact hillSignedSpectralCartesian_ne_zero_open q m τ hgapm
  have hD : AnalyticAt ℂ D (hillOriginalHminusSource q.val) := hB.div (hF.mul hG) (mul_ne_zero hFn hGn)
  let P : hillRealSourceSubmodule →L[ℝ] PeriodOneHminusOne :=
    (hillOriginalHminusSource.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hd := (hD.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
    (P.hasFDerivAt.comp_hasDerivAt t hγ)
  change HasDerivAt (fun s => D (hillOriginalHminusSource (γ s).val))
    ((fderiv ℂ D (hillOriginalHminusSource q.val))
      (hillOriginalHminusSource (hillIndexedDiscriminantHamiltonianSource q k k.pos))) t at hd
  rw [hillSignedCartesian_normalized_bracket_indexed_stationary q n m k σ τ
    hgapn hgapm F G hF hG hFM hGM] at hd
  have hM := hillIntrinsicNormalizedCartesianBracket_eventually_eq_germs q n m σ τ
    hgapn hgapm F G hF hG hFM hGM
  have hQ : Continuous (fun p : hillRealSourceSubmodule =>
      (⟨p.val,p.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  have he := (hQ.continuousAt.comp hγ.continuousAt).tendsto.eventually hM
  exact hd.congr_of_eventuallyEq he

/-- The representative-independent normalized ORIGINAL Gardner bracket
is constant on every complete indexed spectral trajectory. Only the
selected two gaps must be open at one time; the indexed gap may collapse. -/
theorem hillIntrinsicNormalizedCartesianBracket_eq_on_global_indexedCurve
    (n m k : ℕ+) (σ τ : Bool) (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k k.pos (γ t)) t)
    (u v : ℝ)
    (hgapn : hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 m ≠ 0) :
    hillIntrinsicNormalizedCartesianBracket n m σ τ ⟨(γ u).val,(γ u).property⟩ =
      hillIntrinsicNormalizedCartesianBracket n m σ τ ⟨(γ v).val,(γ v).property⟩ := by
  have hgap (j : ℕ+) (hj : hillRealGapHalfLength (γ u).val (γ u).property.1 (γ u).property.2 j ≠ 0) (t : ℝ) :
      hillRealGapHalfLength (γ t).val (γ t).property.1 (γ t).property.2 j ≠ 0 := by
    have he := hillPeriodicEndpoints_eq_on_global_indexedCurve j k j.pos k.pos γ hγ t u
    unfold hillRealGapHalfLength
    rw [he.1,he.2]
    exact hj
  have hd (t : ℝ) := hasDerivAt_hillIntrinsicNormalizedCartesianBracket_indexedCurve
    n m k σ τ γ t (hγ t) (hgap n hgapn t) (hgap m hgapm t)
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) u v

end NLS.KdV
