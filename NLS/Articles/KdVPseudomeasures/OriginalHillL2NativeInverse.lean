import NLS.Articles.KdVPseudomeasures.OriginalHillL2NativeAnalytic
import NLS.Topology.LiftLocalInverseGerms

/-! True real-analytic local inverses for the ACTUAL map in the L2 and
signed positive-half Banach norms. The derivative-generator recovery
formula lifts the proved native local inverse in BOTH directions. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Explicit stronger-norm recovery of an actual native inverse branch. -/
def hillL2InverseRecovery (g : HillRealSignedTarget → HillRealMeanZeroSource)
    (z : HillRealSignedHalfTarget) : HillRealL2BanachSource :=
  hillL2SourceSpatialRecovery ((fderiv ℝ g (hillSignedHalfInclusion z)) (hillSignedHalfSpatialGenerator z))

theorem analyticAt_hillL2InverseRecovery (g : HillRealSignedTarget → HillRealMeanZeroSource)
    (z : HillRealSignedHalfTarget) (hg : AnalyticAt ℝ g (hillSignedHalfInclusion z)) :
    AnalyticAt ℝ (hillL2InverseRecovery g) z := by
  exact @NLS.FunctionalAnalysis.analyticAt_derivative_generator_recovery ℝ
    HillRealSignedTarget HillRealMeanZeroSource HillRealSignedHalfTarget HillRealL2BanachSource
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance g
    hillSignedHalfInclusion hillSignedHalfSpatialGenerator hillL2SourceSpatialRecovery z hg

theorem norm_hillL2InverseRecovery_le_DF (g : HillRealSignedTarget → HillRealMeanZeroSource)
    (z : HillRealSignedHalfTarget) :
    ‖hillL2InverseRecovery g z‖ ≤ 2*‖fderiv ℝ g (hillSignedHalfInclusion z)‖*‖z‖ := by
  have hd := @NLS.FunctionalAnalysis.norm_clm_apply_le_of_norm_le ℝ HillRealSignedTarget HillRealMeanZeroSource
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (fderiv ℝ g (hillSignedHalfInclusion z)) (hillSignedHalfSpatialGenerator z)
    ((2*Real.pi)*‖z‖) (norm_hillSignedHalfSpatialGenerator_le z)
  calc
    ‖hillL2InverseRecovery g z‖ ≤ (1/Real.pi)*
        ‖(fderiv ℝ g (hillSignedHalfInclusion z)) (hillSignedHalfSpatialGenerator z)‖ :=
      norm_hillL2SourceSpatialRecovery_le _
    _ ≤ (1/Real.pi)*(‖fderiv ℝ g (hillSignedHalfInclusion z)‖*((2*Real.pi)*‖z‖)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by field_simp

/-- ANY proved analytic left-inverse germ recovers the SAME original
source in the genuine L2 model from its actual positive-half output. -/
theorem hillL2InverseRecovery_inclusion_of_inverse_germ (q : HillRealMeanZeroSource)
    (g : HillRealSignedTarget → HillRealMeanZeroSource) (hg : AnalyticAt ℝ g (hillRealSignedMap q))
    (hleft : ∀ᶠ a in 𝓝 q, g (hillRealSignedMap a)=a)
    (z : HillRealSignedHalfTarget) (hz : hillSignedHalfInclusion z=hillRealSignedMap q) :
    hillL2SourceInclusion (hillL2InverseRecovery g z)=q := by
  let γ : ℝ → HillRealMeanZeroSource := fun t => hillRealSpatialTranslation t q
  let Z : ℝ → HillRealSignedTarget := fun t => hillRealSignedMap (γ t)
  have hzraw (k : ℤ) : z.val.val.val k=(hillRealSignedMap q).val.val.val k := by
    have h := congrArg (fun a : HillRealSignedTarget => a.val.val.val k) hz
    simpa only [hillSignedHalfInclusion_apply] using h
  have hδ (k : ℤ) : (hillSignedHalfSpatialGenerator z).val.val.val k=
      I*((2*Real.pi*k:ℝ):ℂ)*(hillRealSignedMap q).val.val.val k := by
    rw [hillSignedHalfSpatialGenerator_apply,hzraw]
  have hZ : HasDerivAt Z (hillSignedHalfSpatialGenerator z) 0 :=
    WeightedCoeff.hasDerivAt_fourierRealZero_spatialCurve (Weight.signedSobolev (-1/2))
      (Weight.signedSobolev_neg (-1/2)) (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      (hillRealSignedMap q) _ hδ Z (fun t k => hillRealSignedMap_spatialTranslation_apply q t k)
  have hgZ : DifferentiableAt ℝ g (Z 0) := by
    simpa only [Z,γ,hillRealSpatialTranslation_zero] using hg.differentiableAt
  have hd := @NLS.FunctionalAnalysis.hasDerivAt_differentiable_comp HillRealSignedTarget HillRealMeanZeroSource
    inferInstance inferInstance inferInstance inferInstance g Z (hillSignedHalfSpatialGenerator z) 0 hgZ hZ
  simp only [Z,γ,hillRealSpatialTranslation_zero] at hd
  let v := (fderiv ℝ g (hillRealSignedMap q)) (hillSignedHalfSpatialGenerator z)
  change HasDerivAt (fun t => g (hillRealSignedMap (γ t))) v 0 at hd
  have hcont : Tendsto γ (𝓝 (0:ℝ)) (𝓝 q) := by
    simpa only [γ,hillRealSpatialTranslation_zero] using
      ((continuous_hillRealSpatialTranslation_orbit q).continuousAt (x:=0)).tendsto
  have heq : (fun t => g (hillRealSignedMap (γ t))) =ᶠ[𝓝 (0:ℝ)] γ := hcont.eventually hleft
  have hsource : HasDerivAt γ v 0 := heq.hasDerivAt_iff.mp hd
  have hγ (t : ℝ) (k : ℤ) : (γ t).val.val.val k=
      exp (((t*(2*Real.pi*k):ℝ):ℂ)*I)*q.val.val.val k := by
    change (hillRealMeanZeroInclusion (hillRealSpatialTranslation t q)).val k= _
    rw [hillRealSpatialTranslation_inclusion,WeightedCoeff.spatialTranslation_apply]
    rfl
  have hv := WeightedCoeff.fourierRealZero_spatialGenerator_of_hasDerivAt (Weight.sobolev (-1)) q v γ hγ hsource
  unfold hillL2InverseRecovery
  rw [hz]
  exact hillL2SourceInclusion_recovery_eq q v hv

/-- The lifted analytic inverse branch agrees with the SAME actual native
inverse branch near the original positive-half output. -/
theorem hillL2InverseRecovery_eventually_inclusion (u : HillRealL2BanachSource)
    (g : HillRealSignedTarget → HillRealMeanZeroSource)
    (hga : AnalyticAt ℝ g (hillRealSignedMap (hillL2SourceInclusion u)))
    (hgval : g (hillRealSignedMap (hillL2SourceInclusion u))=hillL2SourceInclusion u)
    (hleft : ∀ᶠ a in 𝓝 (hillL2SourceInclusion u), g (hillRealSignedMap a)=a)
    (hright : ∀ᶠ z in 𝓝 (hillRealSignedMap (hillL2SourceInclusion u)), hillRealSignedMap (g z)=z) :
    ∀ᶠ z in 𝓝 (hillL2NativeMap u),
      hillL2SourceInclusion (hillL2InverseRecovery g z)=g (hillSignedHalfInclusion z) := by
  let q := hillL2SourceInclusion u
  let z₀ := hillL2NativeMap u
  have ht₀ : hillSignedHalfInclusion z₀=hillRealSignedMap q := hillL2NativeMap_inclusion u
  obtain ⟨U,hUsub,hUopen,hqU⟩ := mem_nhds_iff.mp hleft
  have hT : Tendsto hillSignedHalfInclusion (𝓝 z₀) (𝓝 (hillRealSignedMap q)) := by
    simpa only [ht₀] using (hillSignedHalfInclusion.continuous.continuousAt (x:=z₀)).tendsto
  have hgT : Tendsto (fun z => g (hillSignedHalfInclusion z)) (𝓝 z₀) (𝓝 q) := by
    have h := hga.continuousAt.tendsto.comp hT
    rw [hgval] at h
    convert h using 1; rfl
  filter_upwards [hT.eventually hright,hT.eventually hga.eventually_analyticAt,
    hgT.eventually (hUopen.mem_nhds hqU)] with z hz hgZ hgzU
  have hl : ∀ᶠ a in 𝓝 (g (hillSignedHalfInclusion z)), g (hillRealSignedMap a)=a := by
    have hmem : ∀ᶠ a in 𝓝 (g (hillSignedHalfInclusion z)), a ∈ U := hUopen.mem_nhds hgzU
    filter_upwards [hmem] with a ha
    exact hUsub ha
  exact hillL2InverseRecovery_inclusion_of_inverse_germ (g (hillSignedHalfInclusion z)) g
    (by rw [hz]; exact hgZ) hl z hz.symm

/-- BOTH local inverse identities hold in the TRUE L2 and positive-half
Banach topologies at EVERY actual L2 source. -/
theorem exists_hillL2NativeMap_localInverse (u : HillRealL2BanachSource) :
    ∃ G : HillRealSignedHalfTarget → HillRealL2BanachSource,
      AnalyticAt ℝ G (hillL2NativeMap u) ∧ G (hillL2NativeMap u)=u ∧
      (∀ᶠ a in 𝓝 u, G (hillL2NativeMap a)=a) ∧
      (∀ᶠ z in 𝓝 (hillL2NativeMap u), hillL2NativeMap (G z)=z) := by
  let q := hillL2SourceInclusion u
  let z₀ := hillL2NativeMap u
  obtain ⟨g,hga,hgval,hleft,hright,_⟩ := hillPhysicalNativeMap_localInverse q
  let G := hillL2InverseRecovery g
  have ht₀ : hillSignedHalfInclusion z₀=hillRealSignedMap q := hillL2NativeMap_inclusion u
  have hG : AnalyticAt ℝ G z₀ := analyticAt_hillL2InverseRecovery g z₀ (by rw [ht₀]; exact hga)
  have hgood : ∀ᶠ z in 𝓝 z₀, hillL2SourceInclusion (G z)=g (hillSignedHalfInclusion z) :=
    hillL2InverseRecovery_eventually_inclusion u g hga hgval hleft hright
  obtain ⟨hpoint,hl,hr⟩ := NLS.Topology.lift_two_sided_inverse_germs hillRealSignedMap g hillL2NativeMap G
    hillL2SourceInclusion hillSignedHalfInclusion hillL2SourceInclusion.continuous hillSignedHalfInclusion.continuous
    hillL2SourceInclusion_injective hillSignedHalfInclusion_injective hillL2NativeMap_inclusion u
    (analyticAt_hillL2NativeMap u).continuousAt hgood hleft hright
  exact ⟨G,hG,hpoint,hl,hr⟩

end NLS.Articles.KdVPseudomeasures
