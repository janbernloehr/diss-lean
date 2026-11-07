import NLS.ZakharovShabat.SourceOpenGapReflection
import NLS.ZakharovShabat.SourceFullAbelianPrimitive

/-! Actual primitive reflection, fixed by the central endpoint
normalization rather than by a new logarithm branch. -/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {ψ : CoeffPair p}

theorem sourceAbelianHalfPlane_neg_mem (upper : Bool) (z : ℂ) :
    -z ∈ sourceAbelianHalfPlane (!upper) ↔ z ∈ sourceAbelianHalfPlane upper := by
  cases upper
  · change 0 < (-z).im ↔ z.im < 0
    rw [neg_im,neg_pos]
  · change (-z).im < 0 ↔ 0 < z.im
    rw [neg_im,neg_lt_zero]

theorem SourcePeriodicReflection.criticalRootRatio_neg
    (h : SourcePeriodicReflection hp hp1 ψ)
    (hD : ∀ z : ℂ, canonicalDiscriminant hp (periodOnePotential ψ) (-z)=
      canonicalDiscriminant hp (periodOnePotential ψ) z) (z : ℂ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (-z)/sourceCanonicalRoot hp hp1 ψ (-z)=
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z/sourceCanonicalRoot hp hp1 ψ z := by
  have hd (w : ℂ) := (analyticOnNhd_canonicalDiscriminant hp hp1 _
    (periodOnePotential_mem ψ) w (mem_univ _)).differentiableAt.hasDerivAt
  have hc := (hd (-z)).comp z ((hasDerivAt_id z).neg)
  have he : (fun w : ℂ => canonicalDiscriminant hp (periodOnePotential ψ) (-w))=
      canonicalDiscriminant hp (periodOnePotential ψ) := funext hD
  change HasDerivAt (fun w : ℂ => canonicalDiscriminant hp (periodOnePotential ψ) (-w)) _ z at hc
  rw [he] at hc
  have hder : deriv (canonicalDiscriminant hp (periodOnePotential ψ)) (-z)=
      -deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z := by
    have hh := hc.unique (hd z)
    linear_combination -hh
  rw [hder,h.canonicalRoot_neg z,neg_div,div_neg,neg_neg]

theorem sourceAbelianHalfPlanePrimitive_periodicReflection
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (h : SourcePeriodicReflection hp hp1 ψ)
    (hD : ∀ z : ℂ, canonicalDiscriminant hp (periodOnePotential ψ) (-z)=
      canonicalDiscriminant hp (periodOnePotential ψ) z) (upper : Bool) :
    EqOn (sourceAbelianHalfPlanePrimitive hp hp1 ψ hψ 0 upper)
      (fun z => -sourceAbelianHalfPlanePrimitive hp hp1 ψ hψ 0 (!upper) (-z))
      (sourceAbelianHalfPlane upper) := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0
  have ha : -a=canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) 0 := by
    simpa only [neg_zero] using (h 0).2.symm
  apply sourceAbelianHalfPlanePrimitive_eq_of_normalized hp hp1 ψ hψ 0 upper
  · intro z hz
    have hn := (sourceAbelianHalfPlane_neg_mem upper z).mpr hz
    have hd := (((sourceAbelianHalfPlanePrimitive_spec hp hp1 ψ hψ 0 (!upper)).1 (-z) hn).comp z
      ((hasDerivAt_id z).neg)).neg
    simpa only [Function.comp_def,Pi.neg_apply,h.criticalRootRatio_neg hD z,mul_neg_one,neg_neg] using! hd
  · have ht : Tendsto (fun z : ℂ => -z) (𝓝[sourceAbelianHalfPlane upper] a)
        (𝓝[sourceAbelianHalfPlane (!upper)] (-a)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (sourceAbelianHalfPlane_neg_mem upper z).mpr hz
    rw [ha] at ht
    simpa only [neg_zero,Function.comp_def] using
      (((sourceAbelianHalfPlanePrimitive_spec hp hp1 ψ hψ 0 (!upper)).2.2).comp ht).neg

theorem sourceFullAbelianPrimitive_zero_periodicReflection
    {W : Set (CoeffPair p)} (E : SourceAbelianSpectralChart hp hp1 W ψ)
    (hψ : IsRealType (CoeffPair.toMax p ψ)) (h : SourcePeriodicReflection hp hp1 ψ)
    (hD : ∀ z : ℂ, canonicalDiscriminant hp (periodOnePotential ψ) (-z)=
      canonicalDiscriminant hp (periodOnePotential ψ) z) (z : ℂ)
    (hz : z ∈ sourceOpenGapComplement hp hp1 ψ) :
    sourceFullAbelianPrimitive hp hp1 W 0 (-z,ψ) = -sourceFullAbelianPrimitive hp hp1 W 0 (z,ψ) := by
  let F : ℂ → ℂ := fun w => sourceFullAbelianPrimitive hp hp1 W 0 (w,ψ)
  have hhalf (upper : Bool) (w : ℂ) (hw : w ∈ sourceAbelianHalfPlane upper) :
      F (-w) = -F w := by
    have hwr := sourceAbelianHalfPlane_subset_rootDomain hp hp1 ψ hψ upper hw
    have hn := (sourceAbelianHalfPlane_neg_mem upper w).mpr hw
    have hnr := sourceAbelianHalfPlane_subset_rootDomain hp hp1 ψ hψ (!upper) hn
    have he (v : ℂ) (hv : v ∈ sourceCanonicalRootDomain hp hp1 ψ) :
        F v=sourceAbelianGlobalPrimitive hp hp1 ψ hψ v := by
      dsimp only [F]
      rw [sourceFullAbelianPrimitive_eq_real ⟨ψ,hψ⟩ E 0 v
        (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 ψ hv)]
      simp only [Int.cast_zero,mul_zero,add_zero]
      exact sourceAbelianPrimitive_eq_global hp hp1 ψ hψ hv
    rw [he w hwr,he (-w) hnr,
      sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 ψ hψ upper hw,
      sourceAbelianGlobalPrimitive_eq_halfPlane hp hp1 ψ hψ (!upper) hn]
    have hh := sourceAbelianHalfPlanePrimitive_periodicReflection hψ h hD upper hw
    dsimp only at hh
    linear_combination hh
  by_cases hu : 0 < z.im
  · exact hhalf true z hu
  by_cases hl : z.im < 0
  · exact hhalf false z hl
  have hi : z.im=0 := le_antisymm (le_of_not_gt hu) (le_of_not_gt hl)
  have hU := E.discs.isOpen_openGapComplement ψ E.source_mem
  have hzn := (h.neg_mem_openGapComplement_iff z).mpr hz
  exact eq_at_real_of_upperHalfPlane_extension (fun w => F (-w)) (fun w => -F w)
    (fun w => -F w) (sourceOpenGapComplement hp hp1 ψ)
    (sourceOpenGapComplement hp hp1 ψ) z hi hU hU hz hz
    (((sourceFullAbelianPrimitive_spectral_analytic E 0 (-z) hzn).comp
      (f := fun w : ℂ => -w) analyticAt_id.neg).continuousAt)
    ((sourceFullAbelianPrimitive_spectral_analytic E 0 z hz).neg.continuousAt)
    (fun w hw => hhalf true w hw.2) (fun _ _ => rfl)

end NLS.ZakharovShabat
