import NLS.ZakharovShabat.SourceAbelianRealBandValue
import NLS.ZakharovShabat.SourceAbelianLogChart
import NLS.ZakharovShabat.PeriodOneBoundaryInterlacing

/-! # Continuity and logarithm normalization as real sources vary

Inside a real spectral band the primitive has an explicit continuous
arcsine expression. Endpoint continuity keeps nearby real spectral and
source points in the same band. Consequently an anchored logarithm
chart agrees with the actual primitive for all nearby real sources.
-/
noncomputable section
open Set Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real spectral band is stable under small simultaneous changes
of its real coordinate and its source, at a real-source anchor. -/
theorem eventually_mem_sourceRealBand_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ n) :
    ∀ᶠ t : ℝ × CoeffPair p in 𝓝 (a,φ), t.1 ∈ sourceRealBand hp hp1 t.2 n := by
  have hl : ContinuousAt (fun t : ℝ × CoeffPair p =>
      (canonicalPeriodicRight hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) n).re) (a,φ) :=
    by
      have hc := (continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ hφ n).comp
        (f := fun t : ℝ × CoeffPair p => t.2) (continuous_snd.continuousAt (x := (a,φ)))
      simpa only [Function.comp_def] using! continuous_re.continuousAt.comp hc
  have hr : ContinuousAt (fun t : ℝ × CoeffPair p =>
      (canonicalPeriodicLeft hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) (n+1)).re) (a,φ) :=
    by
      have hc := (continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ hφ (n+1)).comp
        (f := fun t : ℝ × CoeffPair p => t.2) (continuous_snd.continuousAt (x := (a,φ)))
      simpa only [Function.comp_def] using! continuous_re.continuousAt.comp hc
  exact (hl.eventually_lt continuous_fst.continuousAt ha.1).and
    (continuous_fst.continuousAt.eventually_lt hr ha.2)

/-- Actual normalized values are jointly continuous in the real
spectral coordinate and the real-type source at every band point. -/
theorem continuousAt_sourceAbelianPrimitive_real_band
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ.val n) :
    ContinuousAt (fun t : ℝ × realTypeSourceSubmodule p =>
      sourceAbelianPrimitive hp hp1 t.2.val t.2.property (t.1 : ℂ)) (a,φ) := by
  have hm : Continuous (fun t : ℝ × realTypeSourceSubmodule p => (t.1,t.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hb : ∀ᶠ t : ℝ × realTypeSourceSubmodule p in 𝓝 (a,φ), t.1 ∈ sourceRealBand hp hp1 t.2.val n :=
    (hm.continuousAt (x := (a,φ))).tendsto.eventually (eventually_mem_sourceRealBand_joint hp hp1 φ.val φ.property n a ha)
  have hc : Continuous (fun t : ℝ × realTypeSourceSubmodule p =>
      sourceRealBandArcsinPrimitive hp t.2.val n t.1-I*(Real.pi : ℂ)/2-I*(Real.pi : ℂ)*n) := by
    exact (((continuous_sourceRealBandArcsinPrimitive_joint hp hp1 n).comp hm).sub continuous_const).sub continuous_const
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hb] with t ht
  exact sourceAbelianPrimitive_eq_arcsin_on_band hp hp1 t.2.val t.2.property n t.1 ht

/-- At a band anchor, a single neighborhood matches the logarithm
chart to the actual primitive for all nearby real sources, real
spectral coordinates, and signed normalization indices simultaneously. -/
theorem sourceAbelianLogChart_eventually_eq_nearby_real_sources
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (m : ℤ) (a : ℝ)
    (ha : a ∈ sourceRealBand hp hp1 φ.val m) :
    ∀ᶠ t : ℝ × realTypeSourceSubmodule p in 𝓝 (a,φ), ∀ n : ℤ,
      sourceAbelianLogChart hp hp1 φ.val φ.property (a : ℂ) n ((t.1 : ℂ),t.2.val) =
        sourceAbelianPrimitive hp hp1 t.2.val t.2.property (t.1 : ℂ)+I*(Real.pi : ℂ)*n := by
  let F : ℝ × realTypeSourceSubmodule p → ℂ := fun t => sourceAbelianPrimitive hp hp1 t.2.val t.2.property (t.1 : ℂ)
  let M : ℝ × realTypeSourceSubmodule p → ℂ := fun t => sourceFloquetMultiplier hp hp1 t.2.val (t.1 : ℂ)
  have hm : Continuous (fun t : ℝ × realTypeSourceSubmodule p => (t.1,t.2.val)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hb : ∀ᶠ t : ℝ × realTypeSourceSubmodule p in 𝓝 (a,φ), t.1 ∈ sourceRealBand hp hp1 t.2.val m :=
    (hm.continuousAt (x := (a,φ))).tendsto.eventually (eventually_mem_sourceRealBand_joint hp hp1 φ.val φ.property m a ha)
  have he : (fun t => exp (F t)) =ᶠ[𝓝 (a,φ)] M := by
    filter_upwards [hb] with t ht
    exact sourceAbelianPrimitive_exp hp hp1 t.2.val t.2.property (t.1 : ℂ)
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 t.2.val
        (sourceRealBand_subset_rootDomain hp hp1 t.2.val t.2.property m t.1 ht))
  have h := normalizedLogChart_eventually_eq M F (a,φ)
    (continuousAt_sourceAbelianPrimitive_real_band hp hp1 φ m a ha) he
  filter_upwards [h] with t ht
  intro n
  change F (a,φ)+log (M t/M (a,φ)) = F t at ht
  change (F (a,φ)+I*(Real.pi : ℂ)*n)+log (M t/M (a,φ)) = F t+I*(Real.pi : ℂ)*n
  linear_combination ht

end NLS.ZakharovShabat
