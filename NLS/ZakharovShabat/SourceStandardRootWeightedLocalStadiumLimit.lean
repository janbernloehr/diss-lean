import NLS.ZakharovShabat.SourceGapStadiumLocalIntegralDecomposition
import NLS.ZakharovShabat.SourceStandardRootWeightedStadiumLimit

/-!
# Shrinking weighted stadium with a local analytic numerator

The selected-root quotient is continuous along a sufficiently small
stadium when the numerator is analytic on a neighborhood of a filled
midpoint disc. The four-piece decomposition and its limit then use no
global continuity assumption on the numerator.
-/

noncomputable section
open Set Metric Filter Topology Complex MeasureTheory intervalIntegral
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted standard-root stadium splits into its four oriented
pieces when the numerator is analytic on a set containing the path. -/
theorem sourceStandardRoot_weighted_stadium_curveIntegral_eq_of_local_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (ρ : ℝ)
    (U : Set ℂ) (hg : AnalyticOnNhd ℂ g U) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    range (sourceGapStadiumPath l r ρ) ⊆
      sourceCanonicalRootDomain hp hp1 ψ →
    range (sourceGapStadiumPath l r ρ) ⊆ U →
    (∫ᶜ z in sourceGapStadiumPath l r ρ,
      holomorphicOneForm
        (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
      sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g ρ -
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g r ρ -
      sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g (-ρ) -
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g l (-ρ) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let f : ℂ → ℂ := fun w => g w / sourceStandardRoot hp hp1 ψ n w
  let D := sourceCanonicalRootDomain hp hp1 ψ ∩ U
  have hf : ∀ z ∈ D, ContinuousAt f z := by
    intro z hz
    exact ((hg z hz.2).div
      (sourceStandardRoot_analyticAt hp hp1 ψ n z (hz.1 n))
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz.1 n))).continuousAt
  dsimp only
  intro hroot hU
  have hdom : range (sourceGapStadiumPath l r ρ) ⊆ D :=
    fun z hz => ⟨hroot hz,hU hz⟩
  have hfour := sourceGapStadium_curveIntegral_fourPieces_on
    hp hp1 ψ n ρ f D hf hdom
  change (∫ᶜ z in sourceGapStadiumPath l r ρ,
    holomorphicOneForm f z) = _ at hfour
  rw [sourceStandardRoot_weighted_horizontalSegment_curveIntegral_eq
      hp hp1 ψ n g ρ,
    sourceStandardRoot_weighted_endpointArc_curveIntegral_eq
      hp hp1 ψ n g r ρ] at hfour
  have hle : l-(ρ:ℂ)*I = l+((-ρ:ℝ):ℂ)*I := by push_cast; ring
  have hre : r-(ρ:ℂ)*I = r+((-ρ:ℝ):ℂ)*I := by push_cast; ring
  rw [hle,hre,
    sourceStandardRoot_weighted_horizontalSegment_curveIntegral_eq
      hp hp1 ψ n g (-ρ),
    sourceStandardRoot_weighted_endpointArc_curveIntegral_eq
      hp hp1 ψ n g l (-ρ)] at hfour
  exact hfour

/-- The shrinking weighted stadium has the same gap-side limit with
only local analyticity on a neighborhood containing a midpoint disc. -/
theorem sourceStandardRoot_weighted_stadium_curveIntegral_tendsto_two_upper_of_local_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hglocal : AnalyticOnNhd ℂ g U) (R : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
    Tendsto (fun ρ : ℝ =>
      ∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm
          (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (2 * gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true)) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  dsimp only
  intro hR hUdisc
  change d < R at hR
  change closedBall c R ⊆ U at hUdisc
  have hlS : l ∈ standardRootGapSegment τ δ := by
    have hq : sourceCanonicalRootGapPoint hp hp1 ψ n (-1) ∈
        standardRootGapSegment τ δ := ⟨-1,by norm_num,rfl⟩
    simpa only [sourceCanonicalRootGapPoint_neg_one_eq_left] using hq
  have hrS : r ∈ standardRootGapSegment τ δ := by
    have hq : sourceCanonicalRootGapPoint hp hp1 ψ n 1 ∈
        standardRootGapSegment τ δ := ⟨1,by norm_num,rfl⟩
    simpa only [sourceCanonicalRootGapPoint_one_eq_right] using hq
  have hgl : ContinuousAt g l := (hglocal l (hgapU hlS)).continuousAt
  have hgr : ContinuousAt g r := (hglocal r (hgapU hrS)).continuousAt
  obtain ⟨ε₀,hε₀,hdom⟩ :=
    exists_sourceGapStadiumPath_range_subset_rootDomain hp hp1 ψ hreal n
  let ε := min ε₀ (R-d)
  have hε : 0 < ε := lt_min hε₀ (sub_pos.mpr hR)
  have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), 0 < ρ :=
    self_mem_nhdsWithin
  have hneg : Tendsto (fun ρ : ℝ => -ρ)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝[Set.Iio 0] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun ρ : ℝ => -ρ) 0 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [hpos] with ρ hρ
      exact neg_neg_of_pos hρ
  have hu := sourceStandardRoot_weighted_horizontalIntegral_tendsto_upper
    hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal
  have hl := (sourceStandardRoot_weighted_horizontalIntegral_tendsto_lower
    hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal).comp hneg
  have ha := sourceStandardRoot_weighted_outerArcIntegrals_tendsto_zero
    hp hp1 ψ hreal n hopen g hgl hgr
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hlow := gapSideBoundaryIntegral_lower_eq_neg_upper τ δ g 1 hδ
  have hsum : Tendsto (fun ρ : ℝ =>
      sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g ρ -
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g r ρ -
      sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g (-ρ) -
      sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g l (-ρ))
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (2 * gapSideBoundaryIntegral τ δ g 1 true)) := by
    have hraw := ((hu.sub ha.2).sub hl).sub ha.1
    simpa [l,r,τ,δ,Function.comp_def,hlow,two_mul] using hraw
  have heq : (fun ρ : ℝ =>
      ∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm
          (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z)
        =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)]
      (fun ρ : ℝ =>
        sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g ρ -
        sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g r ρ -
        sourceStandardRoot_weighted_horizontalIntegral hp hp1 ψ n g (-ρ) -
        sourceStandardRoot_weighted_endpointArcIntegral hp hp1 ψ n g l (-ρ)) := by
    filter_upwards [hpos,hsmall] with ρ hρ hρε
    have hρ₀ : ρ ∈ Ioc 0 ε₀ :=
      ⟨hρ,(le_of_lt hρε).trans (min_le_left _ _)⟩
    have hmargin : d+ρ ≤ R := by
      have hbound := (le_of_lt hρε).trans (min_le_right ε₀ (R-d))
      linarith
    have hdisc := sourceGapStadiumPath_range_subset_midpoint_closedBall
      hp hp1 ψ hreal n hopen ρ R hρ hmargin
    exact sourceStandardRoot_weighted_stadium_curveIntegral_eq_of_local_domain
      hp hp1 ψ n g ρ U hglocal (hdom ρ hρ₀)
        (fun z hz => hUdisc (hdisc hz))
  exact hsum.congr' heq.symm

end NLS.ZakharovShabat
