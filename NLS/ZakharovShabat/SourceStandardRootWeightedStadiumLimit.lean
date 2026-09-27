import NLS.ZakharovShabat.SourceGapStadiumIntegralDecomposition

/-!
# The shrinking weighted standard-root stadium

The four-piece stadium decomposition combines the horizontal gap-side
limits with the vanishing endpoint arcs. Its limit is twice the upper
gap-side boundary integral, with the stadium's clockwise orientation.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The lower and upper selected-root boundary integrals differ by
sign on every noncollapsed gap. -/
theorem gapSideBoundaryIntegral_lower_eq_neg_upper
    (τ δ : ℂ) (g : ℂ → ℂ) (t : ℝ) (hδ : δ ≠ 0) :
    gapSideBoundaryIntegral τ δ g t false =
      -gapSideBoundaryIntegral τ δ g t true := by
  rw [gapSideBoundaryIntegral_eq_primitive τ δ g t hδ false,
    gapSideBoundaryIntegral_eq_primitive τ δ g t hδ true]
  simp [gapSidePrimitive]

/-- The weighted standard-root stadium splits into upper and lower
horizontal integrals and two outward endpoint-arc integrals. -/
theorem sourceStandardRoot_weighted_stadium_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (g : ℂ → ℂ) (ρ : ℝ)
    (hg : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      ContinuousAt g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    range (sourceGapStadiumPath l r ρ) ⊆
      sourceCanonicalRootDomain hp hp1 ψ →
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
  have hf : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      ContinuousAt f z := by
    intro z hz
    exact (hg z hz).div
      (sourceStandardRoot_analyticAt hp hp1 ψ n z (hz n)).continuousAt
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n))
  dsimp only
  intro hdom
  have hfour := sourceGapStadium_curveIntegral_fourPieces
    hp hp1 ψ n ρ f hf hdom
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

/-- As the stadium shrinks onto a real open gap, its weighted integral
converges to twice the upper boundary integral. -/
theorem sourceStandardRoot_weighted_stadium_curveIntegral_tendsto_two_upper
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
    (hglocal : AnalyticOnNhd ℂ g U)
    (hgdomain : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      ContinuousAt g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
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
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
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
  obtain ⟨ε,hε,hdom⟩ :=
    exists_sourceGapStadiumPath_range_subset_rootDomain hp hp1 ψ hreal n
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
    exact sourceStandardRoot_weighted_stadium_curveIntegral_eq
      hp hp1 ψ n g ρ hgdomain (hdom ρ ⟨hρ,hρε.le⟩)
  exact hsum.congr' heq.symm

end NLS.ZakharovShabat
