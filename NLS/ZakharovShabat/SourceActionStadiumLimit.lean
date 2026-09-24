import NLS.ZakharovShabat.SourceActionBoundaryGapSide

/-!
# The shrinking weighted action stadium

The weighted stadium integral splits into its upper and lower
horizontal pieces and its two outward endpoint arcs. The arcs vanish
and the horizontal terms tend to opposite gap-side boundary values.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The recentered weighted quotient is curve integrable on every
smooth path in the full canonical-root domain. -/
theorem sourceAction_curveIntegrable_of_smoothPath
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (q : ℂ)
    {a b : ℂ} (γ : Path a b)
    (hsmooth : ContDiffOn ℝ 1 γ.extend (Icc (0:ℝ) 1))
    (hdom : range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun z => (z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ))) γ := by
  let f : ℂ → ℂ := fun z => (z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hω : ContinuousOn (NLS.ComplexAnalysis.holomorphicOneForm f)
      (range γ) := by
    intro z hz
    have hq := (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
      (hdom hz)).continuousAt
    exact ((((continuousAt_id.sub continuousAt_const).mul hq).smul
      continuousAt_const)).continuousWithinAt
  exact hω.curveIntegrable_of_contDiffOn hsmooth (fun t => ⟨t,rfl⟩)

/-- The closed weighted stadium has the signed four-piece integral
decomposition determined by its clockwise orientation. -/
theorem sourceAction_stadium_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (q : ℂ) (ρ : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    range (sourceGapStadiumPath l r ρ) ⊆
      sourceCanonicalRootDomain hp hp1 ψ →
    (∫ᶜ z in sourceGapStadiumPath l r ρ,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => (w-q) * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z) =
      sourceAction_horizontalIntegral hp hp1 ψ n q ρ -
      sourceAction_endpointArcIntegral hp hp1 ψ q r ρ -
      sourceAction_horizontalIntegral hp hp1 ψ n q (-ρ) -
      sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  dsimp only
  intro hdom
  let f : ℂ → ℂ := fun z => (z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  let ω := NLS.ComplexAnalysis.holomorphicOneForm f
  let upper : Path (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I) :=
    Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)
  let right : Path (r+(ρ:ℂ)*I) (r-(ρ:ℂ)*I) :=
    (sourceEndpointSemicirclePath r ρ).symm
  let lower : Path (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I) :=
    Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)
  let left : Path (l-(ρ:ℂ)*I) (l+(ρ:ℂ)*I) :=
    (sourceLeftOuterArcPath l ρ).symm
  change range (((upper.trans right).trans lower).trans left) ⊆
    sourceCanonicalRootDomain hp hp1 ψ at hdom
  rw [Path.trans_range, Path.trans_range, Path.trans_range] at hdom
  have hudom : range upper ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    fun _ hz => hdom (Or.inl (Or.inl (Or.inl hz)))
  have hrdom : range right ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    fun _ hz => hdom (Or.inl (Or.inl (Or.inr hz)))
  have hldom : range lower ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    fun _ hz => hdom (Or.inl (Or.inr hz))
  have hleftdom : range left ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
    fun _ hz => hdom (Or.inr hz)
  have huInt : CurveIntegrable ω upper :=
    sourceAction_curveIntegrable_of_smoothPath hp hp1 ψ q upper
      (sourceSegmentPath_contDiffOn _ _) hudom
  have hlInt : CurveIntegrable ω lower :=
    sourceAction_curveIntegrable_of_smoothPath hp hp1 ψ q lower
      (sourceSegmentPath_contDiffOn _ _) hldom
  have hrBase : CurveIntegrable ω (sourceEndpointSemicirclePath r ρ) :=
    sourceAction_curveIntegrable_of_smoothPath hp hp1 ψ q _
      (sourceEndpointSemicirclePath_contDiffOn r ρ) (by
        change range ((sourceEndpointSemicirclePath r ρ).symm) ⊆
          sourceCanonicalRootDomain hp hp1 ψ at hrdom
        simpa only [Path.symm_range] using hrdom)
  have hrInt : CurveIntegrable ω right := hrBase.symm
  have hleftBase : CurveIntegrable ω (sourceEndpointSemicirclePath l (-ρ)) :=
    sourceAction_curveIntegrable_of_smoothPath hp hp1 ψ q _
      (sourceEndpointSemicirclePath_contDiffOn l (-ρ)) (by
        change range ((sourceLeftOuterArcPath l ρ).symm) ⊆
          sourceCanonicalRootDomain hp hp1 ψ at hleftdom
        rw [Path.symm_range] at hleftdom
        have hcast : range (sourceLeftOuterArcPath l ρ) =
            range (sourceEndpointSemicirclePath l (-ρ)) := by rfl
        rw [hcast] at hleftdom
        exact hleftdom)
  have hleftInt : CurveIntegrable ω left := by
    apply CurveIntegrable.symm
    exact hleftBase.cast (by push_cast; ring) (by push_cast; ring)
  calc
    (∫ᶜ z in sourceGapStadiumPath l r ρ, ω z) =
        (((∫ᶜ z in upper, ω z) +
          (∫ᶜ z in right, ω z)) +
          (∫ᶜ z in lower, ω z)) +
          (∫ᶜ z in left, ω z) := by
      change (∫ᶜ z in ((upper.trans right).trans lower).trans left, ω z) = _
      rw [curveIntegral_trans ((huInt.trans hrInt).trans hlInt) hleftInt,
        curveIntegral_trans (huInt.trans hrInt) hlInt,
        curveIntegral_trans huInt hrInt]
    _ = sourceAction_horizontalIntegral hp hp1 ψ n q ρ -
          sourceAction_endpointArcIntegral hp hp1 ψ q r ρ -
          sourceAction_horizontalIntegral hp hp1 ψ n q (-ρ) -
          sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ) := by
      have hu : (∫ᶜ z in upper, ω z) =
          sourceAction_horizontalIntegral hp hp1 ψ n q ρ :=
        sourceAction_horizontalSegment_curveIntegral_eq hp hp1 ψ n q ρ
      have hr : (∫ᶜ z in right, ω z) =
          -sourceAction_endpointArcIntegral hp hp1 ψ q r ρ := by
        change (∫ᶜ z in (sourceEndpointSemicirclePath r ρ).symm, ω z) = _
        rw [curveIntegral_symm,sourceAction_endpointArc_curveIntegral_eq]
      have hl : (∫ᶜ z in lower, ω z) =
          -sourceAction_horizontalIntegral hp hp1 ψ n q (-ρ) := by
        change (∫ᶜ z in Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I), ω z) = _
        rw [← Path.segment_symm (l-(ρ:ℂ)*I) (r-(ρ:ℂ)*I),
          curveIntegral_symm]
        have hle : l-(ρ:ℂ)*I = l+((-ρ:ℝ):ℂ)*I := by push_cast; ring
        have hre : r-(ρ:ℂ)*I = r+((-ρ:ℝ):ℂ)*I := by push_cast; ring
        rw [hle,hre]
        exact congrArg Neg.neg
          (sourceAction_horizontalSegment_curveIntegral_eq hp hp1 ψ n q (-ρ))
      have hleft : (∫ᶜ z in left, ω z) =
          -sourceAction_endpointArcIntegral hp hp1 ψ q l (-ρ) := by
        change (∫ᶜ z in (sourceLeftOuterArcPath l ρ).symm, ω z) = _
        rw [curveIntegral_symm]
        change -(∫ᶜ z in (sourceEndpointSemicirclePath l (-ρ)).cast _ _, ω z) = _
        rw [curveIntegral_cast,sourceAction_endpointArc_curveIntegral_eq]
      rw [hu,hr,hl,hleft]
      ring

/-- The weighted stadium integral tends to twice the upper gap-side
boundary value as its radius shrinks to zero. -/
theorem sourceAction_stadium_curveIntegral_tendsto_two_upper
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Tendsto (fun ρ : ℝ =>
      ∫ᶜ z in sourceGapStadiumPath l r ρ,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (w-(q:ℂ)) * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (2 * sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true)) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
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
  have hu := sourceAction_horizontalIntegral_tendsto_upper_boundary
    hp hp1 ψ hreal n hopen (q:ℂ)
  have hl := (sourceAction_horizontalIntegral_tendsto_lower_boundary
    hp hp1 ψ hreal n hopen (q:ℂ)).comp hneg
  have ha := sourceAction_outerArcIntegrals_tendsto_zero
    hp hp1 ψ hreal n hopen (q:ℂ)
  have hsum : Tendsto (fun ρ : ℝ =>
      sourceAction_horizontalIntegral hp hp1 ψ n (q:ℂ) ρ -
      sourceAction_endpointArcIntegral hp hp1 ψ (q:ℂ) r ρ -
      sourceAction_horizontalIntegral hp hp1 ψ n (q:ℂ) (-ρ) -
      sourceAction_endpointArcIntegral hp hp1 ψ (q:ℂ) l (-ρ))
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (2 * sourceAction_cosineBoundaryIntegral hp hp1 ψ n (q:ℂ) true)) := by
    have hraw := ((hu.sub ha.2).sub hl).sub ha.1
    have hlow := sourceAction_lower_cosineBoundaryIntegral_eq_neg_upper
      hp hp1 ψ hreal n hopen q
    simpa [l,r,Function.comp_def,hlow,two_mul] using hraw
  have heq : (fun ρ : ℝ =>
      ∫ᶜ z in sourceGapStadiumPath l r ρ,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => (w-(q:ℂ)) * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z)
        =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)]
      (fun ρ : ℝ =>
        sourceAction_horizontalIntegral hp hp1 ψ n (q:ℂ) ρ -
        sourceAction_endpointArcIntegral hp hp1 ψ (q:ℂ) r ρ -
        sourceAction_horizontalIntegral hp hp1 ψ n (q:ℂ) (-ρ) -
        sourceAction_endpointArcIntegral hp hp1 ψ (q:ℂ) l (-ρ)) := by
    filter_upwards [hpos,hsmall] with ρ hρ hρε
    exact sourceAction_stadium_curveIntegral_eq hp hp1 ψ n (q:ℂ) ρ
      (hdom ρ ⟨hρ,hρε.le⟩)
  exact hsum.congr' heq.symm

end NLS.ZakharovShabat
