import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumPath
import NLS.ZakharovShabat.SourceCriticalRootRatioHorizontalLimit
import NLS.ComplexAnalysis.HolomorphicCurveHomotopy

/-!
# Curve integrals of the shrinking gap stadium

The bundled semicircle and straight-segment paths must be identified
with the parameterized integrals used in the shrinking-contour bounds.
This also fixes the orientation signs of the four pieces.
-/

noncomputable section
open Set Filter Topology Complex MeasureTheory intervalIntegral
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The curve integral over an endpoint semicircle equals its angle
integral. The path uses a linear change from the unit interval to
`[-π/2, π/2]`. -/
theorem curveIntegral_sourceEndpointSemicirclePath
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∫ᶜ z in sourceEndpointSemicirclePath c R,
      NLS.ComplexAnalysis.holomorphicOneForm f z) =
      ∫ θ in (-(Real.pi/2))..(Real.pi/2),
        deriv (circleMap c R) θ * f (circleMap c R θ) := by
  let a : ℝ := -(Real.pi/2)
  let q : ℝ := Real.pi
  let g : ℝ → ℂ := fun θ =>
    deriv (circleMap c R) θ * f (circleMap c R θ)
  have hpath (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      (sourceEndpointSemicirclePath c R).extend t =
        circleMap c R (a+q*t) := by
    rw [(sourceEndpointSemicirclePath c R).extend_apply
      (show t ∈ (Icc 0 1 : Set ℝ) from ⟨ht.1.le,ht.2.le⟩)]
    rfl
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      deriv (sourceEndpointSemicirclePath c R).extend t =
        q • deriv (circleMap c R) (a+q*t) := by
    have hEq : (sourceEndpointSemicirclePath c R).extend =ᶠ[nhds t]
        (fun x : ℝ => circleMap c R (a+q*x)) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) (fun x hx => hpath x hx)
    rw [hEq.deriv_eq]
    have h := (hasDerivAt_circleMap c R (a+q*t)).scomp t
      ((hasDerivAt_const_mul q).const_add a)
    simpa [Function.comp_def, deriv_circleMap, smul_eq_mul, mul_comm] using h.deriv
  calc
    (∫ᶜ z in sourceEndpointSemicirclePath c R,
      NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ t in (0:ℝ)..1, q • g (a+q*t) := by
      rw [curveIntegral_eq_intervalIntegral_deriv]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      simp only [NLS.ComplexAnalysis.holomorphicOneForm_apply]
      rw [hpath t ht, hderiv t ht]
      dsimp [g]
      simp [mul_comm, mul_left_comm]
    _ = q • ∫ t in (0:ℝ)..1, g (q*t+a) := by
      rw [intervalIntegral.integral_smul]
      simp_rw [add_comm a]
    _ = ∫ u in (0:ℝ)..q, g (u+a) := by
      simpa only [mul_zero,mul_one] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := fun u => g (u+a)) (a := 0) (b := 1) q)
    _ = ∫ θ in a..q+a, g θ := by
      simpa only [zero_add] using
        (intervalIntegral.integral_comp_add_right
          (f := g) (a := 0) (b := q) a)
    _ = ∫ θ in (-(Real.pi/2))..(Real.pi/2),
          deriv (circleMap c R) θ * f (circleMap c R θ) := by
      have hendpoint : q+a = Real.pi/2 := by dsimp [q,a]; ring
      rw [hendpoint]

/-- For the critical-root quotient, the bundled semicircle integral
is exactly the previously bounded endpoint-arc integral. -/
theorem sourceCriticalRootRatio_endpointArc_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (c : ℂ) (R : ℝ) :
    (∫ᶜ z in sourceEndpointSemicirclePath c R,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ c R := by
  exact curveIntegral_sourceEndpointSemicirclePath _ c R

/-- The straight path between the vertically shifted endpoints has the
same integral as the signed gap coordinate, including its affine
Jacobian. -/
theorem curveIntegral_sourceGapHorizontalSegment
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (y : ℝ) (f : ℂ → ℂ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    (∫ᶜ z in Path.segment (l+(y:ℂ)*I) (r+(y:ℂ)*I),
      NLS.ComplexAnalysis.holomorphicOneForm f z) =
      ∫ t in (-1:ℝ)..1,
        f (sourceCanonicalRootGapPoint hp hp1 ψ n t+(y:ℂ)*I) *
          sourceStandardRootHalfGap hp hp1 ψ n := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let g : ℝ → ℂ := fun t =>
    f (sourceCanonicalRootGapPoint hp hp1 ψ n t+(y:ℂ)*I)*δ
  have hgap : r-l = 2*δ := by
    dsimp [l,r,δ,sourceStandardRootHalfGap,canonicalPeriodicGap]
    ring
  have hpath (t : ℝ) :
      AffineMap.lineMap (l+(y:ℂ)*I) (r+(y:ℂ)*I) t =
        sourceCanonicalRootGapPoint hp hp1 ψ n (2*t-1)+(y:ℂ)*I := by
    rw [AffineMap.lineMap_apply_module']
    change t • ((r+(y:ℂ)*I)-(l+(y:ℂ)*I)) + (l+(y:ℂ)*I) =
      (l+r)/2 + (r-l)/2 * ((2*t-1:ℝ):ℂ) + (y:ℂ)*I
    simp only [Complex.real_smul]
    push_cast
    ring
  calc
    (∫ᶜ z in Path.segment (l+(y:ℂ)*I) (r+(y:ℂ)*I),
      NLS.ComplexAnalysis.holomorphicOneForm f z) =
        ∫ t in (0:ℝ)..1,
          f (AffineMap.lineMap (l+(y:ℂ)*I) (r+(y:ℂ)*I) t) * (r-l) := by
      rw [curveIntegral_segment]
      apply intervalIntegral.integral_congr
      intro t _
      simp [NLS.ComplexAnalysis.holomorphicOneForm_apply]
    _ = ∫ t in (0:ℝ)..1, (2:ℝ) • g (2*t-1) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [hpath t,hgap]
      dsimp [g]
      ring
    _ = ∫ t in (-1:ℝ)..1, g t := by
      have h := intervalIntegral.smul_integral_comp_mul_add
        (f := g) (a := 0) (b := 1) (2:ℝ) (-1:ℝ)
      have hendpoint : (2:ℝ)*1+(-1)=1 := by norm_num
      simpa only [sub_eq_add_neg, intervalIntegral.integral_smul,
        mul_zero, zero_add, hendpoint] using h
    _ = _ := rfl

/-- The critical-root quotient on the upper and lower horizontal
segment paths is exactly the previously studied horizontal integral. -/
theorem sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (y : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    (∫ᶜ z in Path.segment (l+(y:ℂ)*I) (r+(y:ℂ)*I),
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y := by
  exact curveIntegral_sourceGapHorizontalSegment hp hp1 ψ n y _

/-- The endpoint semicircle path is smooth relative to the unit
interval, including its endpoints. -/
theorem sourceEndpointSemicirclePath_contDiffOn
    (c : ℂ) (R : ℝ) :
    ContDiffOn ℝ 1 (sourceEndpointSemicirclePath c R).extend
      (Icc (0:ℝ) 1) := by
  have hsmooth : ContDiff ℝ 1
      (fun t : ℝ => circleMap c R (-(Real.pi/2)+Real.pi*t)) := by
    exact (contDiff_circleMap c R).comp (by fun_prop)
  apply hsmooth.contDiffOn.congr
  intro t ht
  rw [(sourceEndpointSemicirclePath c R).extend_apply ht]
  rfl

/-- A straight segment path is smooth relative to the unit interval. -/
theorem sourceSegmentPath_contDiffOn (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend
      (Icc (0:ℝ) 1) := by
  have hsmooth : ContDiff ℝ 1
      (fun t : ℝ => AffineMap.lineMap a b t) :=
    AffineMap.contDiff_lineMap a b
  apply hsmooth.contDiffOn.congr
  intro t ht
  rw [(Path.segment a b).extend_apply ht]
  rfl

/-- A smooth path contained in the full root domain carries an
integrable critical-root quotient one-form. -/
theorem sourceCriticalRootRatio_curveIntegrable_of_smoothPath
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    {a b : ℂ} (γ : Path a b)
    (hsmooth : ContDiffOn ℝ 1 γ.extend (Icc (0:ℝ) 1))
    (hdom : range γ ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    CurveIntegrable
      (NLS.ComplexAnalysis.holomorphicOneForm
        (fun z => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
          sourceCanonicalRoot hp hp1 ψ z)) γ := by
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  have hω : ContinuousOn (NLS.ComplexAnalysis.holomorphicOneForm f)
      (range γ) := by
    intro z hz
    exact (((sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z
      (hdom hz)).continuousAt).smul continuousAt_const).continuousWithinAt
  exact hω.curveIntegrable_of_contDiffOn hsmooth (fun t => ⟨t,rfl⟩)

/-- The critical-root quotient integral over the closed stadium is the
signed sum of its upper and lower horizontal integrals and its two
outward semicircle integrals. -/
theorem sourceCriticalRootRatio_stadium_curveIntegral_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (ρ : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    (range (sourceGapStadiumPath l r ρ) ⊆
      sourceCanonicalRootDomain hp hp1 ψ) →
    (∫ᶜ z in sourceGapStadiumPath l r ρ,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n ρ -
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ -
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-ρ) -
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  dsimp only
  intro hdom
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
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
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ upper
      (sourceSegmentPath_contDiffOn _ _) hudom
  have hlInt : CurveIntegrable ω lower :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ lower
      (sourceSegmentPath_contDiffOn _ _) hldom
  have hrBase : CurveIntegrable ω (sourceEndpointSemicirclePath r ρ) :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ _
      (sourceEndpointSemicirclePath_contDiffOn r ρ) (by
        change range ((sourceEndpointSemicirclePath r ρ).symm) ⊆
          sourceCanonicalRootDomain hp hp1 ψ at hrdom
        simpa only [Path.symm_range] using hrdom)
  have hrInt : CurveIntegrable ω right := hrBase.symm
  have hleftBase : CurveIntegrable ω (sourceEndpointSemicirclePath l (-ρ)) :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ _
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
    _ = sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n ρ -
          sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ -
          sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-ρ) -
          sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ) := by
      have hu : (∫ᶜ z in upper, ω z) =
          sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n ρ :=
        sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n ρ
      have hr : (∫ᶜ z in right, ω z) =
          -sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ := by
        change (∫ᶜ z in (sourceEndpointSemicirclePath r ρ).symm, ω z) = _
        rw [curveIntegral_symm,
          sourceCriticalRootRatio_endpointArc_curveIntegral_eq]
      have hl : (∫ᶜ z in lower, ω z) =
          -sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-ρ) := by
        change (∫ᶜ z in Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I), ω z) = _
        rw [← Path.segment_symm (l-(ρ:ℂ)*I) (r-(ρ:ℂ)*I),
          curveIntegral_symm]
        have hle : l-(ρ:ℂ)*I = l+((-ρ:ℝ):ℂ)*I := by push_cast; ring
        have hre : r-(ρ:ℂ)*I = r+((-ρ:ℝ):ℂ)*I := by push_cast; ring
        rw [hle,hre]
        exact congrArg Neg.neg
          (sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq
            hp hp1 ψ n (-ρ))
      have hleft : (∫ᶜ z in left, ω z) =
          -sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ) := by
        change (∫ᶜ z in (sourceLeftOuterArcPath l ρ).symm, ω z) = _
        rw [curveIntegral_symm]
        change -(∫ᶜ z in (sourceEndpointSemicirclePath l (-ρ)).cast _ _, ω z) = _
        rw [curveIntegral_cast,
          sourceCriticalRootRatio_endpointArc_curveIntegral_eq]
      rw [hu,hr,hl,hleft]
      ring

/-- The critical-root quotient integral over the actual closed stadium
path tends to zero as its radius shrinks to the real gap. -/
theorem sourceCriticalRootRatio_stadium_curveIntegral_tendsto_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    Tendsto (fun ρ : ℝ =>
      ∫ᶜ z in sourceGapStadiumPath l r ρ,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
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
  have hu := sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_upper
    hp hp1 ψ hreal n hopen
  have hl := (sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_lower
    hp hp1 ψ hreal n hopen).comp hneg
  have ha := sourceCriticalRootRatio_outerArcIntegrals_tendsto_zero
    hp hp1 ψ hreal n hopen
  have hsum : Tendsto (fun ρ : ℝ =>
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n ρ -
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ -
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-ρ) -
      sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ))
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
    simpa [l,r] using ((hu.sub ha.2).sub hl).sub ha.1
  have heq : (fun ρ : ℝ =>
      ∫ᶜ z in sourceGapStadiumPath l r ρ,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)]
      (fun ρ : ℝ =>
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n ρ -
        sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ r ρ -
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n (-ρ) -
        sourceCriticalRootRatio_endpointArcIntegral hp hp1 ψ l (-ρ)) := by
    filter_upwards [hpos,hsmall] with ρ hρ hρε
    exact sourceCriticalRootRatio_stadium_curveIntegral_eq hp hp1 ψ n ρ
      (hdom ρ ⟨hρ,hρε.le⟩)
  exact hsum.congr' heq.symm

end NLS.ZakharovShabat
