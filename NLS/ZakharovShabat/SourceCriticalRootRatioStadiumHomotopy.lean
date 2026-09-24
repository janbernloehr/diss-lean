import NLS.ZakharovShabat.SourceGapStadiumAffine

/-!
# Homotopy invariance of the critical-root quotient stadium

The four sides of a small stadium are smooth individually. Their
affine deformations stay in the canonical-root domain, so the
piecewise holomorphic homotopy theorem compares their integrals at
different radii.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem sourceCriticalRootRatio_stadiumPieces_curveIntegrable
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (l r : ℂ) (R : ℝ)
    (hdom : range (sourceGapStadiumPath l r R) ⊆
      sourceCanonicalRootDomain hp hp1 ψ) :
    let f : ℂ → ℂ := fun z =>
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
      (Path.segment (l+(R:ℂ)*Complex.I) (r+(R:ℂ)*Complex.I)) ∧
    CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
      (sourceEndpointSemicirclePath r R).symm ∧
    CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
      (Path.segment (r-(R:ℂ)*Complex.I) (l-(R:ℂ)*Complex.I)) ∧
    CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
      (sourceLeftOuterArcPath l R).symm := by
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  let upper : Path (l+(R:ℂ)*Complex.I) (r+(R:ℂ)*Complex.I) :=
    Path.segment (l+(R:ℂ)*Complex.I) (r+(R:ℂ)*Complex.I)
  let right : Path (r+(R:ℂ)*Complex.I) (r-(R:ℂ)*Complex.I) :=
    (sourceEndpointSemicirclePath r R).symm
  let lower : Path (r-(R:ℂ)*Complex.I) (l-(R:ℂ)*Complex.I) :=
    Path.segment (r-(R:ℂ)*Complex.I) (l-(R:ℂ)*Complex.I)
  let left : Path (l-(R:ℂ)*Complex.I) (l+(R:ℂ)*Complex.I) :=
    (sourceLeftOuterArcPath l R).symm
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
  have huInt : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) upper :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ upper
      (sourceSegmentPath_contDiffOn _ _) hudom
  have hlInt : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) lower :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ lower
      (sourceSegmentPath_contDiffOn _ _) hldom
  have hrBase : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
      (sourceEndpointSemicirclePath r R) :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ _
      (sourceEndpointSemicirclePath_contDiffOn r R) (by
        change range ((sourceEndpointSemicirclePath r R).symm) ⊆
          sourceCanonicalRootDomain hp hp1 ψ at hrdom
        simpa only [Path.symm_range] using hrdom)
  have hrInt : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) right :=
    hrBase.symm
  have hleftBase : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f)
      (sourceEndpointSemicirclePath l (-R)) :=
    sourceCriticalRootRatio_curveIntegrable_of_smoothPath hp hp1 ψ _
      (sourceEndpointSemicirclePath_contDiffOn l (-R)) (by
        change range ((sourceLeftOuterArcPath l R).symm) ⊆
          sourceCanonicalRootDomain hp hp1 ψ at hleftdom
        rw [Path.symm_range] at hleftdom
        have hcast : range (sourceLeftOuterArcPath l R) =
            range (sourceEndpointSemicirclePath l (-R)) := by rfl
        rw [hcast] at hleftdom
        exact hleftdom)
  have hleftInt : CurveIntegrable (NLS.ComplexAnalysis.holomorphicOneForm f) left := by
    apply CurveIntegrable.symm
    exact hleftBase.cast (by push_cast; ring) (by push_cast; ring)
  exact ⟨huInt, hrInt, hlInt, hleftInt⟩

/-- Around a real-type periodic gap, the critical-root quotient
integral over the closed stadium is independent of all sufficiently
small positive radii. -/
theorem sourceCriticalRootRatio_stadium_curveIntegral_eq_of_radii
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧ ∀ R₀ ∈ Ioc 0 ε, ∀ R₁ ∈ Ioc 0 ε,
      (∫ᶜ z in sourceGapStadiumPath l r R₀,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) =
      ∫ᶜ z in sourceGapStadiumPath l r R₁,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε,hε,hdom⟩ :=
    exists_sourceGapStadiumPath_range_subset_rootDomain hp hp1 ψ hreal n
  refine ⟨ε,hε,?_⟩
  intro R₀ hR₀ R₁ hR₁
  let f : ℂ → ℂ := fun w =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
      sourceCanonicalRoot hp hp1 ψ w
  let ω := NLS.ComplexAnalysis.holomorphicOneForm f
  let D := sourceCanonicalRootDomain hp hp1 ψ
  let upper₀ : Path (l+(R₀:ℂ)*Complex.I) (r+(R₀:ℂ)*Complex.I) :=
    Path.segment (l+(R₀:ℂ)*Complex.I) (r+(R₀:ℂ)*Complex.I)
  let right₀ : Path (r+(R₀:ℂ)*Complex.I) (r-(R₀:ℂ)*Complex.I) :=
    (sourceEndpointSemicirclePath r R₀).symm
  let lower₀ : Path (r-(R₀:ℂ)*Complex.I) (l-(R₀:ℂ)*Complex.I) :=
    Path.segment (r-(R₀:ℂ)*Complex.I) (l-(R₀:ℂ)*Complex.I)
  let left₀ : Path (l-(R₀:ℂ)*Complex.I) (l+(R₀:ℂ)*Complex.I) :=
    (sourceLeftOuterArcPath l R₀).symm
  let upper₁ : Path (l+(R₁:ℂ)*Complex.I) (r+(R₁:ℂ)*Complex.I) :=
    Path.segment (l+(R₁:ℂ)*Complex.I) (r+(R₁:ℂ)*Complex.I)
  let right₁ : Path (r+(R₁:ℂ)*Complex.I) (r-(R₁:ℂ)*Complex.I) :=
    (sourceEndpointSemicirclePath r R₁).symm
  let lower₁ : Path (r-(R₁:ℂ)*Complex.I) (l-(R₁:ℂ)*Complex.I) :=
    Path.segment (r-(R₁:ℂ)*Complex.I) (l-(R₁:ℂ)*Complex.I)
  let left₁ : Path (l-(R₁:ℂ)*Complex.I) (l+(R₁:ℂ)*Complex.I) :=
    (sourceLeftOuterArcPath l R₁).symm
  have hInt₀ := sourceCriticalRootRatio_stadiumPieces_curveIntegrable
    hp hp1 ψ l r R₀ (hdom R₀ hR₀)
  have hInt₁ := sourceCriticalRootRatio_stadiumPieces_curveIntegrable
    hp hp1 ψ l r R₁ (hdom R₁ hR₁)
  change CurveIntegrable ω upper₀ ∧ CurveIntegrable ω right₀ ∧
    CurveIntegrable ω lower₀ ∧ CurveIntegrable ω left₀ at hInt₀
  change CurveIntegrable ω upper₁ ∧ CurveIntegrable ω right₁ ∧
    CurveIntegrable ω lower₁ ∧ CurveIntegrable ω left₁ at hInt₁
  have hleftSmooth (R : ℝ) :
      ContDiffOn ℝ 2 ((sourceLeftOuterArcPath l R).symm).extend
        (Icc (0:ℝ) 1) := by
    apply sourcePath_symm_contDiffOn_two
    change ContDiffOn ℝ 2 (sourceEndpointSemicirclePath l (-R)).extend
      (Icc (0:ℝ) 1)
    exact sourceEndpointSemicirclePath_contDiffOn_two l (-R)
  change (∫ᶜ z in ((upper₀.trans right₀).trans lower₀).trans left₀, ω z) =
    ∫ᶜ z in ((upper₁.trans right₁).trans lower₁).trans left₁, ω z
  apply NLS.ComplexAnalysis.four_piece_curveIntegral_eq_of_affine_homotopy
    f (t := D)
  · intro s u
    exact sourceGapStadiumPieces_affine_mem l r ε R₀ R₁ D
      hR₀ hR₁ hdom s u
  · intro z hz
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz).differentiableAt
  · exact sourceSegmentPath_contDiffOn_two _ _
  · exact sourcePath_symm_contDiffOn_two _
      (sourceEndpointSemicirclePath_contDiffOn_two r R₀)
  · exact sourceSegmentPath_contDiffOn_two _ _
  · exact hleftSmooth R₀
  · exact sourceSegmentPath_contDiffOn_two _ _
  · exact sourcePath_symm_contDiffOn_two _
      (sourceEndpointSemicirclePath_contDiffOn_two r R₁)
  · exact sourceSegmentPath_contDiffOn_two _ _
  · exact hleftSmooth R₁
  · exact hInt₀.1
  · exact hInt₀.2.1
  · exact hInt₀.2.2.1
  · exact hInt₀.2.2.2
  · exact hInt₁.1
  · exact hInt₁.2.1
  · exact hInt₁.2.2.1
  · exact hInt₁.2.2.2

/-- At an open real-type gap, every sufficiently small closed stadium
has zero critical-root quotient integral. The integral is constant in
the radius by piecewise homotopy invariance, and its shrinking-radius
limit is zero. -/
theorem sourceCriticalRootRatio_stadium_curveIntegral_eq_zero_of_small_radius
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ R ∈ Ioc 0 ε,
      (∫ᶜ z in sourceGapStadiumPath l r R,
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z) = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let F : ℝ → ℂ := fun R =>
    ∫ᶜ z in sourceGapStadiumPath l r R,
      NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z
  obtain ⟨ε,hε,hconst⟩ :=
    sourceCriticalRootRatio_stadium_curveIntegral_eq_of_radii hp hp1 ψ hreal n
  have hlim : Tendsto F (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 (0:ℂ)) :=
    sourceCriticalRootRatio_stadium_curveIntegral_tendsto_zero
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro R hR
  have hsmall₀ : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
    hsmall₀.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), 0 < ρ :=
    self_mem_nhdsWithin
  have hEq : F =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)] fun _ => F R := by
    filter_upwards [hsmall,hpos] with ρ hρlt hρpos
    exact hconst ρ ⟨hρpos,hρlt.le⟩ R hR
  have hconstlim : Tendsto F (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 (F R)) :=
    tendsto_const_nhds.congr' hEq.symm
  exact tendsto_nhds_unique hconstlim hlim

end NLS.ZakharovShabat
