import NLS.ZakharovShabat.SourceCriticalRootRatioHalfPlanePaths
import NLS.ZakharovShabat.SourceCriticalRootRatioHorizontalLimit
import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumIntegral
import NLS.ZakharovShabat.SourceGapStadiumAffine

/-!
# Arbitrary upper and lower paths approaching a real periodic gap

At each positive or negative height, path independence in the
corresponding half-plane identifies any smooth path between the
shifted endpoints with the horizontal segment. The already proved
horizontal integral limit then applies to arbitrary such path families.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem sourceHorizontalSegment_im
    (l r : ℂ) (hl : l.im = 0) (hr : r.im = 0) (y : ℝ) (u : I) :
    ((Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)) u).im = y := by
  apply sourceHorizontalSegment_im_eq l r hl hr y
  rw [← Path.range_segment]
  exact ⟨u,rfl⟩

/-- Any smooth upper-half-plane path joining the endpoints shifted by
positive height has the same quotient integral as the straight
horizontal segment at that height. -/
theorem sourceCriticalRootRatio_upperPathIntegral_eq_horizontal
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∀ γ : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
      ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
      (∀ u : I, 0 < (γ u).im) →
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y := by
  dsimp only
  intro γ hγ hupper
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hsegmentUpper (u : I) :
      0 < ((Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)) u).im := by
    rw [sourceHorizontalSegment_im l r hl hr y u]
    exact hy
  calc
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
      ∫ᶜ z in Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z := by
          exact sourceCriticalRootRatio_upperHalfPlane_pathIntegral_eq
            hp hp1 ψ hreal γ _ hγ
              (sourceSegmentPath_contDiffOn_two _ _) hupper hsegmentUpper
    _ = sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y :=
      sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n y

/-- The lower-half-plane analogue at negative height. -/
theorem sourceCriticalRootRatio_lowerPathIntegral_eq_horizontal
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (y : ℝ) (hy : y < 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∀ γ : Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
      ContDiffOn ℝ 2 γ.extend (Icc 0 1) →
      (∀ u : I, (γ u).im < 0) →
      (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
        sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y := by
  dsimp only
  intro γ hγ hlower
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hsegmentLower (u : I) :
      ((Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I)) u).im < 0 := by
    rw [sourceHorizontalSegment_im l r hl hr y u]
    exact hy
  calc
    (∫ᶜ z in γ, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =
      ∫ᶜ z in Path.segment (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
        NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z := by
          exact sourceCriticalRootRatio_lowerHalfPlane_pathIntegral_eq
            hp hp1 ψ hreal γ _ hγ
              (sourceSegmentPath_contDiffOn_two _ _) hlower hsegmentLower
    _ = sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n y :=
      sourceCriticalRootRatio_horizontalSegment_curveIntegral_eq hp hp1 ψ n y

/-- The integral along any family of smooth upper-half-plane paths
between vertically shifted gap endpoints tends to zero as the positive
height tends to zero. No bound on path length or shape is needed. -/
theorem sourceCriticalRootRatio_upperPaths_tendsto_zero
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
    ∀ γ : (y : ℝ) → Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
      (∀ y : ℝ, 0 < y → ContDiffOn ℝ 2 (γ y).extend (Icc 0 1)) →
      (∀ y : ℝ, 0 < y → ∀ u : I, 0 < ((γ y) u).im) →
      Tendsto
        (fun y : ℝ => ∫ᶜ z in γ y, NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 0) := by
  dsimp only
  intro γ hγ hupper
  have heq :
      (fun y : ℝ => ∫ᶜ z in γ y, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[Set.Ioi 0] (0:ℝ)]
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact sourceCriticalRootRatio_upperPathIntegral_eq_horizontal
      hp hp1 ψ hreal n y hy (γ y) (hγ y hy) (hupper y hy)
  exact (sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_upper
    hp hp1 ψ hreal n hopen).congr' heq.symm

/-- The same zero limit for arbitrary smooth lower-half-plane path
families as their negative height tends to zero. -/
theorem sourceCriticalRootRatio_lowerPaths_tendsto_zero
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
    ∀ γ : (y : ℝ) → Path (l+(y:ℂ)*Complex.I) (r+(y:ℂ)*Complex.I),
      (∀ y : ℝ, y < 0 → ContDiffOn ℝ 2 (γ y).extend (Icc 0 1)) →
      (∀ y : ℝ, y < 0 → ∀ u : I, ((γ y) u).im < 0) →
      Tendsto
        (fun y : ℝ => ∫ᶜ z in γ y, NLS.ComplexAnalysis.holomorphicOneForm
          (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
            sourceCanonicalRoot hp hp1 ψ w) z)
        (𝓝[Set.Iio 0] (0:ℝ)) (𝓝 0) := by
  dsimp only
  intro γ hγ hlower
  have heq :
      (fun y : ℝ => ∫ᶜ z in γ y, NLS.ComplexAnalysis.holomorphicOneForm
        (fun w => deriv (canonicalDiscriminant hp (periodOnePotential ψ)) w /
          sourceCanonicalRoot hp hp1 ψ w) z) =ᶠ[𝓝[Set.Iio 0] (0:ℝ)]
      sourceCriticalRootRatio_horizontalIntegral hp hp1 ψ n := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact sourceCriticalRootRatio_lowerPathIntegral_eq_horizontal
      hp hp1 ψ hreal n y hy (γ y) (hγ y hy) (hlower y hy)
  exact (sourceCriticalRootRatio_horizontalIntegral_tendsto_zero_lower
    hp hp1 ψ hreal n hopen).congr' heq.symm

end NLS.ZakharovShabat
