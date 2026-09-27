import NLS.ZakharovShabat.SourceGapStadiumCircleLocalGeometry
import NLS.ZakharovShabat.SourceGapStadiumIntegralDecomposition

/-!
# Stadium decomposition on a local continuity domain

The four-piece formula only needs the integrand to be continuous at
points of the stadium path. The domain is explicit so a local analytic
numerator can be used without global hypotheses.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth path carries a holomorphic one-form when its scalar
integrand is continuous at all points of a containing set. -/
theorem sourceGap_curveIntegrable_of_smoothPath_on
    (D : Set ℂ) (f : ℂ → ℂ)
    (hf : ∀ z ∈ D, ContinuousAt f z)
    {a b : ℂ} (γ : Path a b)
    (hsmooth : ContDiffOn ℝ 1 γ.extend (Icc (0:ℝ) 1))
    (hdom : range γ ⊆ D) :
    CurveIntegrable (holomorphicOneForm f) γ := by
  have hω : ContinuousOn (holomorphicOneForm f) (range γ) := by
    intro z hz
    exact ((hf z (hdom hz)).smul continuousAt_const).continuousWithinAt
  exact hω.curveIntegrable_of_contDiffOn hsmooth (fun t => ⟨t,rfl⟩)

/-- The stadium integral equals its four oriented pieces when the
integrand is continuous on a set containing the whole stadium. -/
theorem sourceGapStadium_curveIntegral_fourPieces_on
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (ρ : ℝ) (f : ℂ → ℂ) (D : Set ℂ)
    (hf : ∀ z ∈ D, ContinuousAt f z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    range (sourceGapStadiumPath l r ρ) ⊆
      D →
    (∫ᶜ z in sourceGapStadiumPath l r ρ, holomorphicOneForm f z) =
      (∫ᶜ z in Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I),
        holomorphicOneForm f z) -
      (∫ᶜ z in sourceEndpointSemicirclePath r ρ,
        holomorphicOneForm f z) -
      (∫ᶜ z in Path.segment (l-(ρ:ℂ)*I) (r-(ρ:ℂ)*I),
        holomorphicOneForm f z) -
      (∫ᶜ z in sourceEndpointSemicirclePath l (-ρ),
        holomorphicOneForm f z) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  dsimp only
  intro hdom
  let ω := holomorphicOneForm f
  let upper : Path (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I) :=
    Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)
  let right : Path (r+(ρ:ℂ)*I) (r-(ρ:ℂ)*I) :=
    (sourceEndpointSemicirclePath r ρ).symm
  let lower : Path (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I) :=
    Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)
  let left : Path (l-(ρ:ℂ)*I) (l+(ρ:ℂ)*I) :=
    (sourceLeftOuterArcPath l ρ).symm
  change range (((upper.trans right).trans lower).trans left) ⊆
    D at hdom
  rw [Path.trans_range, Path.trans_range, Path.trans_range] at hdom
  have hudom : range upper ⊆ D :=
    fun _ hz => hdom (Or.inl (Or.inl (Or.inl hz)))
  have hrdom : range right ⊆ D :=
    fun _ hz => hdom (Or.inl (Or.inl (Or.inr hz)))
  have hldom : range lower ⊆ D :=
    fun _ hz => hdom (Or.inl (Or.inr hz))
  have hleftdom : range left ⊆ D :=
    fun _ hz => hdom (Or.inr hz)
  have huInt : CurveIntegrable ω upper :=
    sourceGap_curveIntegrable_of_smoothPath_on D f hf upper
      (sourceSegmentPath_contDiffOn _ _) hudom
  have hlInt : CurveIntegrable ω lower :=
    sourceGap_curveIntegrable_of_smoothPath_on D f hf lower
      (sourceSegmentPath_contDiffOn _ _) hldom
  have hrBase : CurveIntegrable ω (sourceEndpointSemicirclePath r ρ) :=
    sourceGap_curveIntegrable_of_smoothPath_on D f hf _
      (sourceEndpointSemicirclePath_contDiffOn r ρ) (by
        change range ((sourceEndpointSemicirclePath r ρ).symm) ⊆
          D at hrdom
        simpa only [Path.symm_range] using hrdom)
  have hrInt : CurveIntegrable ω right := hrBase.symm
  have hleftBase : CurveIntegrable ω (sourceEndpointSemicirclePath l (-ρ)) :=
    sourceGap_curveIntegrable_of_smoothPath_on D f hf _
      (sourceEndpointSemicirclePath_contDiffOn l (-ρ)) (by
        change range ((sourceLeftOuterArcPath l ρ).symm) ⊆
          D at hleftdom
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
    _ = (∫ᶜ z in upper, ω z) -
          (∫ᶜ z in sourceEndpointSemicirclePath r ρ, ω z) -
          (∫ᶜ z in Path.segment (l-(ρ:ℂ)*I) (r-(ρ:ℂ)*I), ω z) -
          (∫ᶜ z in sourceEndpointSemicirclePath l (-ρ), ω z) := by
      have hr : (∫ᶜ z in right, ω z) =
          -(∫ᶜ z in sourceEndpointSemicirclePath r ρ, ω z) := by
        change (∫ᶜ z in (sourceEndpointSemicirclePath r ρ).symm, ω z) = _
        rw [curveIntegral_symm]
      have hl : (∫ᶜ z in lower, ω z) =
          -(∫ᶜ z in Path.segment (l-(ρ:ℂ)*I) (r-(ρ:ℂ)*I), ω z) := by
        change (∫ᶜ z in Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I), ω z) = _
        rw [← Path.segment_symm (l-(ρ:ℂ)*I) (r-(ρ:ℂ)*I),
          curveIntegral_symm]
      have hleft : (∫ᶜ z in left, ω z) =
          -(∫ᶜ z in sourceEndpointSemicirclePath l (-ρ), ω z) := by
        change (∫ᶜ z in (sourceLeftOuterArcPath l ρ).symm, ω z) = _
        rw [curveIntegral_symm]
        change -(∫ᶜ z in (sourceEndpointSemicirclePath l (-ρ)).cast _ _, ω z) = _
        rw [curveIntegral_cast]
      rw [hr,hl,hleft]
      ring

end NLS.ZakharovShabat
