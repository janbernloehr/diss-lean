import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumCircleVanishing
import NLS.ZakharovShabat.SourceStandardRootFirstMoment

/-!
# Deforming weighted standard-root contours to gap stadiums

For a real open periodic gap, the existing four-piece homotopy between
the gap stadium and the corner circle applies to any holomorphic
weight divided by the selected standard root. The orientation of the
stadium is clockwise, hence the sign in the contour identity.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corner-circle integral of any integrand holomorphic on the
canonical-root domain is the negative of its gap-stadium integral. -/
theorem exists_sourceGap_cornerCircleIntegral_eq_neg_stadium_of_differentiable
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (f : ℂ → ℂ)
    (hf : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      DifferentiableAt ℂ f z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      (∮ z in C(c, stadiumCornerRadius d ρ), f z) =
        -(∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm f z) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε₀,hε₀,heq⟩ :=
    exists_sourceGap_stadium_eq_cornerCirclePath_integral_of_differentiable
      hp hp1 ψ hreal n hopen f hf
  obtain ⟨ε₁,hε₁,hcircleDom⟩ :=
    exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
      hp hp1 ψ hreal n
  let ε := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  have hρ₀ : ρ ∈ Ioc 0 ε₀ := ⟨hρ.1,hρ.2.trans (min_le_left _ _)⟩
  have hρ₁ : ρ ∈ Ioc 0 ε₁ := ⟨hρ.1,hρ.2.trans (min_le_right _ _)⟩
  let R := stadiumCornerRadius d ρ
  let δ := R-d
  have hδ := stadiumCornerRadius_sub_halfWidth hd hρ.1
  have hδ₁ : δ ∈ Ioc 0 ε₁ := ⟨hδ.1,hδ.2.trans hρ₁.2⟩
  have hR : 0 ≤ R := by dsimp [R]; exact norm_nonneg _
  have hRadius : d+δ = R := by dsimp [δ]; ring
  have hsphere : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    have h := (hcircleDom δ hδ₁).2.2
    change sphere c (d+δ) ⊆ sourceCanonicalRootDomain hp hp1 ψ at h
    rw [hRadius] at h
    exact h
  have hfCircle (θ : ℝ) : ContinuousAt f (circleMap c R θ) := by
    have hz : circleMap c R θ ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      hsphere (circleMap_mem_sphere c hR θ)
    exact (hf _ hz).continuousAt
  have hloop := stadiumCircleLoop_curveIntegral_eq_neg_circleIntegral
    f c d ρ hfCircle
  have hstadEq := heq ρ hρ₀
  calc
    (∮ z in C(c, R), f z) =
        -(∫ᶜ z in (((stadiumCircleUpperArc c d ρ).trans
          (stadiumCircleRightArc c d ρ)).trans
          (stadiumCircleLowerArc c d ρ)).trans
          (stadiumCircleLeftArc c d ρ), holomorphicOneForm f z) := by
            rw [hloop]
            simp only [R, neg_neg]
    _ = -(∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm f z) := by rw [hstadEq]

/-- The weighted inverse standard-root integral on sufficiently small
corner circles equals the negatively oriented gap-stadium integral. -/
theorem exists_sourceStandardRoot_weighted_cornerCircleIntegral_eq_neg_stadium
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ)
    (hg : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      (∮ z in C(c, stadiumCornerRadius d ρ),
        g z / sourceStandardRoot hp hp1 ψ n z) =
        -(∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm
            (fun z => g z / sourceStandardRoot hp hp1 ψ n z) z) := by
  apply exists_sourceGap_cornerCircleIntegral_eq_neg_stadium_of_differentiable
    hp hp1 ψ hreal n hopen _
  intro z hz
  have hnot : z ∉ sourcePeriodicSegment hp hp1 ψ n := hz n
  exact ((hg z hz).div
    (sourceStandardRoot_analyticAt hp hp1 ψ n z hnot)
    (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hnot)).differentiableAt

end NLS.ZakharovShabat
