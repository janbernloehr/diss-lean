import NLS.ZakharovShabat.SourceGapStadiumCircleLocalHomotopy
import NLS.ZakharovShabat.SourceStandardRootWeightedStadium

/-!
# Local weighted stadium-to-circle identity

The numerator only needs to be analytic on a neighborhood containing
a filled midpoint disc. The selected standard root is analytic off its
gap, and the actual affine stadium-to-circle deformation stays in that
disc for sufficiently small stadium height.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A local disc of differentiability suffices to equate the corner
circle integral with the negatively oriented gap-stadium integral. -/
theorem exists_sourceGap_cornerCircleIntegral_eq_neg_stadium_of_local_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (R : ℝ) (f : ℂ → ℂ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R →
    (∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ ∩ closedBall c R,
      DifferentiableAt ℂ f z) →
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
  dsimp only
  intro hR hf
  change d < R at hR
  obtain ⟨ε₀,hε₀,heq⟩ :=
    exists_sourceGap_stadium_eq_cornerCirclePath_integral_of_local_disc
      hp hp1 ψ hreal n hopen R f hR hf
  obtain ⟨ε₁,hε₁,hcircleDom⟩ :=
    exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
      hp hp1 ψ hreal n
  let ε := min (min ε₀ ε₁) (R-d)
  have hε : 0 < ε := lt_min (lt_min hε₀ hε₁) (sub_pos.mpr hR)
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  have hρ₀ : ρ ∈ Ioc 0 ε₀ :=
    ⟨hρ.1,(hρ.2.trans (min_le_left _ _)).trans (min_le_left _ _)⟩
  have hρ₁ : ρ ∈ Ioc 0 ε₁ :=
    ⟨hρ.1,(hρ.2.trans (min_le_left _ _)).trans (min_le_right _ _)⟩
  let Rc := stadiumCornerRadius d ρ
  let δ := Rc-d
  have hδ := stadiumCornerRadius_sub_halfWidth hd hρ.1
  have hδ₁ : δ ∈ Ioc 0 ε₁ := ⟨hδ.1,hδ.2.trans hρ₁.2⟩
  have hRc : 0 ≤ Rc := by dsimp [Rc]; exact norm_nonneg _
  have hRadius : d+δ = Rc := by dsimp [δ]; ring
  have hsphere : sphere c Rc ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    have h := (hcircleDom δ hδ₁).2.2
    change sphere c (d+δ) ⊆ sourceCanonicalRootDomain hp hp1 ψ at h
    rw [hRadius] at h
    exact h
  have hRcR : Rc ≤ R := by
    have hmargin := hρ.2.trans (min_le_right (min ε₀ ε₁) (R-d))
    linarith [hδ.2]
  have hfCircle (θ : ℝ) : ContinuousAt f (circleMap c Rc θ) := by
    have hs : circleMap c Rc θ ∈ sphere c Rc :=
      circleMap_mem_sphere c hRc θ
    have hb : circleMap c Rc θ ∈ closedBall c R :=
      mem_closedBall.mpr (by linarith [mem_sphere.mp hs])
    exact (hf _ ⟨hsphere hs,hb⟩).continuousAt
  have hloop := stadiumCircleLoop_curveIntegral_eq_neg_circleIntegral
    f c d ρ hfCircle
  have hstadEq := heq ρ hρ₀
  calc
    (∮ z in C(c, Rc), f z) =
        -(∫ᶜ z in (((stadiumCircleUpperArc c d ρ).trans
          (stadiumCircleRightArc c d ρ)).trans
          (stadiumCircleLowerArc c d ρ)).trans
          (stadiumCircleLeftArc c d ρ), holomorphicOneForm f z) := by
            rw [hloop]
            simp only [Rc, neg_neg]
    _ = -(∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm f z) := by rw [hstadEq]

/-- The weighted selected-root corner-circle identity requires
analyticity of the numerator only near the enclosing midpoint disc. -/
theorem exists_sourceStandardRoot_weighted_cornerCircleIntegral_eq_neg_stadium_of_local_disc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (R : ℝ) (g : ℂ → ℂ) (U : Set ℂ)
    (hg : AnalyticOnNhd ℂ g U) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      (∮ z in C(c, stadiumCornerRadius d ρ),
        g z / sourceStandardRoot hp hp1 ψ n z) =
        -(∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm
            (fun z => g z / sourceStandardRoot hp hp1 ψ n z) z) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro hR hU
  change d < R at hR
  change closedBall c R ⊆ U at hU
  apply exists_sourceGap_cornerCircleIntegral_eq_neg_stadium_of_local_disc
    hp hp1 ψ hreal n hopen R _ hR
  intro z hz
  have hnot : z ∉ sourcePeriodicSegment hp hp1 ψ n := hz.1 n
  exact ((hg z (hU hz.2)).div
    (sourceStandardRoot_analyticAt hp hp1 ψ n z hnot)
    (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hnot)).differentiableAt

end NLS.ZakharovShabat
