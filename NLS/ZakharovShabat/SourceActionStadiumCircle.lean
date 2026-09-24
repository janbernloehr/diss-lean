import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumCircleVanishing
import NLS.ZakharovShabat.SourceActionCircle

/-!
# Deforming the weighted action circle to a shrinking gap stadium

The cut-avoiding four-piece homotopy also applies to the spectral-
parameter-weighted quotient. Its clockwise orientation gives the
negative of the counterclockwise action circle integral.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On sufficiently small corner circles, the recentered weighted
circle integral is the negative weighted stadium integral. -/
theorem exists_sourceAction_cornerCircleIntegral_eq_neg_stadium
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (q : ℂ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    let f : ℂ → ℂ := fun z =>
      (z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)
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
  let f : ℂ → ℂ := fun z =>
    (z-q) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hf : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      DifferentiableAt ℂ f z := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).mul
      (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz) |>.differentiableAt
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

/-- The actual action on a small midpoint corner circle is a
normalized, oppositely oriented weighted stadium integral. -/
theorem exists_sourceActionCircle_eq_neg_stadium
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
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    let f : ℂ → ℂ := fun z =>
      z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      sourceActionCircle hp hp1 ψ c (stadiumCornerRadius d ρ) =
        -(Real.pi : ℂ)⁻¹ *
          (∫ᶜ z in sourceGapStadiumPath l r ρ,
            holomorphicOneForm f z) := by
  obtain ⟨ε,hε,heq⟩ :=
    exists_sourceAction_cornerCircleIntegral_eq_neg_stadium
      hp hp1 ψ hreal n hopen 0
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  have h := heq ρ hρ
  change (∮ z in C(_,stadiumCornerRadius _ ρ),
      (z-0) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) =
    -(∫ᶜ z in sourceGapStadiumPath _ _ ρ,
      holomorphicOneForm
        (fun z => (z-0) * sourceCriticalRootRatioJoint hp hp1 (z,ψ)) z) at h
  simp only [sub_zero] at h
  unfold sourceActionCircle
  rw [h]
  ring

end NLS.ZakharovShabat
