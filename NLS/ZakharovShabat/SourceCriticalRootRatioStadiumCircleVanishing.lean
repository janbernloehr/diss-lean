import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumCircleHomotopy

/-!
# Vanishing of the critical-root quotient integral on gap circles

For an open real-type periodic gap, a sufficiently small circle
through the four corners of the shrinking stadium has zero integral.
The stadium integral vanishes, and the cut-avoiding piecewise homotopy
transfers that result to the standard counterclockwise circle.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Small corner circles around an open real-type periodic gap have
zero critical-root quotient integral. -/
theorem exists_sourceCriticalRootRatio_cornerCircleIntegral_eq_zero
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
      deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
        sourceCanonicalRoot hp hp1 ψ z
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      (∮ z in C(c, stadiumCornerRadius d ρ), f z) = 0 := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let f : ℂ → ℂ := fun z =>
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z /
      sourceCanonicalRoot hp hp1 ψ z
  obtain ⟨ε₀,hε₀,hzero⟩ :=
    sourceCriticalRootRatio_stadium_curveIntegral_eq_zero_of_small_radius
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₁,hε₁,heq⟩ :=
    exists_sourceCriticalRootRatio_stadium_eq_cornerCirclePath_integral
      hp hp1 ψ hreal n hopen
  obtain ⟨ε₂,hε₂,hcircleDom⟩ :=
    exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
      hp hp1 ψ hreal n
  let ε := min ε₀ (min ε₁ ε₂)
  have hε : 0 < ε := lt_min hε₀ (lt_min hε₁ hε₂)
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    have hgap : l.re < r.re := hopen
    exact div_pos (sub_pos.mpr hgap) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  have hρ₀ : ρ ∈ Ioc 0 ε₀ :=
    ⟨hρ.1, hρ.2.trans (min_le_left _ _)⟩
  have hρ₁ : ρ ∈ Ioc 0 ε₁ :=
    ⟨hρ.1, hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hρ₂ : ρ ∈ Ioc 0 ε₂ :=
    ⟨hρ.1, hρ.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  let R := stadiumCornerRadius d ρ
  let δ := R-d
  have hδ := stadiumCornerRadius_sub_halfWidth hd hρ.1
  have hδ₂ : δ ∈ Ioc 0 ε₂ := ⟨hδ.1,hδ.2.trans hρ₂.2⟩
  have hR : 0 ≤ R := by dsimp [R]; exact norm_nonneg _
  have hRadius : d+δ = R := by dsimp [δ]; ring
  have hsphere : sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    have h := (hcircleDom δ hδ₂).2.2
    change sphere c (d+δ) ⊆ sourceCanonicalRootDomain hp hp1 ψ at h
    rw [hRadius] at h
    exact h
  have hfCircle (θ : ℝ) : ContinuousAt f (circleMap c R θ) := by
    have hz : circleMap c R θ ∈ sourceCanonicalRootDomain hp hp1 ψ :=
      hsphere (circleMap_mem_sphere c hR θ)
    exact (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ _ hz).continuousAt
  have hloop := stadiumCircleLoop_curveIntegral_eq_neg_circleIntegral
    f c d ρ hfCircle
  have hstadEq := heq ρ hρ₁
  have hstadZero := hzero ρ hρ₀
  have hneg : -(∮ z in C(c, R), f z) = 0 := by
    calc
      -(∮ z in C(c, R), f z) =
          (∫ᶜ z in (((stadiumCircleUpperArc c d ρ).trans
            (stadiumCircleRightArc c d ρ)).trans
            (stadiumCircleLowerArc c d ρ)).trans
            (stadiumCircleLeftArc c d ρ), holomorphicOneForm f z) := hloop.symm
      _ = (∫ᶜ z in sourceGapStadiumPath l r ρ,
          holomorphicOneForm f z) := hstadEq.symm
      _ = 0 := hstadZero
  exact neg_eq_zero.mp hneg

end NLS.ZakharovShabat
