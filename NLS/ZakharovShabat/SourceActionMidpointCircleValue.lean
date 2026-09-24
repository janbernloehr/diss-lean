import NLS.ZakharovShabat.SourceActionCircleNonzero
import NLS.ZakharovShabat.SourceCriticalRootRatioMidpointCircle

/-!
# The exact action value on small midpoint circles

Radial deformation makes the weighted circle integral constant on
sufficiently small circles around an open real gap. The shrinking
stadium limit then identifies that constant with the upper boundary
integral.
-/

noncomputable section
open Set Metric Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The action is invariant under a concentric deformation whose closed
annulus lies in the canonical-root domain. -/
theorem sourceActionCircle_eq_of_annulus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (havoid : closedBall c R \ ball c r ⊆
      sourceCanonicalRootDomain hp hp1 ψ) :
    sourceActionCircle hp hp1 ψ c R =
      sourceActionCircle hp hp1 ψ c r := by
  let f : ℂ → ℂ := fun z => z * sourceCriticalRootRatioJoint hp hp1 (z,ψ)
  have hf : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ f z := by
    intro z hz
    exact analyticAt_id.mul
      (sourceCriticalRootRatio_analyticOnNhd hp hp1 ψ z hz)
  have hc : ContinuousOn f (closedBall c R \ ball c r) := by
    intro z hz
    exact (hf z (havoid hz)).continuousAt.continuousWithinAt
  have hd : ∀ z ∈ (ball c R \ closedBall c r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ f z := by
    intro z hz
    have hz' : z ∈ closedBall c R \ ball c r :=
      ⟨ball_subset_closedBall hz.1.1,
        fun h => hz.1.2 (ball_subset_closedBall h)⟩
    exact (hf z (havoid hz')).differentiableAt
  have heq : (∮ z in C(c,R), f z) = ∮ z in C(c,r), f z :=
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      hr hrR (s := ∅) Set.countable_empty hc hd
  exact congrArg ((Real.pi : ℂ)⁻¹ * ·) heq

/-- All sufficiently small midpoint circles around an open real gap
give the same action. -/
theorem exists_sourceActionCircle_eq_of_small_midpointCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η₁ ∈ Ioc 0 ε, ∀ η₂ ∈ Ioc 0 ε,
      sourceActionCircle hp hp1 ψ c (d+η₁) =
        sourceActionCircle hp hp1 ψ c (d+η₂) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,hcircle⟩ :=
    exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
      hp hp1 ψ hreal n
  refine ⟨ε,hε,?_⟩
  intro η₁ hη₁ η₂ hη₂
  wlog hle : η₁ ≤ η₂ generalizing η₁ η₂
  · exact (this η₂ hη₂ η₁ hη₁ (le_of_not_ge hle)).symm
  apply (sourceActionCircle_eq_of_annulus hp hp1 ψ c
    (d+η₁) (d+η₂) (hcircle η₁ hη₁).1 (by linarith) ?_).symm
  intro z hz
  have hdist : d+η₁ ≤ dist z c ∧ dist z c ≤ d+η₂ := by
    constructor
    · exact le_of_not_gt hz.2
    · exact hz.1
  let η := dist z c-d
  have hη : η ∈ Ioc 0 ε := by
    dsimp [η]
    constructor
    · linarith [hη₁.1]
    · linarith [hη₂.2]
  have hzsphere : z ∈ sphere c (d+η) := by
    simp only [mem_sphere]
    dsimp [η]
    ring
  exact (hcircle η hη).2.2 hzsphere

/-- On every sufficiently small midpoint circle, the action is exactly
the normalized upper gap-side boundary integral. -/
theorem exists_sourceActionCircle_eq_upperBoundaryIntegral
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      sourceActionCircle hp hp1 ψ c (d+η) =
        -(2 * (Real.pi : ℂ)⁻¹) *
          sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let W := sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true
  let K : ℂ := -(2 * (Real.pi : ℂ)⁻¹) * W
  obtain ⟨ε₁,hε₁,hconst⟩ :=
    exists_sourceActionCircle_eq_of_small_midpointCircles
      hp hp1 ψ hreal n
  obtain ⟨ε₂,hε₂,hstadEq⟩ :=
    exists_sourceActionCircle_eq_neg_stadium
      hp hp1 ψ hreal n hopen
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hstad := sourceAction_stadium_curveIntegral_tendsto_two_upper
    hp hp1 ψ hreal n hopen 0
  have hstad' : Tendsto
      (fun ρ => ∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm
          (fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z)
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 (2*W)) := by
    simpa only [l,r,W, Complex.ofReal_zero, sub_zero] using hstad
  have hlim : Tendsto
      (fun ρ => sourceActionCircle hp hp1 ψ c (stadiumCornerRadius d ρ))
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 K) := by
    have hscaled : Tendsto
        (fun ρ => -(Real.pi : ℂ)⁻¹ *
          (∫ᶜ z in sourceGapStadiumPath l r ρ,
            holomorphicOneForm
              (fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z))
        (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 K) := by
      have hscaled' : Tendsto
          (fun ρ => -(Real.pi : ℂ)⁻¹ *
            (∫ᶜ z in sourceGapStadiumPath l r ρ,
              holomorphicOneForm
                (fun w => w * sourceCriticalRootRatioJoint hp hp1 (w,ψ)) z))
          (𝓝[Set.Ioi 0] (0:ℝ))
          (𝓝 (-(Real.pi : ℂ)⁻¹ * (2*W))) :=
        tendsto_const_nhds.mul hstad'
      have hK : -(Real.pi : ℂ)⁻¹ * (2*W) = K := by
        dsimp [K]
        ring
      rw [hK] at hscaled'
      exact hscaled'
    have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
    have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
      hsmall0.filter_mono nhdsWithin_le_nhds
    apply hscaled.congr'
    filter_upwards [hsmall,self_mem_nhdsWithin] with ρ hρε hρ
    have hρ₂ : ρ ∈ Ioc 0 ε₂ :=
      ⟨hρ, (le_of_lt hρε).trans (min_le_right _ _)⟩
    exact (hstadEq ρ hρ₂).symm
  refine ⟨ε,hε,?_⟩
  intro η hη
  have hη₁ : η ∈ Ioc 0 ε₁ :=
    ⟨hη.1,hη.2.trans (min_le_left _ _)⟩
  have hconstlim : Tendsto
      (fun ρ => sourceActionCircle hp hp1 ψ c (stadiumCornerRadius d ρ))
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (sourceActionCircle hp hp1 ψ c (d+η))) := by
    apply tendsto_const_nhds.congr'
    have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
    have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
      hsmall0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with ρ hρε hρ
    let R := stadiumCornerRadius d ρ
    let δ := R-d
    have hδ := stadiumCornerRadius_sub_halfWidth hd hρ
    have hδ₁ : δ ∈ Ioc 0 ε₁ := by
      exact ⟨hδ.1, hδ.2.trans (le_of_lt hρε) |>.trans
        (min_le_left _ _)⟩
    have heq := hconst δ hδ₁ η hη₁
    have hR : d+δ = R := by dsimp [δ]; ring
    rw [hR] at heq
    exact heq.symm
  have heq : sourceActionCircle hp hp1 ψ c (d+η) = K :=
    tendsto_nhds_unique hconstlim hlim
  change sourceActionCircle hp hp1 ψ c (d+η) = K
  exact heq

/-- The exact boundary formula makes every sufficiently small midpoint
action real and nonzero on an open real-type gap. -/
theorem exists_sourceActionCircle_real_ne_zero_on_small_midpointCircles
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      (sourceActionCircle hp hp1 ψ c (d+η)).im = 0 ∧
      sourceActionCircle hp hp1 ψ c (d+η) ≠ 0 := by
  obtain ⟨ε,hε,heq⟩ :=
    exists_sourceActionCircle_eq_upperBoundaryIntegral
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro η hη
  rw [heq η hη]
  have hW := sourceAction_upper_cosineBoundaryIntegral_sign
    hp hp1 ψ hreal n hopen 0
  constructor
  · have hWim : (sourceAction_cosineBoundaryIntegral hp hp1 ψ n 0 true).im = 0 := by
      simpa only [Complex.ofReal_zero] using hW.1
    simp [Complex.mul_im, hWim]
  · exact mul_ne_zero
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num)
        (inv_ne_zero (by exact_mod_cast Real.pi_ne_zero)))) hW.2

end NLS.ZakharovShabat
