import NLS.ZakharovShabat.SourceStandardRootWeightedCornerCircleLimit
import NLS.ZakharovShabat.SourceStandardRootGapSideSourceIntegral

/-!
# Exact weighted contour value on small midpoint circles

Annulus invariance makes the weighted inverse-root circle integral
constant while its circle contracts toward an open real gap. The
shrinking-circle limit therefore identifies the value of each small
circle with the upper gap-side boundary integral.
-/

noncomputable section
open Set Metric Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted standard-root integral is unchanged between two
concentric circles when their closed annulus avoids every periodic
gap and the numerator is analytic there. -/
theorem circleIntegral_weighted_sourceStandardRoot_eq_of_annulus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (g : ℂ → ℂ)
    (hg : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (havoid : closedBall c R \ ball c r ⊆
      sourceCanonicalRootDomain hp hp1 ψ) :
    (∮ z in C(c,R), g z / sourceStandardRoot hp hp1 ψ n z) =
      ∮ z in C(c,r), g z / sourceStandardRoot hp hp1 ψ n z := by
  let f : ℂ → ℂ := fun z => g z / sourceStandardRoot hp hp1 ψ n z
  have hf : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ f z := by
    intro z hz
    exact (hg z hz).div
      (sourceStandardRoot_analyticAt hp hp1 ψ n z (hz n))
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z (hz n))
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
  exact Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) Set.countable_empty hc hd

/-- If the inner circle encloses the selected gap and the outer disc
avoids every other gap, the weighted integral is radially invariant. -/
theorem circleIntegral_weighted_sourceStandardRoot_eq_of_isolated_annulus
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n : ℤ) (g : ℂ → ℂ)
    (hg : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z)
    (c : ℂ) (r R : ℝ) (hr : 0 < r) (hrR : r ≤ R)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c r)
    (hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    (∮ z in C(c,R), g z / sourceStandardRoot hp hp1 ψ n z) =
      ∮ z in C(c,r), g z / sourceStandardRoot hp hp1 ψ n z := by
  apply circleIntegral_weighted_sourceStandardRoot_eq_of_annulus
    hp hp1 ψ n g hg c r R hr hrR
  intro z hz m
  by_cases hm : m = n
  · subst m
    intro hmem
    exact hz.2 (hseg hmem)
  · exact (hother hz.1) m hm

/-- All sufficiently small midpoint circles around a real periodic
gap have the same weighted inverse-root integral. -/
theorem exists_weighted_sourceStandardRoot_eq_of_small_midpointCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (g : ℂ → ℂ)
    (hg : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η₁ ∈ Ioc 0 ε, ∀ η₂ ∈ Ioc 0 ε,
      (∮ z in C(c,d+η₁), g z / sourceStandardRoot hp hp1 ψ n z) =
        ∮ z in C(c,d+η₂), g z / sourceStandardRoot hp hp1 ψ n z := by
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
  apply (circleIntegral_weighted_sourceStandardRoot_eq_of_annulus
    hp hp1 ψ n g hg c (d+η₁) (d+η₂)
      (hcircle η₁ hη₁).1 (by linarith) ?_).symm
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

/-- Every sufficiently small midpoint circle has the exact weighted
boundary value determined by the real gap. -/
theorem exists_weighted_sourceStandardRoot_smallCircle_eq_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hglocal : AnalyticOnNhd ℂ g U)
    (hgdomain : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      (∮ z in C(c,d+η), g z / sourceStandardRoot hp hp1 ψ n z) =
        -(2 * gapSideBoundaryIntegral
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let B := gapSideBoundaryIntegral
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true
  obtain ⟨ε,hε,hconst⟩ :=
    exists_weighted_sourceStandardRoot_eq_of_small_midpointCircles
      hp hp1 ψ hreal n g hgdomain
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hlim := sourceStandardRoot_weighted_cornerCircleIntegral_tendsto_boundary
    hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal hgdomain
  refine ⟨ε,hε,?_⟩
  intro η hη
  have hconstlim : Tendsto (fun ρ =>
      ∮ z in C(c,stadiumCornerRadius d ρ),
        g z / sourceStandardRoot hp hp1 ψ n z)
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (∮ z in C(c,d+η),
        g z / sourceStandardRoot hp hp1 ψ n z)) := by
    apply tendsto_const_nhds.congr'
    have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
    have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
      hsmall0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall,self_mem_nhdsWithin] with ρ hρε hρ
    let R := stadiumCornerRadius d ρ
    let δ := R-d
    have hδ := stadiumCornerRadius_sub_halfWidth hd hρ
    have hδ₁ : δ ∈ Ioc 0 ε := ⟨hδ.1,hδ.2.trans (le_of_lt hρε)⟩
    have heq := hconst δ hδ₁ η hη
    have hR : d+δ = R := by dsimp [δ]; ring
    rw [hR] at heq
    exact heq.symm
  exact tendsto_nhds_unique hconstlim hlim

/-- The normalized integral on each sufficiently small midpoint circle
is bounded by the attained maximum of the numerator on the selected
real gap, as in the estimate of Lemma 12.3. -/
theorem exists_weighted_sourceStandardRoot_smallCircle_max_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hglocal : AnalyticOnNhd ℂ g U)
    (hgdomain : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧
      ∃ z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (∀ w ∈ standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n),
          ‖g w‖ ≤ ‖g z‖) ∧
        ∀ η ∈ Ioc 0 ε,
          ‖(2*Real.pi : ℂ)⁻¹ *
            (∮ w in C(c,d+η),
              g w / sourceStandardRoot hp hp1 ψ n w)‖ ≤ ‖g z‖ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  let B := gapSideBoundaryIntegral τ δ g 1 true
  obtain ⟨ε,hε,hcircle⟩ :=
    exists_weighted_sourceStandardRoot_smallCircle_eq_boundary
      hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal hgdomain
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  have hgcont : ContinuousOn g (standardRootGapSegment τ δ) := by
    intro z hz
    exact ((hglocal z (hgapU hz)).continuousAt).continuousWithinAt
  obtain ⟨z,hz,hmax,hbound⟩ :=
    sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound
      hp hp1 ψ n hgap g hgcont
  refine ⟨ε,hε,z,hz,hmax,?_⟩
  intro η hη
  rw [hcircle η hη]
  have hπ : (Real.pi:ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have heq : (2*Real.pi : ℂ)⁻¹ * (-(2*B)) =
      -(B/(Real.pi:ℂ)) := by
    field_simp [hπ]
  rw [heq,norm_neg]
  exact hbound 1 true

/-- Every isolated midpoint circle around a real open gap has the
same exact weighted contour value, regardless of its radius. -/
theorem weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_isolated
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hglocal : AnalyticOnNhd ℂ g U)
    (hgdomain : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R →
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      (∮ z in C(c,R), g z / sourceStandardRoot hp hp1 ψ n z) =
        -(2 * gapSideBoundaryIntegral
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true) := by
  obtain ⟨ε,hε,hsmall⟩ :=
    exists_weighted_sourceStandardRoot_smallCircle_eq_boundary
      hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal hgdomain
  dsimp only at hsmall ⊢
  intro R hR hother
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  let η : ℝ := min ε ((R-d)/2)
  change d < R at hR
  change closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n at hother
  have hmargin : 0 < (R-d)/2 := by linarith
  have hηpos : 0 < η := lt_min hε hmargin
  have hηε : η ≤ ε := min_le_left _ _
  have hηR : d+η ≤ R := by
    have h := min_le_right ε ((R-d)/2)
    dsimp [η] at h ⊢
    linarith
  have hinner : 0 < d+η := by
    have hd : 0 < d := by
      change 0 < (r.re-l.re)/2
      exact div_pos (sub_pos.mpr hopen) (by norm_num)
    linarith
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+η) :=
    sourcePeriodicSegment_subset_midpoint_ball hp hp1 ψ hreal n η hηpos
  have heq := circleIntegral_weighted_sourceStandardRoot_eq_of_isolated_annulus
    hp hp1 ψ n g hgdomain c (d+η) R hinner hηR hseg hother
  exact heq.trans (hsmall η ⟨hηpos,hηε⟩)

/-- The Lemma 12.3 gap-maximum bound holds on every isolated midpoint
circle around a real open periodic gap. -/
theorem weighted_sourceStandardRoot_midpointCircle_max_bound_of_isolated
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (U : Set ℂ) (hUopen : IsOpen U)
    (hgapU : standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ U)
    (hglocal : AnalyticOnNhd ℂ g U)
    (hgdomain : ∀ z ∈ sourceCanonicalRootDomain hp hp1 ψ,
      AnalyticAt ℂ g z) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R →
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n →
      ∃ z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (∀ w ∈ standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n),
          ‖g w‖ ≤ ‖g z‖) ∧
        ‖(2*Real.pi:ℂ)⁻¹ *
          (∮ w in C(c,R),
            g w / sourceStandardRoot hp hp1 ψ n w)‖ ≤ ‖g z‖ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hgap := sourceCanonicalPeriodicGap_ne_zero_of_openRealGap
    hp hp1 ψ hreal n hopen
  have hgcont : ContinuousOn g (standardRootGapSegment τ δ) := by
    intro z hz
    exact ((hglocal z (hgapU hz)).continuousAt).continuousWithinAt
  obtain ⟨z,hz,hmax,hbound⟩ :=
    sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound
      hp hp1 ψ n hgap g hgcont
  dsimp only
  intro R hR hother
  refine ⟨z,hz,hmax,?_⟩
  rw [weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_isolated
    hp hp1 ψ hreal n hopen g U hUopen hgapU hglocal hgdomain R hR hother]
  let B := gapSideBoundaryIntegral τ δ g 1 true
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (2*Real.pi:ℂ)⁻¹ * (-(2*B)) = -(B/(Real.pi:ℂ)) := by
    field_simp [hπ]
  rw [heq,norm_neg]
  exact hbound 1 true

end NLS.ZakharovShabat
