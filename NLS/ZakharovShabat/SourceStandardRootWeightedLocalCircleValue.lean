import NLS.ZakharovShabat.SourceStandardRootWeightedLocalStadiumLimit
import NLS.ZakharovShabat.SourceStandardRootWeightedLocalStadiumCircle
import NLS.ZakharovShabat.SourceStandardRootWeightedCircleValue

/-!
# Local weighted circle value on a real periodic gap

The local stadium limit, local stadium-to-circle deformation, and
local annulus invariance identify the exact weighted integral on a
midpoint circle. No analyticity of the numerator outside the selected
midpoint disc is used.
-/

noncomputable section
open Set Metric Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A midpoint circle inside a local analytic disc has the exact
weighted selected-root value from the upper gap-side integral. -/
theorem weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_local_disc
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
    (hg : AnalyticOnNhd ℂ g U) (R : ℝ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
    (∮ z in C(c,R), g z / sourceStandardRoot hp hp1 ψ n z) =
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
  dsimp only
  intro hR hUdisc
  change d < R at hR
  change closedBall c R ⊆ U at hUdisc
  obtain ⟨ε₀,hε₀,hcontour⟩ :=
    exists_sourceStandardRoot_weighted_cornerCircleIntegral_eq_neg_stadium_of_local_disc
      hp hp1 ψ hreal n hopen R g U hg hR hUdisc
  have hstad :=
    sourceStandardRoot_weighted_stadium_curveIntegral_tendsto_two_upper_of_local_disc
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg R hR hUdisc
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  let ε := min ε₀ (R-d)
  have hε : 0 < ε := lt_min hε₀ (sub_pos.mpr hR)
  have hsmall0 : ∀ᶠ ρ in 𝓝 (0:ℝ), ρ < ε := Iio_mem_nhds hε
  have hsmall : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), ρ < ε :=
    hsmall0.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ ρ in 𝓝[Set.Ioi 0] (0:ℝ), 0 < ρ :=
    self_mem_nhdsWithin
  have hconstlim : Tendsto (fun ρ : ℝ =>
      -(∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm
          (fun z => g z / sourceStandardRoot hp hp1 ψ n z) z))
      (𝓝[Set.Ioi 0] (0:ℝ))
      (𝓝 (∮ z in C(c,R),
        g z / sourceStandardRoot hp hp1 ψ n z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hpos,hsmall] with ρ hρ hρε
    have hρ₀ : ρ ∈ Ioc 0 ε₀ :=
      ⟨hρ,(le_of_lt hρε).trans (min_le_left _ _)⟩
    let Rc := stadiumCornerRadius d ρ
    let δ := Rc-d
    have hδ := stadiumCornerRadius_sub_halfWidth hd hρ
    have hRcpos : 0 < Rc := by
      have hδpos : 0 < Rc-d := hδ.1
      linarith
    have hRcR : Rc ≤ R := by
      have hmargin := (le_of_lt hρε).trans (min_le_right ε₀ (R-d))
      linarith [hδ.2]
    have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c Rc := by
      have hm := sourcePeriodicSegment_subset_midpoint_ball
        hp hp1 ψ hreal n δ hδ.1
      change sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+δ) at hm
      have heq : d+δ = Rc := by dsimp [δ]; ring
      rw [heq] at hm
      exact hm
    have hradial :=
      circleIntegral_weighted_sourceStandardRoot_eq_of_local_isolated_annulus
        hp hp1 ψ n g U hg c Rc R hRcpos hRcR hseg hUdisc
    exact hradial.trans (hcontour ρ hρ₀)
  have hlimit : Tendsto (fun ρ : ℝ =>
      -(∫ᶜ z in sourceGapStadiumPath l r ρ,
        holomorphicOneForm
          (fun z => g z / sourceStandardRoot hp hp1 ψ n z) z))
      (𝓝[Set.Ioi 0] (0:ℝ)) (𝓝 (-(2*B))) := by
    simpa only [B] using hstad.neg
  exact tendsto_nhds_unique hconstlim hlimit

/-- The local-disc form of the Lemma 12.3 maximum estimate: the
normalized weighted integral on a midpoint circle is bounded by the
attained maximum of the numerator on the selected real gap. -/
theorem weighted_sourceStandardRoot_midpointCircle_max_bound_of_local_disc
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
    (hg : AnalyticOnNhd ℂ g U) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∀ R : ℝ, d < R → closedBall c R ⊆ U →
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
    exact ((hg z (hgapU hz)).continuousAt).continuousWithinAt
  obtain ⟨z,hz,hmax,hbound⟩ :=
    sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound
      hp hp1 ψ n hgap g hgcont
  dsimp only
  intro R hR hUdisc
  refine ⟨z,hz,hmax,?_⟩
  rw [weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_local_disc
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg R hR hUdisc]
  let B := gapSideBoundaryIntegral τ δ g 1 true
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (2*Real.pi:ℂ)⁻¹ * (-(2*B)) = -(B/(Real.pi:ℂ)) := by
    field_simp [hπ]
  rw [heq,norm_neg]
  exact hbound 1 true

end NLS.ZakharovShabat
