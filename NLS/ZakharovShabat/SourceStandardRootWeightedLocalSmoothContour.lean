import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue
import NLS.ComplexAnalysis.RadialContourHomotopy

/-!
# Weighted gap integrals on deformed local contours

A gap-avoiding homotopy transports the exact local circle value to a
smooth enclosing loop. Polar graphs provide explicit noncircular loops
whose homotopies satisfy the required local geometry.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact local weighted value persists on a smooth loop reached
from a nested enclosing circle through the numerator's analytic domain
without crossing the selected gap. -/
theorem weighted_sourceStandardRoot_curveIntegral_eq_boundary_of_local_homotopy
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
    (hg : AnalyticOnNhd ℂ g U)
    (c₀ : ℂ) (r₀ R : ℝ) (hr₀ : 0 < r₀)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    {a : ℂ} (γ : Path a a)
    (H : (circlePath c₀ r₀ : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hH_U : range H ⊆ U)
    (hH_avoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      closedBall c₀ r₀ ⊆ closedBall c R →
    (∫ᶜ z in γ, holomorphicOneForm
      (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
      -(2 * gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true) := by
  dsimp only
  intro hR hUdisc hnest
  have heq := sourceStandardRoot_weighted_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ n g U hg H hloop hH_U hH_avoid hcontdiff
  calc
    (∫ᶜ z in γ, holomorphicOneForm
      (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
        ∫ᶜ z in circlePath c₀ r₀, holomorphicOneForm
          (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z := heq.symm
    _ = ∮ z in C(c₀,r₀), g z / sourceStandardRoot hp hp1 ψ n z :=
      curveIntegral_circlePath _ c₀ r₀
    _ = _ := weighted_sourceStandardRoot_circle_eq_boundary_of_local_nested_midpoint
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg
        c₀ r₀ R hr₀ hseg₀ hR hUdisc hnest

/-- The local maximum bound holds on every loop with such an explicit
gap-avoiding homotopy from an enclosing circle. -/
theorem weighted_sourceStandardRoot_curveIntegral_max_bound_of_local_homotopy
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
    (hg : AnalyticOnNhd ℂ g U)
    (c₀ : ℂ) (r₀ R : ℝ) (hr₀ : 0 < r₀)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    {a : ℂ} (γ : Path a a)
    (H : (circlePath c₀ r₀ : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hH_U : range H ⊆ U)
    (hH_avoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      closedBall c₀ r₀ ⊆ closedBall c R →
      ∃ z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (∀ w ∈ standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n),
          ‖g w‖ ≤ ‖g z‖) ∧
        ‖(2 * (Real.pi : ℂ))⁻¹ *
          (∫ᶜ w in γ, holomorphicOneForm
            (fun z => g z / sourceStandardRoot hp hp1 ψ n z) w)‖ ≤ ‖g z‖ := by
  dsimp only
  intro hR hUdisc hnest
  obtain ⟨z,hz,hmax,hbound⟩ :=
    weighted_sourceStandardRoot_circle_max_bound_of_local_nested_midpoint
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg
        c₀ r₀ R hr₀ hseg₀ hR hUdisc hnest
  have heq := sourceStandardRoot_weighted_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ n g U hg H hloop hH_U hH_avoid hcontdiff
  refine ⟨z,hz,hmax,?_⟩
  rw [← heq]
  simpa only [curveIntegral_circlePath] using hbound

/-- For a numerator real-valued on the gap, the normalized integral
on a smoothly deformed local contour attains the negative of one gap
value. -/
theorem weighted_sourceStandardRoot_curveIntegral_real_mean_value_of_local_homotopy
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
    (hg : AnalyticOnNhd ℂ g U)
    (hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n), (g z).im = 0)
    (c₀ : ℂ) (r₀ R : ℝ) (hr₀ : 0 < r₀)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    {a : ℂ} (γ : Path a a)
    (H : (circlePath c₀ r₀ : C(I, ℂ)).Homotopy γ)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hH_U : range H ⊆ U)
    (hH_avoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      closedBall c₀ r₀ ⊆ closedBall c R →
      ∃ μ ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (∫ᶜ z in γ, holomorphicOneForm
            (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) = -g μ := by
  dsimp only
  intro hR hUdisc hnest
  obtain ⟨μ,hμ,hvalue⟩ :=
    weighted_sourceStandardRoot_circle_real_mean_value_of_local_nested_midpoint
      hp hp1 ψ hreal n hopen g U hUopen hgapU hg hgreal
        c₀ r₀ R hr₀ hseg₀ hR hUdisc hnest
  have heq := sourceStandardRoot_weighted_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ n g U hg H hloop hH_U hH_avoid hcontdiff
  refine ⟨μ,hμ,?_⟩
  rw [← heq]
  simpa only [curveIntegral_circlePath] using hvalue

/-- An analytic numerator has the same exact gap-side integral on a
smooth polar contour as on a midpoint circle. The polar radius stays
between a gap-enclosing inner radius and the local analytic radius. -/
theorem weighted_sourceStandardRoot_radialPath_eq_boundary_of_local_disc
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
    (hg : AnalyticOnNhd ℂ g U)
    (rmin R : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (hperiod : ρ (2 * Real.pi) = ρ 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < rmin → rmin < R → closedBall c R ⊆ U →
      (∀ θ ∈ Icc (0:ℝ) (2 * Real.pi), rmin < ρ θ ∧ ρ θ ≤ R) →
    (∫ᶜ z in radialPath c ρ hρ.continuous hperiod,
      holomorphicOneForm
        (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
      -(2 * gapSideBoundaryIntegral
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro hdrmin hrminR hUdisc hρbounds
  change d < rmin at hdrmin
  change closedBall c R ⊆ U at hUdisc
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hrmin : 0 < rmin := hd.trans hdrmin
  have hR : d < R := hdrmin.trans hrminR
  have hRpos : 0 < R := hrmin.trans hrminR
  have hsegmin : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c rmin := by
    have hm := sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 ψ hreal n (rmin-d) (sub_pos.mpr hdrmin)
    change sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+(rmin-d)) at hm
    rwa [show d+(rmin-d)=rmin by ring] at hm
  have hsegR : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R :=
    hsegmin.trans (ball_subset_ball hrminR.le)
  let H := radialHomotopy c R ρ hρ.continuous hperiod
  have hH_U : range H ⊆ U := by
    rintro z ⟨⟨s,u⟩,rfl⟩
    apply hUdisc
    exact radialHomotopy_mem_closedBall
      c R R ρ hρ.continuous hperiod hRpos.le (le_refl R)
        (by
          intro θ hθ
          exact ⟨(hrmin.trans (hρbounds θ hθ).1).le,
            (hρbounds θ hθ).2⟩)
        s u
  have hH_avoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    rintro z ⟨⟨s,u⟩,rfl⟩ hz
    have hnot := radialHomotopy_disjoint_closedBall
      c R rmin ρ hρ.continuous hperiod hrmin.le hrminR
        (fun θ hθ => (hρbounds θ hθ).1) s u
    exact hnot (ball_subset_closedBall (hsegmin hz))
  exact weighted_sourceStandardRoot_curveIntegral_eq_boundary_of_local_homotopy
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg
      c R R hRpos hsegR (radialPath c ρ hρ.continuous hperiod)
      H (radialHomotopy_loop c R ρ hρ.continuous hperiod)
      hH_U hH_avoid
      (radialHomotopy_contDiffOn c R ρ hρ.continuous hperiod hρ)
      hR hUdisc (subset_rfl)

/-- The Lemma 12.3 maximum estimate extends to a noncircular polar
contour whose radii remain inside one local analytic disc and outside
an inner disc containing the selected real gap. -/
theorem weighted_sourceStandardRoot_radialPath_max_bound_of_local_disc
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
    (hg : AnalyticOnNhd ℂ g U)
    (rmin R : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (hperiod : ρ (2 * Real.pi) = ρ 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < rmin → rmin < R → closedBall c R ⊆ U →
      (∀ θ ∈ Icc (0:ℝ) (2 * Real.pi), rmin < ρ θ ∧ ρ θ ≤ R) →
      ∃ z ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (∀ w ∈ standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n),
          ‖g w‖ ≤ ‖g z‖) ∧
        ‖(2 * (Real.pi : ℂ))⁻¹ *
          (∫ᶜ w in radialPath c ρ hρ.continuous hperiod,
            holomorphicOneForm
              (fun z => g z / sourceStandardRoot hp hp1 ψ n z) w)‖ ≤ ‖g z‖ := by
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
  intro hdrmin hrminR hUdisc hρbounds
  refine ⟨z,hz,hmax,?_⟩
  rw [weighted_sourceStandardRoot_radialPath_eq_boundary_of_local_disc
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg
      rmin R ρ hρ hperiod hdrmin hrminR hUdisc hρbounds]
  let B := gapSideBoundaryIntegral τ δ g 1 true
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (2 * (Real.pi : ℂ))⁻¹ * (-(2 * B)) =
      -(B / (Real.pi : ℂ)) := by
    field_simp [hπ]
  rw [heq,norm_neg]
  exact hbound 1 true

/-- The normalized weighted integral on such a noncircular polar
contour is the negative of one numerator value on the real gap. -/
theorem weighted_sourceStandardRoot_radialPath_real_mean_value_of_local_disc
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
    (hg : AnalyticOnNhd ℂ g U)
    (hgreal : ∀ z ∈ standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n), (g z).im = 0)
    (rmin R : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ 2 ρ)
    (hperiod : ρ (2 * Real.pi) = ρ 0) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < rmin → rmin < R → closedBall c R ⊆ U →
      (∀ θ ∈ Icc (0:ℝ) (2 * Real.pi), rmin < ρ θ ∧ ρ θ ≤ R) →
      ∃ μ ∈ standardRootGapSegment
        (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n),
        (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          (∫ᶜ z in radialPath c ρ hρ.continuous hperiod,
            holomorphicOneForm
              (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) = -g μ := by
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let δ := sourceStandardRootHalfGap hp hp1 ψ n
  have hδ : δ ≠ 0 :=
    sourceStandardRootHalfGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen
  have hgcont : ContinuousOn g (standardRootGapSegment τ δ) := by
    intro z hz
    exact ((hg z (hgapU hz)).continuousAt).continuousWithinAt
  dsimp only
  intro hdrmin hrminR hUdisc hρbounds
  apply normalized_real_mean_value_of_boundary τ δ g _ hδ hgcont hgreal
  exact weighted_sourceStandardRoot_radialPath_eq_boundary_of_local_disc
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg
      rmin R ρ hρ hperiod hdrmin hrminR hUdisc hρbounds

end NLS.ZakharovShabat
