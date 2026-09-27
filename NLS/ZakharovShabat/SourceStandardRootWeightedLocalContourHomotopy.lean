import NLS.ZakharovShabat.SourceStandardRootWeightedLocalCircleValue
import NLS.ComplexAnalysis.NestedCircleHomotopy

/-!
# Local weighted contour homotopy

The weighted selected-root quotient is holomorphic wherever its
numerator is analytic and the selected periodic gap is avoided.
Smooth loop homotopies in that local set preserve its integral.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped unitInterval ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A smooth closed-loop homotopy preserves the weighted selected-root
integral when its compact image stays in the numerator's analytic
domain and avoids the selected gap. -/
theorem sourceStandardRoot_weighted_curveIntegral_eq_of_homotopy_range
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (g : ℂ → ℂ) (U : Set ℂ) (hg : AnalyticOnNhd ℂ g U)
    {a b : ℂ} {γ₁ : Path a a} {γ₂ : Path b b}
    (H : (γ₁ : C(I, ℂ)).Homotopy γ₂)
    (hloop : ∀ s : I, H (s, 1) = H (s, 0))
    (hU : range H ⊆ U)
    (havoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ)
    (hcontdiff : ContDiffOn ℝ 2
      (fun xy : ℝ × ℝ => Set.IccExtend zero_le_one (H.extend xy.1) xy.2)
      (Icc 0 1)) :
    (∫ᶜ z in γ₁, holomorphicOneForm
      (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z) =
      ∫ᶜ z in γ₂, holomorphicOneForm
        (fun w => g w / sourceStandardRoot hp hp1 ψ n w) z := by
  have hclosed : IsClosed (range H) :=
    (isCompact_range (map_continuous H)).isClosed
  apply curveIntegral_eq_of_holomorphic_homotopy
    (fun w => g w / sourceStandardRoot hp hp1 ψ n w)
    H hloop (t := range H)
  · intro s _ u _
    exact ⟨(s,u),rfl⟩
  · intro z hz
    have hz' : z ∈ range H := by simpa only [hclosed.closure_eq] using hz
    have hnot : z ∉ sourcePeriodicSegment hp hp1 ψ n := havoid hz'
    exact ((hg z (hU hz')).div
      (sourceStandardRoot_analyticAt hp hp1 ψ n z hnot)
      (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hnot)).differentiableAt
  · exact hcontdiff

/-- Two nested enclosing circles, possibly with different centers,
have equal weighted selected-root integrals when the numerator is
analytic near the larger filled disc. Other periodic gaps are irrelevant
for this single-root quotient. -/
theorem circleIntegral_weighted_sourceStandardRoot_eq_of_local_nestedCircles
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (g : ℂ → ℂ) (U : Set ℂ) (hg : AnalyticOnNhd ℂ g U)
    (c₀ c₁ : ℂ) (r₀ r₁ : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁)
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀)
    (hseg₁ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₁ r₁)
    (hnest : closedBall c₀ r₀ ⊆ closedBall c₁ r₁)
    (hU : closedBall c₁ r₁ ⊆ U) :
    (∮ z in C(c₀,r₀), g z / sourceStandardRoot hp hp1 ψ n z) =
      ∮ z in C(c₁,r₁), g z / sourceStandardRoot hp hp1 ψ n z := by
  let f : ℂ → ℂ := fun w => g w / sourceStandardRoot hp hp1 ψ n w
  let H := ContinuousMap.Homotopy.affine
    (circlePath c₀ r₀ : C(I, ℂ))
    (circlePath c₁ r₁ : C(I, ℂ))
  have hUrange : range H ⊆ U := by
    rintro z ⟨⟨s,u⟩,rfl⟩
    exact hU (affineCircleHomotopy_mem_outer_closedBall
      c₀ c₁ r₀ r₁ hr₀.le hr₁.le hnest s u)
  have havoid : range H ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ := by
    rintro z ⟨⟨s,u⟩,rfl⟩ hz
    exact (affineCircleHomotopy_ne_of_mem_both_balls
      c₀ c₁ _ r₀ r₁ (hseg₀ hz) (hseg₁ hz) s u) rfl
  have heq := sourceStandardRoot_weighted_curveIntegral_eq_of_homotopy_range
    hp hp1 ψ n g U hg H
    (affineHomotopy_loop (γ₁ := circlePath c₀ r₀)
      (γ₂ := circlePath c₁ r₁))
    hUrange havoid
    (affineHomotopy_contDiffOn
      (circlePath_contDiffOn c₀ r₀)
      (circlePath_contDiffOn c₁ r₁))
  calc
    (∮ z in C(c₀,r₀), f z) =
        ∫ᶜ z in circlePath c₀ r₀, holomorphicOneForm f z :=
      (curveIntegral_circlePath f c₀ r₀).symm
    _ = ∫ᶜ z in circlePath c₁ r₁, holomorphicOneForm f z := heq
    _ = ∮ z in C(c₁,r₁), f z := curveIntegral_circlePath f c₁ r₁

/-- An enclosing circle may have any center, provided it lies inside
one midpoint disc on which the numerator is analytic. Its weighted
integral has the same exact gap-side value as the midpoint circle. -/
theorem weighted_sourceStandardRoot_circle_eq_boundary_of_local_nested_midpoint
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
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    d < R → closedBall c R ⊆ U →
      closedBall c₀ r₀ ⊆ closedBall c R →
    (∮ z in C(c₀,r₀), g z / sourceStandardRoot hp hp1 ψ n z) =
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
  intro hR hU hnest
  change d < R at hR
  change closedBall c R ⊆ U at hU
  change closedBall c₀ r₀ ⊆ closedBall c R at hnest
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    exact div_pos (sub_pos.mpr hopen) (by norm_num)
  have hRpos : 0 < R := lt_trans hd hR
  have hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    have hm := sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 ψ hreal n (R-d) (sub_pos.mpr hR)
    change sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+(R-d)) at hm
    rwa [show d+(R-d)=R by ring] at hm
  exact (circleIntegral_weighted_sourceStandardRoot_eq_of_local_nestedCircles
    hp hp1 ψ n g U hg c₀ c r₀ R hr₀ hRpos hseg₀ hseg hnest hU).trans
      (weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_local_disc
        hp hp1 ψ hreal n hopen g U hUopen hgapU hg R hR hU)

/-- The Lemma 12.3 maximum bound holds for enclosing circles with
arbitrary centers inside an analytic midpoint disc. -/
theorem weighted_sourceStandardRoot_circle_max_bound_of_local_nested_midpoint
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
    (hseg₀ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c₀ r₀) :
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
        ‖(2*Real.pi:ℂ)⁻¹ *
          (∮ w in C(c₀,r₀),
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
  intro hR hU hnest
  refine ⟨z,hz,hmax,?_⟩
  rw [weighted_sourceStandardRoot_circle_eq_boundary_of_local_nested_midpoint
    hp hp1 ψ hreal n hopen g U hUopen hgapU hg
      c₀ r₀ R hr₀ hseg₀ hR hU hnest]
  let B := gapSideBoundaryIntegral τ δ g 1 true
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (2*Real.pi:ℂ)⁻¹ * (-(2*B)) = -(B/(Real.pi:ℂ)) := by
    field_simp [hπ]
  rw [heq,norm_neg]
  exact hbound 1 true

end NLS.ZakharovShabat
