import NLS.ZakharovShabat.SourceStandardRootWeightedLocalRealMeanValue

/-! # Exact gap-side values on real-centered enclosing circles

A smaller midpoint disc and nested contour deformation remove the need
for a midpoint-centered original contour. Numerators may be complex valued.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cosine-coordinate closed gap is the original periodic segment. -/
theorem sourceStandardRoot_gapSegment_eq_periodicSegment
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) = sourcePeriodicSegment hp hp1 ψ n := by
  apply Subset.antisymm
  · rintro z ⟨t,ht,rfl⟩
    exact sourceCanonicalRootGapPoint_mem_segment hp hp1 ψ n t ht.1 ht.2
  · intro z hz
    rw [sourcePeriodicSegment,segment_eq_image_lineMap] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    refine ⟨2*t-1,⟨by linarith [ht.1],by linarith [ht.2]⟩,?_⟩
    simp only [sourceStandardRootMidpoint,sourceStandardRootHalfGap,
      canonicalPeriodicMidpoint,canonicalPeriodicGap,AffineMap.lineMap_apply_module,
      Complex.real_smul,ofReal_sub,ofReal_mul,ofReal_ofNat,ofReal_one]
    ring

/-- Shrinking any real-centered enclosing circle to an open real gap gives
minus twice the upper-side integral, with its fixed orientation. -/
theorem weighted_sourceStandardRoot_realCenteredCircle_eq_boundary
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (x q : ℝ) (hq : 0 < q)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball (x:ℂ) q)
    (hg : AnalyticOnNhd ℂ g (closedBall (x:ℂ) q)) :
    (∮ z in C((x:ℂ),q), g z / sourceStandardRoot hp hp1 ψ n z) =
      -(2 * gapSideBoundaryIntegral (sourceStandardRootMidpoint hp hp1 ψ n)
        (sourceStandardRootHalfGap hp hp1 ψ n) g 1 true) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ρ,hρ,hnest⟩ := exists_sourceStandardRoot_innerMidpointDisc_of_realCenteredCircle
    hp hp1 ψ hreal n x q hseg
  have hd : 0 < d := div_pos (sub_pos.mpr hopen) (by norm_num)
  have hρpos : 0 < ρ := hd.trans hρ
  have hsegρ : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c ρ := by
    have h := sourcePeriodicSegment_subset_midpoint_ball hp hp1 ψ hreal n (ρ-d) (sub_pos.mpr hρ)
    change sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+(ρ-d)) at h
    simpa only [add_sub_cancel] using h
  have hgap : standardRootGapSegment (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆ ball (x:ℂ) q := by
    rw [sourceStandardRoot_gapSegment_eq_periodicSegment]
    exact hseg
  exact (circleIntegral_weighted_sourceStandardRoot_eq_of_local_nestedCircles
    hp hp1 ψ n g (closedBall (x:ℂ) q) hg c (x:ℂ) ρ q hρpos hq hsegρ hseg
      (hnest.trans ball_subset_closedBall) Subset.rfl).symm.trans
    (weighted_sourceStandardRoot_midpointCircle_eq_boundary_of_local_disc
      hp hp1 ψ hreal n hopen g (ball (x:ℂ) q) isOpen_ball hgap
        (hg.mono ball_subset_closedBall) ρ hρ hnest)

/-- The normalized contour is bounded by the attained maximum of the
complex numerator on the real gap, independently of the enclosing radius. -/
theorem weighted_sourceStandardRoot_realCenteredCircle_max_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)
    (g : ℂ → ℂ) (x q : ℝ) (hq : 0 < q)
    (hseg : sourcePeriodicSegment hp hp1 ψ n ⊆ ball (x:ℂ) q)
    (hg : AnalyticOnNhd ℂ g (closedBall (x:ℂ) q)) :
    ∃ z ∈ sourcePeriodicSegment hp hp1 ψ n,
      (∀ w ∈ sourcePeriodicSegment hp hp1 ψ n, ‖g w‖ ≤ ‖g z‖) ∧
      ‖(2*Real.pi:ℂ)⁻¹ *
        (∮ w in C((x:ℂ),q), g w / sourceStandardRoot hp hp1 ψ n w)‖ ≤ ‖g z‖ := by
  have hcont : ContinuousOn g (standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n) (sourceStandardRootHalfGap hp hp1 ψ n)) := by
    rw [sourceStandardRoot_gapSegment_eq_periodicSegment]
    exact hg.continuousOn.mono (hseg.trans ball_subset_closedBall)
  obtain ⟨z,hz,hmax,hbound⟩ := sourceStandardRoot_gapSideBoundaryIntegral_uniform_max_bound
    hp hp1 ψ n (sourceCanonicalPeriodicGap_ne_zero_of_openRealGap hp hp1 ψ hreal n hopen) g hcont
  rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hz hmax
  refine ⟨z,hz,hmax,?_⟩
  rw [weighted_sourceStandardRoot_realCenteredCircle_eq_boundary hp hp1 ψ hreal n hopen g x q hq hseg hg]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq (B : ℂ) : (2*Real.pi:ℂ)⁻¹ * (-(2*B)) = -(B/(Real.pi:ℂ)) := by
    field_simp [hπ]
  rw [heq,norm_neg]
  exact hbound 1 true

end NLS.ZakharovShabat
