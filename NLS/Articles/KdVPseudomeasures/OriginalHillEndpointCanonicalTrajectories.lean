import NLS.Articles.KdVPseudomeasures.OriginalHillEndpointCanonicalFlow

/-! The compact-open physical weak-star trajectory map on EVERY bounded
KdV-invariant endpoint subset. Appendix B transfers actual rough norm
continuity, with no compactness or closedness assumption on that subset. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

def HillEndpointKdVInvariant (r : ℝ) (hr : AdmissiblePredualOrder r)
    (V : Set (WeakStarPotential r)) : Prop :=
  ∀ q ∈ V, ∀ t : ℝ, hillEndpointWeakStarKdVFlow r hr q t ∈ V

theorem continuous_sourceOriginalPotential_on_bounded
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (V : Set (WeakStarPotential r)) (hb : PotentialNormBounded r V) :
    Continuous (fun q : V => sourceOriginalPotential r hr q.val.toPotential) := by
  have h : Continuous (fun q : V => (⟨sourceLowerDistribution r (-1) (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) q.val,
      sourceLowerDistribution_source_conditions r (-1) (p := 2) (by norm_num)
        (admissible_hminusOne_threshold r hr) q.val⟩ : OriginalHminusOnePotential)) :=
    (sourceLowerDistributionMapOn r (-1) (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) V hb).continuous.subtype_mk _
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr, sourceOriginalPotential] using! h

def hillEndpointWeakStarKdVTrajectoryOn (r : ℝ) (hr : AdmissiblePredualOrder r)
    (V : Set (WeakStarPotential r)) (hV : HillEndpointKdVInvariant r hr V)
    (T : ℝ) (q : V) : C(Icc (-T) T, V) where
  toFun t := ⟨hillEndpointWeakStarKdVFlow r hr q.val t.val, hV q.val q.property t.val⟩
  continuous_toFun := ((continuous_hillEndpointWeakStarKdVFlow_time r hr q.val).comp
    continuous_subtype_val).subtype_mk _

theorem continuous_hillEndpointWeakStarKdVTrajectoryOn
    (r : ℝ) (hr : AdmissiblePredualOrder r)
    (V : Set (WeakStarPotential r)) (hb : PotentialNormBounded r V)
    (hV : HillEndpointKdVInvariant r hr V) (T : ℝ) :
    Continuous (hillEndpointWeakStarKdVTrajectoryOn r hr V hV T) := by
  apply (continuous_sourceTrajectory_iff_lowerDistribution r (-1) (p := 2)
    (by norm_num) (admissible_hminusOne_threshold r hr) V hb _).mpr
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : V × Icc (-T) T => sourceLowerDistribution r (-1) (p := 2)
    (by norm_num) (admissible_hminusOne_threshold r hr)
      (hillEndpointWeakStarKdVFlow r hr p.1.val p.2.val))
  simp only [hillEndpointWeakStarKdVFlow_lower]
  have hi : Continuous (fun p : V × Icc (-T) T =>
      (p.2.val, sourceOriginalPotential r hr p.1.val.toPotential)) :=
    (continuous_subtype_val.comp continuous_snd).prodMk
      ((continuous_sourceOriginalPotential_on_bounded r hr V hb).comp continuous_fst)
  have h := continuous_subtype_val.comp (continuous_hillOriginalCanonicalKdVFlow.comp hi)
  simpa only [Function.comp_def] using! h

theorem isCompact_closure_range_hillEndpointWeakStarKdVFlow
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : WeakStarPotential r) :
    IsCompact (closure (range (hillEndpointWeakStarKdVFlow r hr q))) :=
  isCompact_closure_source_of_bounded r _ (potentialNormBounded_range_hillEndpointWeakStarKdVFlow r hr q)

end NLS.Articles.KdVPseudomeasures
