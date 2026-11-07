import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalRoughFlow
import NLS.Articles.KdVPseudomeasures.EndpointIsospectralTorusImage
import NLS.Articles.KdVPseudomeasures.SourceWeakStarLimits

/-! Actual endpoint invariance, bounded full orbits and weak-star
continuous trajectories of the SAME physical canonical KdV flow.
Every endpoint representative is the identical original distribution. -/
noncomputable section
open Set NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem sourceOriginalPotential_injective (r : ℝ) (hr : AdmissiblePredualOrder r) :
    Function.Injective (sourceOriginalPotential r hr) := by
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg (fun a : OriginalHminusOnePotential => a.val.val) he
  simpa only [sourceOriginalPotential_val] using h

theorem exists_endpoint_hillOriginalCanonicalKdVFlow
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (t : ℝ) :
    ∃ p : Potential r, sourceOriginalPotential r hr p =
      hillOriginalCanonicalKdVFlow (sourceOriginalPotential r hr q) t :=
  exists_endpoint_representative_of_original_isospectral r hr q _
    (hillOriginalCanonicalKdVFlow_isospectral _ t)

def hillEndpointCanonicalKdVFlow (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : Potential r) (t : ℝ) : Potential r :=
  Classical.choose (exists_endpoint_hillOriginalCanonicalKdVFlow r hr q t)

theorem hillEndpointCanonicalKdVFlow_original
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (t : ℝ) :
    sourceOriginalPotential r hr (hillEndpointCanonicalKdVFlow r hr q t) =
      hillOriginalCanonicalKdVFlow (sourceOriginalPotential r hr q) t :=
  Classical.choose_spec (exists_endpoint_hillOriginalCanonicalKdVFlow r hr q t)

theorem hillEndpointCanonicalKdVFlow_zero
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    hillEndpointCanonicalKdVFlow r hr q 0 = q := by
  apply sourceOriginalPotential_injective r hr
  rw [hillEndpointCanonicalKdVFlow_original, hillOriginalCanonicalKdVFlow_zero]

theorem hillEndpointCanonicalKdVFlow_add
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (t s : ℝ) :
    hillEndpointCanonicalKdVFlow r hr (hillEndpointCanonicalKdVFlow r hr q s) t =
      hillEndpointCanonicalKdVFlow r hr q (t + s) := by
  apply sourceOriginalPotential_injective r hr
  simp only [hillEndpointCanonicalKdVFlow_original, hillOriginalCanonicalKdVFlow_add]

theorem hillEndpointCanonicalKdVFlow_isospectral
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) (t : ℝ) :
    hillEndpointCanonicalKdVFlow r hr q t ∈ endpointIsospectralSet r hr q := by
  apply (mem_endpointIsospectralSet_iff_original r hr q _).mpr
  rw [hillEndpointCanonicalKdVFlow_original]
  exact hillOriginalCanonicalKdVFlow_isospectral _ t

theorem exists_uniform_norm_bound_hillEndpointCanonicalKdVFlow
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖(hillEndpointCanonicalKdVFlow r hr q t).val‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := sourceLemma3_5_i r hr q
  exact ⟨C,hC,fun t => hb _ (hillEndpointCanonicalKdVFlow_isospectral r hr q t)⟩

def hillEndpointWeakStarKdVFlow (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) (t : ℝ) : WeakStarPotential r :=
  ⟨hillEndpointCanonicalKdVFlow r hr q.toPotential t⟩

theorem hillEndpointWeakStarKdVFlow_lower
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : WeakStarPotential r) (t : ℝ) :
    sourceLowerDistribution r (-1) (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) (hillEndpointWeakStarKdVFlow r hr q t) =
      (hillOriginalCanonicalKdVFlow (sourceOriginalPotential r hr q.toPotential) t).val := by
  rw [sourceLowerDistribution_eq_potentialHminusOne r hr]
  exact congrArg Subtype.val (hillEndpointCanonicalKdVFlow_original r hr q.toPotential t)

theorem potentialNormBounded_range_hillEndpointWeakStarKdVFlow
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : WeakStarPotential r) :
    PotentialNormBounded r (range (hillEndpointWeakStarKdVFlow r hr q)) := by
  obtain ⟨C,_,hC⟩ := exists_uniform_norm_bound_hillEndpointCanonicalKdVFlow r hr q.toPotential
  exact ⟨C,fun _ ⟨t,ht⟩ => ht ▸ hC t⟩

theorem continuous_hillEndpointWeakStarKdVFlow_time
    (r : ℝ) (hr : AdmissiblePredualOrder r) (q : WeakStarPotential r) :
    Continuous (hillEndpointWeakStarKdVFlow r hr q) := by
  let A := range (hillEndpointWeakStarKdVFlow r hr q)
  let f : ℝ → A := fun t => ⟨hillEndpointWeakStarKdVFlow r hr q t,mem_range_self t⟩
  have hc : Continuous f := (continuous_source_iff_lowerDistribution r (-1) (p := 2)
    (by norm_num) (admissible_hminusOne_threshold r hr) A
    (potentialNormBounded_range_hillEndpointWeakStarKdVFlow r hr q) f).mpr (by
      have he : (fun t : ℝ => sourceLowerDistribution r (-1) (p := 2) (by norm_num)
          (admissible_hminusOne_threshold r hr) (f t).val) =
          (fun t => (hillOriginalCanonicalKdVFlow (sourceOriginalPotential r hr q.toPotential) t).val) :=
        funext (fun t => hillEndpointWeakStarKdVFlow_lower r hr q t)
      rw [he]
      exact continuous_hillOriginalCanonicalKdVFlow_val_time _)
  exact continuous_subtype_val.comp hc

end NLS.Articles.KdVPseudomeasures
