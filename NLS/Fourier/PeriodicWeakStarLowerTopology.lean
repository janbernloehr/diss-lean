import NLS.Fourier.PeriodicEndpointLowerInclusion
import NLS.Fourier.PeriodicWeightedWeakStar

/-! # Lower norm topology on the original periodic distributions

Appendix B's lower norm spaces can be taken to be the original distribution
spaces, rather than just their coefficient realizations. The full normalized
smooth-test distribution is unchanged, and all bounded-set topology and
closure statements are transported through the Fourier isometry.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Fourier.PeriodicFourierLebesgue
open SmoothPeriodicTest
variable {L : ℝ} [Fact (0 < L)] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An endpoint weak-star point as an original lower order distribution. -/
def lowerWeakStarDistribution (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    FourierLebesgueSpace L t p :=
  (sobolevCoefficients t p).symm (WeightedCoeff.lowerWeakStarRealization r t hp h f)

/-- Every original Fourier coefficient is retained. -/
theorem lowerWeakStarDistribution_coefficient (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) (n : ℤ) :
    (lowerWeakStarDistribution (L := L) r t hp h f).val (mode (-n)) =
      WeightedCoeff.weakStarCoordinates r f n := by
  change ((sobolevCoefficients t p) ((sobolevCoefficients t p).symm
    (WeightedCoeff.lowerWeakStarRealization r t hp h f))).val n = _
  rw [LinearIsometryEquiv.apply_symm_apply, WeightedCoeff.lowerWeakStarRealization_val]

/-- The entire original smooth-test distribution, not only its norm or
coefficients, is preserved in the lower order space. -/
theorem lowerWeakStarDistribution_val (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (f : WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)) :
    (lowerWeakStarDistribution (L := L) r t hp h f).val =
      ((sobolevCoefficients (-r) ⊤).symm (WeightedCoeff.weakStarCoeff r f)).val := by
  apply Distribution.ext_coefficients
  intro n
  rw [lowerWeakStarDistribution_coefficient]
  change WeightedCoeff.weakStarCoordinates r f n =
    ((sobolevCoefficients (-r) ⊤) ((sobolevCoefficients (-r) ⊤).symm
      (WeightedCoeff.weakStarCoeff r f))).val n
  rw [LinearIsometryEquiv.apply_symm_apply, WeightedCoeff.weakStarCoeff_val]

/-- Compatibility with the existing inclusion of original distributions. -/
theorem lowerWeakStarDistribution_realization (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal) (u : FourierLebesgueSpace L (-r) ⊤) :
    lowerWeakStarDistribution r t hp h
      (WeightedCoeff.wienerDualRealization r (sobolevCoefficients (-r) ⊤ u)) =
        endpointLowerInclusion (-r) t hp h u := by
  simp only [lowerWeakStarDistribution, WeightedCoeff.lowerWeakStarRealization,
    WeightedCoeff.weakStarCoeff_wienerDualRealization]
  rfl

/-- The original lower norm space induces the exact endpoint topology on
every bounded set. This controls arbitrary filters. -/
theorem isEmbedding_lowerWeakStarDistribution_on_bounded (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) :
    Topology.IsEmbedding (fun f : A => lowerWeakStarDistribution (L := L) r t hp h f.val) :=
  (sobolevCoefficients t p).symm.toHomeomorph.isEmbedding.comp
    (WeightedCoeff.isEmbedding_lowerWeakStarRealization_on_bounded r t hp h A hb)

/-- Arbitrary-filter convergence in the actual original lower norm space
is equivalent to weak-star convergence within a common bounded set. -/
theorem tendsto_weakStar_subtype_iff_lowerDistribution (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) {X : Type*} {l : Filter X} (f : X → A) (a : A) :
    Tendsto f l (𝓝 a) ↔
      Tendsto (fun x => lowerWeakStarDistribution (L := L) r t hp h (f x).val) l
        (𝓝 (lowerWeakStarDistribution r t hp h a.val)) :=
  (isEmbedding_lowerWeakStarDistribution_on_bounded r t hp h A hb).tendsto_nhds_iff

/-- Compactness is measured in the original lower norm distribution space. -/
theorem isCompact_weakStar_iff_bounded_lowerDistribution_compact (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1))) :
    IsCompact A ↔ Bornology.IsBounded A ∧
      IsCompact (lowerWeakStarDistribution (L := L) r t hp h '' A) := by
  rw [WeightedCoeff.isCompact_weakStar_iff_bounded_lower_compact r t hp h A]
  apply and_congr Iff.rfl
  change IsCompact (WeightedCoeff.lowerWeakStarRealization r t hp h '' A) ↔
    IsCompact (((sobolevCoefficients (L := L) t p).symm ∘
      WeightedCoeff.lowerWeakStarRealization r t hp h) '' A)
  rw [Set.image_comp]
  exact (sobolevCoefficients (L := L) t p).symm.toHomeomorph.isEmbedding.isCompact_iff

/-- Weak-star closure of bounded endpoint data is exactly the closure in
the original lower norm distribution space, with no change of action. -/
theorem closure_lowerWeakStarDistribution_image (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded A) :
    closure (lowerWeakStarDistribution (L := L) r t hp h '' A) =
      lowerWeakStarDistribution r t hp h '' closure A := by
  have he := (sobolevCoefficients (L := L) t p).symm.toHomeomorph.isClosedEmbedding.closure_image_eq
    (WeightedCoeff.lowerWeakStarRealization r t hp h '' A)
  change closure ((sobolevCoefficients (L := L) t p).symm ''
    (WeightedCoeff.lowerWeakStarRealization r t hp h '' A)) =
    (sobolevCoefficients (L := L) t p).symm ''
      closure (WeightedCoeff.lowerWeakStarRealization r t hp h '' A) at he
  rw [WeightedCoeff.closure_lowerWeakStarRealization_image r t hp h A hb] at he
  change closure (((sobolevCoefficients (L := L) t p).symm ∘
    WeightedCoeff.lowerWeakStarRealization r t hp h) '' A) =
    ((sobolevCoefficients (L := L) t p).symm ∘
      WeightedCoeff.lowerWeakStarRealization r t hp h) '' closure A
  simpa only [Set.image_comp] using he

/-- The original lower distribution realization as a continuous map on
a bounded endpoint set. -/
def lowerWeakStarDistributionMapOn (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded V) : C(V, FourierLebesgueSpace L t p) :=
  ⟨fun f => lowerWeakStarDistribution r t hp h f.val,
    (isEmbedding_lowerWeakStarDistribution_on_bounded r t hp h V hb).continuous⟩

/-- The equivalence of topologies persists on the full compact-open
trajectory spaces of original distributions. -/
theorem isEmbedding_lowerWeakStarDistributionTrajectory (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded V) {K : Type*} [TopologicalSpace K] :
    Topology.IsEmbedding ((lowerWeakStarDistributionMapOn r t hp h V hb).comp :
      C(K,V) → C(K, FourierLebesgueSpace L t p)) :=
  ContinuousMap.isEmbedding_postcomp _
    (isEmbedding_lowerWeakStarDistribution_on_bounded r t hp h V hb)

/-- Continuous dependence with values in weak-star trajectories is equivalent
to continuous dependence in original lower norm distribution trajectories. -/
theorem continuous_weakStarTrajectory_iff_lowerDistribution (r t : ℝ) (hp : p ≠ ⊤)
    (h : 1 < (-r-t)*p.toReal)
    (V : Set (WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1)))
    (hb : Bornology.IsBounded V)
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X] (S : X → C(K,V)) :
    Continuous S ↔ Continuous (fun x =>
      (lowerWeakStarDistributionMapOn (L := L) r t hp h V hb).comp (S x)) :=
  (isEmbedding_lowerWeakStarDistributionTrajectory r t hp h V hb).continuous_iff

end NLS.Fourier.PeriodicFourierLebesgue
