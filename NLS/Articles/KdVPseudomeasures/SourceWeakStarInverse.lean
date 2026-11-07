import NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets

/-!
# Compactness criteria for inverse weak-star continuity

These consequences of Appendix B retain the original endpoint bounds and
the entire physical distributions. A closed bounded physical domain makes
every continuous injective map into a physical weak-star space a closed
embedding. A bounded image lets Fourier or lower norm tests establish the
forward continuity. Inverse continuity is then a conclusion.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

/-- For an ambient physical map with bounded image, continuity is detected
by the original Fourier coefficients. -/
theorem continuous_sourceMap_iff_coefficients (r : ℝ)
    {X : Type*} [TopologicalSpace X] (f : X → WeakStarPotential r)
    (hb : PotentialNormBounded r (range f)) :
    Continuous f ↔ ∀ n : ℤ,
      Continuous (fun x => (f x).toPotential.val.val (mode (-n))) := by
  let g : X → range f := fun x => ⟨f x, mem_range_self x⟩
  have hg : Continuous g ↔ Continuous f :=
    Topology.IsEmbedding.subtypeVal.continuous_iff
  exact hg.symm.trans (continuous_source_iff_coefficients r (range f) hb g)

/-- Compactness of the physical domain supplies inverse continuity without
any endpoint bound on the image, when forward continuity is already known. -/
theorem isClosedEmbedding_sourceMap_of_closed_bounded (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hf : Continuous f) (hi : Function.Injective f) :
    Topology.IsClosedEmbedding f := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp
    ((isCompact_source_iff_bounded_closed s A).mpr ⟨hb, hc⟩)
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  exact hf.isClosedEmbedding hi

/-- Fourier-continuous injective maps on closed bounded physical sets are
closed embeddings, provided their images are endpoint norm bounded. -/
theorem isClosedEmbedding_sourceMap_of_bounded_coefficients (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hfb : PotentialNormBounded r (range f))
    (hf : ∀ n : ℤ, Continuous (fun x => (f x).toPotential.val.val (mode (-n))))
    (hi : Function.Injective f) : Topology.IsClosedEmbedding f :=
  isClosedEmbedding_sourceMap_of_closed_bounded s r A hb hc f
    ((continuous_sourceMap_iff_coefficients r f hfb).mpr hf) hi

/-- The weak-star homeomorphism onto the exact physical image. -/
def sourceMapHomeomorphRange (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hf : Continuous f) (hi : Function.Injective f) :
    A ≃ₜ range f :=
  (isClosedEmbedding_sourceMap_of_closed_bounded s r A hb hc f hf hi).isEmbedding.toHomeomorph

/-- The homeomorphism uses the supplied physical map itself. -/
theorem sourceMapHomeomorphRange_apply (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hf : Continuous f) (hi : Function.Injective f) (a : A) :
    (sourceMapHomeomorphRange s r A hb hc f hf hi a).val = f a := rfl

/-- Recovering a physical point from its image returns the same point. -/
theorem sourceMapHomeomorphRange_symm_apply (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hf : Continuous f) (hi : Function.Injective f) (a : A) :
    (sourceMapHomeomorphRange s r A hb hc f hf hi).symm ⟨f a, mem_range_self a⟩ = a :=
  (isClosedEmbedding_sourceMap_of_closed_bounded s r A hb hc f hf hi).isEmbedding.toHomeomorph_symm_apply a

/-- Closed physical constraints are carried to ambient weak-star closed
constraints by a continuous injective map on a closed bounded domain. -/
theorem isClosed_sourceMap_image_iff (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hf : Continuous f) (hi : Function.Injective f)
    (B : Set A) : IsClosed (f '' B) ↔ IsClosed B :=
  (isClosedEmbedding_sourceMap_of_closed_bounded s r A hb hc f hf hi).isClosed_iff_image_isClosed.symm

/-- Every filter, not just sequences, detects convergence before and after
a continuous injective map on a closed bounded physical domain. -/
theorem tendsto_sourceMap_iff_of_closed_bounded (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hf : Continuous f) (hi : Function.Injective f)
    {X : Type*} {l : Filter X} (x : X → A) (a : A) :
    Tendsto (f ∘ x) l (𝓝 (f a)) ↔ Tendsto x l (𝓝 a) :=
  (isClosedEmbedding_sourceMap_of_closed_bounded s r A hb hc f hf hi).isEmbedding.tendsto_nhds_iff.symm

/-- Inverse continuity can independently use any admissible original lower
finite-p norms on the two sides. The endpoint image bound remains explicit. -/
theorem tendsto_sourceMap_lower_iff_lower_of_closed_bounded (s r t u : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (ht : 1 < (-s-t)*p.toReal)
    (hq : q ≠ ⊤) (hu : 1 < (-r-u)*q.toReal)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hfb : PotentialNormBounded r (range f))
    (hf : Continuous f) (hi : Function.Injective f)
    {X : Type*} {l : Filter X} (x : X → A) (a : A) :
    Tendsto (fun k => sourceLowerDistribution r u hq hu (f (x k))) l
      (𝓝 (sourceLowerDistribution r u hq hu (f a))) ↔
    Tendsto (fun k => sourceLowerDistribution s t hp ht (x k).val) l
      (𝓝 (sourceLowerDistribution s t hp ht a.val)) := by
  have hfx : PotentialNormBounded r (range (f ∘ x)) := by
    obtain ⟨R, hR⟩ := hfb
    refine ⟨R, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact hR _ (mem_range_self (x k))
  exact (tendsto_source_iff_lowerDistribution_of_bounded r u hq hu (f ∘ x) (f a) hfx).symm.trans
    ((tendsto_sourceMap_iff_of_closed_bounded s r A hb hc f hf hi x a).trans
      (tendsto_source_iff_lowerDistribution s t hp ht A hb x a))

/-- In the article range, inverse convergence is detected by the identical
original H-minus-one distributions on both sides. -/
theorem tendsto_sourceMap_originalHminusOne_iff_of_closed_bounded (s r : ℝ)
    (hs : AdmissiblePredualOrder s) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential s)) (hb : PotentialNormBounded s A) (hc : IsClosed A)
    (f : A → WeakStarPotential r) (hfb : PotentialNormBounded r (range f))
    (hf : Continuous f) (hi : Function.Injective f)
    {X : Type*} {l : Filter X} (x : X → A) (a : A) :
    Tendsto (fun k => potentialHminusOne r hr (f (x k)).toPotential) l
      (𝓝 (potentialHminusOne r hr (f a).toPotential)) ↔
    Tendsto (fun k => potentialHminusOne s hs (x k).val.toPotential) l
      (𝓝 (potentialHminusOne s hs a.val.toPotential)) := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne s hs,
    sourceLowerDistribution_eq_potentialHminusOne r hr] using
    tendsto_sourceMap_lower_iff_lower_of_closed_bounded s r (-1) (-1) (p := 2) (q := 2)
      (by norm_num) (admissible_hminusOne_threshold s hs)
      (by norm_num) (admissible_hminusOne_threshold r hr) A hb hc f hfb hf hi x a

end NLS.Articles.KdVPseudomeasures
