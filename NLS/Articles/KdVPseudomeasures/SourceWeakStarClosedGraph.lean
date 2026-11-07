import NLS.FunctionalAnalysis.CompactClosedGraph
import NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets

/-!
# Closed graphs for bounded physical weak-star maps

Only the image requires an endpoint norm bound. The ambient source space
need not be metrizable. Sequential graph tests additionally require a
bounded physical domain; its topology and the image-closure topology are
then metrizable by Appendix B.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- A map with bounded physical image is continuous exactly when its graph
is closed in the full weak-star product topology. -/
theorem continuous_source_iff_isClosed_graph_of_bounded (r : ℝ)
    {X : Type*} [TopologicalSpace X] (f : X → WeakStarPotential r)
    (hb : PotentialNormBounded r (range f)) :
    Continuous f ↔ IsClosed {p : X × WeakStarPotential r | f p.1 = p.2} := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  let C := closure (range f)
  let : CompactSpace C := isCompact_iff_compactSpace.mp
    ((isCompact_closure_source_iff_bounded r _).mpr hb)
  let g : X → C := fun x => ⟨f x, subset_closure (mem_range_self x)⟩
  constructor
  · intro hf
    exact isClosed_eq (hf.comp continuous_fst) continuous_snd
  · intro hg
    have hgc : IsClosed {p : X × C | g p.1 = p.2} := by
      have hc : Continuous (fun p : X × C => (p.1, p.2.val)) :=
        continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
      convert hg.preimage hc using 1
      ext p
      exact Subtype.ext_iff
    have hcont := (NLS.continuous_iff_isClosed_graph_compact_target g).mpr hgc
    exact continuous_subtype_val.comp hcont

/-- On a bounded physical domain, continuity of a bounded physical map can
be checked by the uniqueness of limits of convergent graph sequences. -/
theorem continuous_source_iff_seq_graph_of_bounded (s r : ℝ)
    (A : Set (WeakStarPotential s)) (hA : PotentialNormBounded s A)
    (f : A → WeakStarPotential r) (hb : PotentialNormBounded r (range f)) :
    Continuous f ↔ ∀ (x : ℕ → A) (a : A) (b : WeakStarPotential r),
      Tendsto x atTop (𝓝 a) → Tendsto (f ∘ x) atTop (𝓝 b) → f a = b := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  let := metrizable_source_of_bounded s A hA
  let C := closure (range f)
  let : CompactSpace C := isCompact_iff_compactSpace.mp
    ((isCompact_closure_source_iff_bounded r _).mpr hb)
  let := metrizable_source_of_bounded r C
    ((potentialNormBounded_closure_iff r _).mpr hb)
  let g : A → C := fun a => ⟨f a, subset_closure (mem_range_self a)⟩
  constructor
  · intro hf x a b hx hb'
    exact tendsto_nhds_unique (hf.continuousAt.tendsto.comp hx) hb'
  · intro hgraph
    have hgc : IsClosed {p : A × C | g p.1 = p.2} := by
      apply isSeqClosed_iff_isClosed.mp
      intro x a hx ht
      apply Subtype.ext
      apply hgraph (fun n => (x n).1) a.1 a.2.val
        (continuous_fst.continuousAt.tendsto.comp ht)
      have he : (fun n => f (x n).1) = fun n => (x n).2.val := by
        funext n
        exact congrArg Subtype.val (hx n)
      change Tendsto (fun n => f (x n).1) atTop (𝓝 a.2.val)
      rw [he]
      exact (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp ht
    exact continuous_subtype_val.comp
      ((NLS.continuous_iff_isClosed_graph_compact_target g).mpr hgc)

/-- The sequential graph criterion can use any admissible original lower
norm on each side, independently. The endpoint bounds stay explicit. -/
theorem continuous_source_iff_seq_lower_graph_of_bounded (s r t u : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (ht : 1 < (-s-t)*p.toReal)
    (hq : q ≠ ⊤) (hu : 1 < (-r-u)*q.toReal)
    (A : Set (WeakStarPotential s)) (hA : PotentialNormBounded s A)
    (f : A → WeakStarPotential r) (hb : PotentialNormBounded r (range f)) :
    Continuous f ↔ ∀ (x : ℕ → A) (a : A) (b : WeakStarPotential r),
      Tendsto (fun n => sourceLowerDistribution s t hp ht (x n).val) atTop
        (𝓝 (sourceLowerDistribution s t hp ht a.val)) →
      Tendsto (fun n => sourceLowerDistribution r u hq hu (f (x n))) atTop
        (𝓝 (sourceLowerDistribution r u hq hu b)) → f a = b := by
  rw [continuous_source_iff_seq_graph_of_bounded s r A hA f hb]
  apply forall_congr' fun x => forall_congr' fun a => forall_congr' fun b => ?_
  have hfx : PotentialNormBounded r (range (f ∘ x)) := by
    obtain ⟨R, hR⟩ := hb
    refine ⟨R, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hR _ (mem_range_self (x n))
  rw [tendsto_source_iff_lowerDistribution s t hp ht A hA x a,
    tendsto_source_iff_lowerDistribution_of_bounded r u hq hu (f ∘ x) b hfx]
  rfl

/-- In the article's regularity range both sides of the bounded graph test
may use the norm of the identical original H-minus-one distribution. -/
theorem continuous_source_iff_seq_originalHminusOne_graph_of_bounded (s r : ℝ)
    (hs : AdmissiblePredualOrder s) (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential s)) (hA : PotentialNormBounded s A)
    (f : A → WeakStarPotential r) (hb : PotentialNormBounded r (range f)) :
    Continuous f ↔ ∀ (x : ℕ → A) (a : A) (b : WeakStarPotential r),
      Tendsto (fun n => potentialHminusOne s hs (x n).val.toPotential) atTop
        (𝓝 (potentialHminusOne s hs a.val.toPotential)) →
      Tendsto (fun n => potentialHminusOne r hr (f (x n)).toPotential) atTop
        (𝓝 (potentialHminusOne r hr b.toPotential)) → f a = b := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne s hs,
    sourceLowerDistribution_eq_potentialHminusOne r hr] using
    continuous_source_iff_seq_lower_graph_of_bounded s r (-1) (-1) (p := 2) (q := 2)
      (by norm_num) (admissible_hminusOne_threshold s hs)
      (by norm_num) (admissible_hminusOne_threshold r hr) A hA f hb

end NLS.Articles.KdVPseudomeasures
