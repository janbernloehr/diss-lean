import NLS.Articles.KdVPseudomeasures.SourceWeakStarTopology
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Bounded weak-star limits in the original physical source space

These consequences of Appendix B keep the endpoint norm of the original
distribution. Sequential descriptions are restricted to norm-bounded sets;
no sequentiality of the entire weak-star space is assumed.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- Endpoint norm sublevel sets are closed for the physical weak-star topology. -/
theorem isClosed_sourceNormBall (r R : ℝ) :
    IsClosed {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R} :=
  ((isCompact_source_iff_bounded_closed r _).mp (isCompact_sourceNormBall r R)).2

/-- The exact original endpoint norm is weak-star lower semicontinuous. -/
theorem lowerSemicontinuous_sourceNorm (r : ℝ) :
    LowerSemicontinuous (fun q : WeakStarPotential r => ‖q.toPotential.val‖) :=
  lowerSemicontinuous_iff_isClosed_preimage.mpr (isClosed_sourceNormBall r)

/-- Every weak-star limit of an eventually norm-bounded net has the same bound. -/
theorem sourceNorm_le_of_tendsto (r R : ℝ)
    {X : Type*} {l : Filter X} [NeBot l]
    (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hx : Tendsto x l (𝓝 a)) (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) :
    ‖a.toPotential.val‖ ≤ R :=
  (isClosed_sourceNormBall r R).mem_of_tendsto hx hb

/-- Taking weak-star closure preserves any specified original endpoint norm bound. -/
theorem sourceNorm_le_of_mem_closure (r R : ℝ) (A : Set (WeakStarPotential r))
    (hb : ∀ q ∈ A, ‖q.toPotential.val‖ ≤ R)
    {a : WeakStarPotential r} (ha : a ∈ closure A) : ‖a.toPotential.val‖ ≤ R :=
  closure_minimal hb (isClosed_sourceNormBall r R) ha

/-- A source subset is norm bounded exactly when its weak-star closure is. -/
theorem potentialNormBounded_closure_iff (r : ℝ) (A : Set (WeakStarPotential r)) :
    PotentialNormBounded r (closure A) ↔ PotentialNormBounded r A := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, fun q hq => hR q (subset_closure hq)⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, fun _ hq => sourceNorm_le_of_mem_closure r R A hR hq⟩

/-- A lower norm limit of eventually endpoint-bounded data retains the full
endpoint regularity, the same bound and all original physical conditions. -/
theorem exists_source_of_tendsto_lower_normBound (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (g : FourierLebesgueSpace (2:ℝ) t p)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hg : Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) l (𝓝 g)) :
    ∃ a : WeakStarPotential r, ‖a.toPotential.val‖ ≤ R ∧
      sourceLowerDistribution r t hp h a = g := by
  have hc := ((isCompact_source_iff_bounded_lower_compact r t hp h _).mp
    (isCompact_sourceNormBall r R)).2.isClosed
  have hgmem := hc.mem_of_tendsto hg (hb.mono fun k hk => mem_image_of_mem _ hk)
  exact hgmem

/-- On a bounded physical set, continuity is exactly continuity of all Fourier coefficients. -/
theorem continuous_source_iff_coefficients (r : ℝ)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {X : Type*} [TopologicalSpace X] (f : X → A) :
    Continuous f ↔ ∀ n : ℤ,
      Continuous (fun x => (f x).val.toPotential.val.val (mode (-n))) := by
  let B := weakStarPotentialCoordinates r '' A
  let j : A → B := fun q => ⟨weakStarPotentialCoordinates r q.val, ⟨q.val, q.property, rfl⟩⟩
  have hj : Topology.IsEmbedding j :=
    ((isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal).codRestrict B _
  have he := (WeightedCoeff.isEmbedding_weakStarCoordinates_on_bounded r B
    ((potentialNormBounded_iff_coordinates r A).mp hb)).comp hj
  refine he.continuous_iff.trans ?_
  simp only [continuous_pi_iff, Function.comp_def, j, weakStarPotentialCoordinates,
    potentialCoordinates_apply]

/-- Continuity into a bounded physical set can be tested in any admissible lower norm. -/
theorem continuous_source_iff_lowerDistribution (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {X : Type*} [TopologicalSpace X] (f : X → A) :
    Continuous f ↔ Continuous (fun x => sourceLowerDistribution r t hp h (f x).val) :=
  (isEmbedding_sourceLowerDistribution_on_bounded r t hp h A hb).continuous_iff

/-- Maps out of a bounded physical weak-star set are continuous iff sequentially continuous. -/
theorem continuous_from_source_iff_seqContinuous (r : ℝ)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {Y : Type*} [TopologicalSpace Y] (f : A → Y) :
    Continuous f ↔ SeqContinuous f := by
  let := metrizable_source_of_bounded r A hb
  exact continuous_iff_seqContinuous

/-- Every point in the closure of a bounded source set is a limit of a sequence in that set. -/
theorem mem_closure_source_iff_seq_limit (r : ℝ)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    (a : WeakStarPotential r) :
    a ∈ closure A ↔ ∃ x : ℕ → WeakStarPotential r,
      (∀ n, x n ∈ A) ∧ Tendsto x atTop (𝓝 a) := by
  have h : 1 < (-r-(-r-2))*(1:ℝ≥0∞).toReal := by norm_num
  let F := sourceLowerDistribution r (-r-2) (p := 1) (by simp) h
  constructor
  · intro ha
    have hl : F a ∈ closure (F '' A) := by
      rw [closure_sourceLowerDistribution_image r (-r-2) (by simp) h A hb]
      exact mem_image_of_mem _ ha
    obtain ⟨y, hy, ht⟩ := mem_closure_iff_seq_limit.mp hl
    choose x hx hxy using hy
    refine ⟨x, hx, ?_⟩
    apply (tendsto_source_seq_iff_bounded_lower r (-r-2) (p := 1) (by simp) h x a).mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨R, hR⟩ := hb
      exact ⟨R, fun q hq => by obtain ⟨n, rfl⟩ := hq; exact hR _ (hx n)⟩
    · change Tendsto (fun k => F (x k)) atTop (𝓝 (F a))
      have he : (fun k => F (x k)) = y := funext hxy
      rw [he]
      exact ht
  · rintro ⟨x, hx, ht⟩
    exact mem_closure_of_tendsto ht (Eventually.of_forall hx)

/-- Ambient weak-star closedness of a bounded source set can be checked with sequences. -/
theorem isClosed_source_iff_seq_limits (r : ℝ)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    IsClosed A ↔ ∀ (x : ℕ → WeakStarPotential r) (a : WeakStarPotential r),
      (∀ n, x n ∈ A) → Tendsto x atTop (𝓝 a) → a ∈ A := by
  constructor
  · intro hA x a hx ht
    exact hA.mem_of_tendsto ht (Eventually.of_forall hx)
  · intro hA
    rw [← closure_eq_iff_isClosed]
    apply subset_antisymm _ subset_closure
    intro a ha
    obtain ⟨x, hx, ht⟩ := (mem_closure_source_iff_seq_limit r A hb a).mp ha
    exact hA x a hx ht

/-- One extracted physical subsequence converges in every admissible lower norm space. -/
theorem exists_source_subseq_all_lower_of_bounded (r : ℝ)
    (x : ℕ → WeakStarPotential r) (hb : PotentialNormBounded r (range x)) :
    ∃ a ∈ closure (range x), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 a) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        Tendsto (fun k => sourceLowerDistribution r t hp h (x (φ k))) atTop
          (𝓝 (sourceLowerDistribution r t hp h a)) := by
  obtain ⟨a, ha, φ, hφ, ht⟩ := exists_source_subseq_of_bounded r x hb
  refine ⟨a, ha, φ, hφ, ht, ?_⟩
  intro t p hp1 hp h
  let : Fact (1 ≤ p) := ⟨hp1⟩
  exact ((tendsto_source_seq_iff_bounded_lower r t hp h (x ∘ φ) a).mp ht).2

end NLS.Articles.KdVPseudomeasures
