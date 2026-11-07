import NLS.Articles.KdVPseudomeasures.RealPredualTopology

/-!
# Appendix B on the original physical potential space

The wrapper keeps the original distribution and its physical constraints, and
equips it explicitly with the Wiener weak-star topology. Its endpoint norm is
always the norm of the original distribution, not a compatible metric for this
topology. All real predual orders are allowed in Appendix B.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- An original physical potential, with the topology specified below. -/
structure WeakStarPotential (r : ℝ) where
  toPotential : Potential r

/-- The original potential's exact full Wiener weak-dual representation. -/
def weakStarPotentialCoordinates (r : ℝ) (q : WeakStarPotential r) :
    WeakDual ℂ (WeightedCoeff (Weight.sobolev r) 1) :=
  potentialCoordinates r q.toPotential.val

instance (r : ℝ) : TopologicalSpace (WeakStarPotential r) :=
  TopologicalSpace.induced (weakStarPotentialCoordinates r) inferInstance

/-- The source topology is explicitly weak-star, including the physical constraints. -/
theorem isClosedEmbedding_weakStarPotentialCoordinates (r : ℝ) :
    Topology.IsClosedEmbedding (weakStarPotentialCoordinates r) := by
  have hi : Function.Injective (weakStarPotentialCoordinates r) := by
    intro q v h
    have he := congrArg (potentialFromCoordinates r) h
    simp only [weakStarPotentialCoordinates, potentialFromCoordinates_coordinates] at he
    cases q
    cases v
    congr 1
    exact Subtype.ext he
  have hr : range (weakStarPotentialCoordinates r) = potentialCoordinateLocus r := by
    ext f
    constructor
    · rintro ⟨q, rfl⟩
      exact (mem_potentialCoordinateLocus_iff r _).mpr q.toPotential.property
    · intro hf
      exact ⟨⟨(potentialCoordinateEquiv r).symm ⟨f, hf⟩⟩,
        congrArg Subtype.val ((potentialCoordinateEquiv r).apply_symm_apply ⟨f, hf⟩)⟩
  exact ⟨⟨⟨rfl⟩, hi⟩, hr ▸ isClosed_potentialCoordinateLocus r⟩

/-- Boundedness is stated in the original endpoint distribution norm. -/
def PotentialNormBounded (r : ℝ) (A : Set (WeakStarPotential r)) : Prop :=
  ∃ R : ℝ, ∀ q ∈ A, ‖q.toPotential.val‖ ≤ R

/-- Original endpoint norm boundedness equals the norm bornology of the full dual. -/
theorem potentialNormBounded_iff_coordinates (r : ℝ) (A : Set (WeakStarPotential r)) :
    PotentialNormBounded r A ↔ Bornology.IsBounded (weakStarPotentialCoordinates r '' A) := by
  rw [← WeakDual.isBounded_toWeakDual_preimage_iff_isBounded,
    isBounded_iff_forall_norm_le]
  constructor
  · rintro ⟨R, hR⟩
    refine ⟨R, ?_⟩
    intro f hf
    obtain ⟨q, hq, he⟩ := hf
    have hn := norm_potentialCoordinates r q.toPotential.val
    change ‖(weakStarPotentialCoordinates r q).toStrongDual‖ = ‖q.toPotential.val‖ at hn
    rw [he] at hn
    exact hn.trans_le (hR q hq)
  · rintro ⟨R, hR⟩
    refine ⟨R, fun q hq => ?_⟩
    rw [← norm_potentialCoordinates r q.toPotential.val]
    exact hR _ ⟨q, hq, rfl⟩

/-- Appendix B.1(iii)(a)-(c) for the original physical potentials. -/
theorem isCompact_source_iff_bounded_closed (r : ℝ) (A : Set (WeakStarPotential r)) :
    IsCompact A ↔ PotentialNormBounded r A ∧ IsClosed A := by
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.isCompact_iff,
    WeightedCoeff.isCompact_weakStar_iff_bounded_closed r,
    ← potentialNormBounded_iff_coordinates,
    ← (isClosedEmbedding_weakStarPotentialCoordinates r).isClosed_iff_image_isClosed]

/-- Original physical norm balls are compact in their explicit weak-star topology. -/
theorem isCompact_sourceNormBall (r R : ℝ) :
    IsCompact {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R} := by
  apply (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.isCompact_iff.mpr
  have he : weakStarPotentialCoordinates r '' {q | ‖q.toPotential.val‖ ≤ R} =
      WeightedCoeff.weakStarBall r R ∩ potentialCoordinateLocus r := by
    ext f
    constructor
    · rintro ⟨q, hq, rfl⟩
      change ‖q.toPotential.val‖ ≤ R at hq
      refine ⟨?_, (mem_potentialCoordinateLocus_iff r _).mpr q.toPotential.property⟩
      simpa only [WeightedCoeff.weakStarBall, mem_preimage, Metric.mem_closedBall,
        dist_zero_right, weakStarPotentialCoordinates, norm_potentialCoordinates] using hq
    · rintro ⟨hb, hf⟩
      let q : WeakStarPotential r := ⟨(potentialCoordinateEquiv r).symm ⟨f, hf⟩⟩
      have heq : weakStarPotentialCoordinates r q = f :=
        congrArg Subtype.val ((potentialCoordinateEquiv r).apply_symm_apply ⟨f, hf⟩)
      refine ⟨q, ?_, heq⟩
      change ‖q.toPotential.val‖ ≤ R
      rw [← norm_potentialCoordinates r q.toPotential.val]
      change ‖(weakStarPotentialCoordinates r q).toStrongDual‖ ≤ R
      rw [heq]
      simpa only [WeightedCoeff.weakStarBall, mem_preimage, Metric.mem_closedBall,
        dist_zero_right] using hb
  rw [he]
  exact isCompact_potentialCoordinateBall r R

/-- Appendix B.1(iii)(a)-(b), without an assumed bound on the source set. -/
theorem isCompact_source_iff_isSeqCompact (r : ℝ) (A : Set (WeakStarPotential r)) :
    IsCompact A ↔ IsSeqCompact A := by
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.isCompact_iff,
    WeightedCoeff.isCompact_weakStar_iff_isSeqCompact r]
  constructor
  · intro h x hx
    obtain ⟨_, ⟨a, ha, rfl⟩, φ, hφ, ht⟩ := h (fun n => mem_image_of_mem _ (hx n))
    exact ⟨a, ha, φ, hφ,
      (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.tendsto_nhds_iff.mpr ht⟩
  · intro h
    exact h.image (isClosedEmbedding_weakStarPotentialCoordinates r).continuous.seqContinuous

/-- Every bounded source subset is metrizable in its weak-star topology. -/
theorem metrizable_source_of_bounded (r : ℝ) (A : Set (WeakStarPotential r))
    (hb : PotentialNormBounded r A) : TopologicalSpace.MetrizableSpace A := by
  let B := weakStarPotentialCoordinates r '' A
  have hB := (potentialNormBounded_iff_coordinates r A).mp hb
  let j : A → B := fun q => ⟨weakStarPotentialCoordinates r q.val, ⟨q.val, q.property, rfl⟩⟩
  have hj : Topology.IsEmbedding j :=
    ((isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal).codRestrict B _
  exact ((WeightedCoeff.isEmbedding_weakStarCoordinates_on_bounded r B hB).comp hj).metrizableSpace

/-- Appendix B.1(i): metrizability of every original source norm ball. -/
theorem metrizable_sourceNormBall (r R : ℝ) :
    TopologicalSpace.MetrizableSpace {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R} :=
  metrizable_source_of_bounded r _ ⟨R, fun _ hq => hq⟩

/-- Appendix B.1(i): sequential compactness with all physical restrictions. -/
theorem isSeqCompact_sourceNormBall (r R : ℝ) :
    IsSeqCompact {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R} :=
  (isCompact_source_iff_isSeqCompact r _).mp (isCompact_sourceNormBall r R)

/-- Appendix B.1(ii)(a)-(b), using original norms and Fourier coefficients. -/
theorem tendsto_source_seq_iff_bounded_coefficients (r : ℝ)
    (x : ℕ → WeakStarPotential r) (a : WeakStarPotential r) :
    Tendsto x atTop (𝓝 a) ↔ PotentialNormBounded r (range x) ∧ ∀ n : ℤ,
      Tendsto (fun k => (x k).toPotential.val.val (mode (-n))) atTop
        (𝓝 (a.toPotential.val.val (mode (-n)))) := by
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.tendsto_nhds_iff,
    WeightedCoeff.tendsto_weakStar_seq_iff_bounded_coordinates]
  simp only [Function.comp_def, weakStarPotentialCoordinates, potentialCoordinates_apply,
    potentialNormBounded_iff_coordinates, ← range_comp]

/-- Inclusion into an actual lower norm space of original distributions. -/
def sourceLowerDistribution (r t : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal) (q : WeakStarPotential r) :
    FourierLebesgueSpace (2:ℝ) t p :=
  lowerWeakStarDistribution r t hp h (weakStarPotentialCoordinates r q)

/-- The lower inclusion represents exactly the same original distribution. -/
theorem sourceLowerDistribution_val (r t : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal) (q : WeakStarPotential r) :
    (sourceLowerDistribution r t hp h q).val = q.toPotential.val.val := by
  change (lowerWeakStarDistribution r t hp h
    (WeightedCoeff.wienerDualRealization r
      (sobolevCoefficients (-r) ⊤ q.toPotential.val))).val = _
  rw [lowerWeakStarDistribution_realization, endpointLowerInclusion_val]

/-- Reality, mean zero and period one hold in every lower distribution space. -/
theorem sourceLowerDistribution_source_conditions (r t : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal) (q : WeakStarPotential r) :
    (sourceLowerDistribution r t hp h q).val.IsRealMeanZeroPeriodOne := by
  rw [sourceLowerDistribution_val]
  exact q.toPotential.property

/-- Appendix B.1(iv) on every bounded subset of original physical potentials. -/
theorem isEmbedding_sourceLowerDistribution_on_bounded (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    Topology.IsEmbedding (fun q : A => sourceLowerDistribution r t hp h q.val) := by
  let B := weakStarPotentialCoordinates r '' A
  let j : A → B := fun q => ⟨weakStarPotentialCoordinates r q.val, ⟨q.val, q.property, rfl⟩⟩
  have hj : Topology.IsEmbedding j :=
    ((isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal).codRestrict B _
  change Topology.IsEmbedding ((fun f : B => lowerWeakStarDistribution (L := 2) r t hp h f.val) ∘ j)
  exact (isEmbedding_lowerWeakStarDistribution_on_bounded (L := 2) r t hp h B
    ((potentialNormBounded_iff_coordinates r A).mp hb)).comp hj

/-- Exact lower norm convergence criterion on bounded source sets, for any filter. -/
theorem tendsto_source_iff_lowerDistribution (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {X : Type*} {l : Filter X} (x : X → A) (a : A) :
    Tendsto x l (𝓝 a) ↔
      Tendsto (fun k => sourceLowerDistribution r t hp h (x k).val) l
        (𝓝 (sourceLowerDistribution r t hp h a.val)) :=
  (isEmbedding_sourceLowerDistribution_on_bounded r t hp h A hb).tendsto_nhds_iff

/-- Appendix B.1(ii)(a)-(c) for each admissible original lower norm space. -/
theorem tendsto_source_seq_iff_bounded_lower (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (x : ℕ → WeakStarPotential r) (a : WeakStarPotential r) :
    Tendsto x atTop (𝓝 a) ↔ PotentialNormBounded r (range x) ∧
      Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) atTop
        (𝓝 (sourceLowerDistribution r t hp h a)) := by
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.tendsto_nhds_iff,
    WeightedCoeff.tendsto_weakStar_seq_iff_bounded_lower r t hp h]
  rw [potentialNormBounded_iff_coordinates, ← range_comp]
  apply and_congr Iff.rfl
  change Tendsto (fun k => WeightedCoeff.lowerWeakStarRealization r t hp h
    (weakStarPotentialCoordinates r (x k))) atTop
    (𝓝 (WeightedCoeff.lowerWeakStarRealization r t hp h (weakStarPotentialCoordinates r a))) ↔
      Tendsto ((sobolevCoefficients (L := 2) t p).symm ∘
        (fun k => WeightedCoeff.lowerWeakStarRealization r t hp h
          (weakStarPotentialCoordinates r (x k)))) atTop
        (𝓝 ((sobolevCoefficients (L := 2) t p).symm
          (WeightedCoeff.lowerWeakStarRealization r t hp h (weakStarPotentialCoordinates r a))))
  exact (sobolevCoefficients (L := 2) t p).symm.toHomeomorph.isEmbedding.tendsto_nhds_iff

/-- Appendix B.1(iii)(a)-(d), retaining the original endpoint bound. -/
theorem isCompact_source_iff_bounded_lower_compact (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) :
    IsCompact A ↔ PotentialNormBounded r A ∧
      IsCompact (sourceLowerDistribution r t hp h '' A) := by
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.isCompact_iff,
    isCompact_weakStar_iff_bounded_lowerDistribution_compact (L := 2) r t hp h,
    ← potentialNormBounded_iff_coordinates]
  simp only [← image_comp]
  rfl

/-- The literal existential lower-exponent criterion in Appendix B.1(ii)(c). -/
theorem tendsto_source_seq_iff_bounded_some_lower (r : ℝ)
    (x : ℕ → WeakStarPotential r) (a : WeakStarPotential r) :
    Tendsto x atTop (𝓝 a) ↔ PotentialNormBounded r (range x) ∧
      ∃ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal), t < -r ∧
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) atTop
          (𝓝 (sourceLowerDistribution r t hp h a)) := by
  constructor
  · intro hx
    have h : 1 < (-r-(-r-2))*(1:ℝ≥0∞).toReal := by norm_num
    have ht := (tendsto_source_seq_iff_bounded_lower r (-r-2)
      (p := 1) (by simp) h x a).mp hx
    exact ⟨ht.1, -r-2, 1, le_rfl, by simp, h, by linarith, ht.2⟩
  · rintro ⟨hb, t, p, hp1, hp, h, _, ht⟩
    let : Fact (1 ≤ p) := ⟨hp1⟩
    exact (tendsto_source_seq_iff_bounded_lower r t hp h x a).mpr ⟨hb, ht⟩

/-- The literal existential compactness criterion in Appendix B.1(iii)(d). -/
theorem isCompact_source_iff_bounded_some_lower_compact (r : ℝ)
    (A : Set (WeakStarPotential r)) :
    IsCompact A ↔ PotentialNormBounded r A ∧
      ∃ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal), t < -r ∧
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        IsCompact (sourceLowerDistribution r t hp h '' A) := by
  constructor
  · intro hA
    have h : 1 < (-r-(-r-2))*(1:ℝ≥0∞).toReal := by norm_num
    have ht := (isCompact_source_iff_bounded_lower_compact r (-r-2)
      (p := 1) (by simp) h A).mp hA
    exact ⟨ht.1, -r-2, 1, le_rfl, by simp, h, by linarith, ht.2⟩
  · rintro ⟨hb, t, p, hp1, hp, h, _, ht⟩
    let : Fact (1 ≤ p) := ⟨hp1⟩
    exact (isCompact_source_iff_bounded_lower_compact r t hp h A).mpr ⟨hb, ht⟩

/-- Bounded source sets have compact weak-star closure within the physical space. -/
theorem isCompact_closure_source_of_bounded (r : ℝ) (A : Set (WeakStarPotential r))
    (hb : PotentialNormBounded r A) : IsCompact (closure A) := by
  apply (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.isCompact_iff.mpr
  rw [← (isClosedEmbedding_weakStarPotentialCoordinates r).closure_image_eq]
  exact WeightedCoeff.isCompact_closure_weakStar_of_bounded r _
    ((potentialNormBounded_iff_coordinates r A).mp hb)

/-- A bounded sequence has a physical weak-star limit along a strictly increasing subsequence. -/
theorem exists_source_subseq_of_bounded (r : ℝ) (x : ℕ → WeakStarPotential r)
    (hb : PotentialNormBounded r (range x)) :
    ∃ a ∈ closure (range x), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  ((isCompact_source_iff_isSeqCompact r _).mp
    (isCompact_closure_source_of_bounded r (range x) hb))
      (fun n => subset_closure (mem_range_self n))

/-- Taking weak-star closure commutes with passage to the original lower norm space. -/
theorem closure_sourceLowerDistribution_image (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    closure (sourceLowerDistribution r t hp h '' A) =
      sourceLowerDistribution r t hp h '' closure A := by
  have hc := closure_lowerWeakStarDistribution_image (L := 2) r t hp h
    (weakStarPotentialCoordinates r '' A) ((potentialNormBounded_iff_coordinates r A).mp hb)
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).closure_image_eq] at hc
  simp only [← image_comp] at hc
  exact hc

/-- The real Wiener predual induces exactly the source topology on bounded sets. -/
theorem isEmbedding_sourceRealWienerTests_on_bounded (r : ℝ)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    Topology.IsEmbedding (fun q : A =>
      originalRealWienerEvaluations r (weakStarPotentialCoordinates r q.val)) := by
  let B := weakStarPotentialCoordinates r '' A
  let j : A → B := fun q => ⟨weakStarPotentialCoordinates r q.val, ⟨q.val, q.property, rfl⟩⟩
  have hj : Topology.IsEmbedding j :=
    ((isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal).codRestrict B _
  have hB : B ⊆ potentialCoordinateLocus r := by
    rintro _ ⟨q, _, rfl⟩
    exact (mem_potentialCoordinateLocus_iff r _).mpr q.toPotential.property
  change Topology.IsEmbedding ((fun f : B => originalRealWienerEvaluations r f.val) ∘ j)
  exact (isEmbedding_originalRealWienerEvaluations_on_bounded r B
    ((potentialNormBounded_iff_coordinates r A).mp hb) hB).comp hj

/-- Arbitrary-filter criterion against every original real Wiener test on bounded source sets. -/
theorem tendsto_source_iff_realWienerTests (r : ℝ)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {X : Type*} {l : Filter X} (x : X → A) (a : A) :
    Tendsto x l (𝓝 a) ↔ ∀ u : OriginalRealWienerTest r,
      Tendsto (fun k => originalRealWienerEvaluations r
        (weakStarPotentialCoordinates r (x k).val) u) l
        (𝓝 (originalRealWienerEvaluations r (weakStarPotentialCoordinates r a.val) u)) := by
  rw [(isEmbedding_sourceRealWienerTests_on_bounded r A hb).tendsto_nhds_iff]
  exact tendsto_pi_nhds

/-- The same-distribution inclusion is injective on the original physical space. -/
theorem sourceLowerDistribution_injective (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal) :
    Function.Injective (sourceLowerDistribution r t hp h) := by
  intro q v he
  have hd := congrArg (fun u : FourierLebesgueSpace (2:ℝ) t p => u.val) he
  rw [sourceLowerDistribution_val, sourceLowerDistribution_val] at hd
  cases q
  cases v
  congr 1
  exact Subtype.ext (Subtype.ext hd)

/-- For bounded physical source sets, ambient closedness can be checked in a lower norm space. -/
theorem isClosed_source_iff_lower_image (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    IsClosed A ↔ IsClosed (sourceLowerDistribution r t hp h '' A) := by
  constructor
  · intro hA
    exact ((isCompact_source_iff_bounded_lower_compact r t hp h A).mp
      ((isCompact_source_iff_bounded_closed r A).mpr ⟨hb, hA⟩)).2.isClosed
  · intro hA
    rw [← closure_eq_iff_isClosed]
    apply (sourceLowerDistribution_injective r t hp h).image_injective
    rw [← closure_sourceLowerDistribution_image r t hp h A hb, hA.closure_eq]

/-- Lower norm realization as a continuous map on a bounded physical source set. -/
def sourceLowerDistributionMapOn (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A) :
    C(A, FourierLebesgueSpace (2:ℝ) t p) :=
  ⟨fun q => sourceLowerDistribution r t hp h q.val,
    (isEmbedding_sourceLowerDistribution_on_bounded r t hp h A hb).continuous⟩

/-- The lower norm realization induces the full compact-open source trajectory topology. -/
theorem isEmbedding_sourceLowerDistributionTrajectory (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K : Type*} [TopologicalSpace K] :
    Topology.IsEmbedding ((sourceLowerDistributionMapOn r t hp h A hb).comp :
      C(K,A) → C(K, FourierLebesgueSpace (2:ℝ) t p)) :=
  ContinuousMap.isEmbedding_postcomp _
    (isEmbedding_sourceLowerDistribution_on_bounded r t hp h A hb)

/-- Continuous dependence in physical weak-star trajectories equals lower norm trajectory continuity. -/
theorem continuous_sourceTrajectory_iff_lowerDistribution (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K X : Type*} [TopologicalSpace K] [TopologicalSpace X] (S : X → C(K,A)) :
    Continuous S ↔ Continuous (fun x =>
      (sourceLowerDistributionMapOn r t hp h A hb).comp (S x)) :=
  (isEmbedding_sourceLowerDistributionTrajectory r t hp h A hb).continuous_iff

/-- In the article range the lower realization is the exact original H-minus-one potential. -/
theorem sourceLowerDistribution_eq_potentialHminusOne (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : WeakStarPotential r) :
    sourceLowerDistribution r (-1) (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) q = potentialHminusOne r hr q.toPotential := by
  apply Subtype.ext
  rw [sourceLowerDistribution_val, potentialHminusOne_val]

end NLS.Articles.KdVPseudomeasures
