import NLS.Articles.KdVPseudomeasures.SourceWeakStarLimits

/-!
# Eventually bounded nets of original physical potentials

Appendix B's bounded-set topology comparison also applies when a net enters
an endpoint norm ball only eventually. Lower norm limits then determine a
unique physical weak-star limit, with the same specified endpoint bound.
No boundedness conclusion for general weak-star convergent nets is used.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open NLS.Fourier.PeriodicFourierLebesgue

/-- The coefficient criterion for a norm-bounded ambient family, with any filter. -/
theorem tendsto_source_iff_coefficients_of_bounded (r : ℝ)
    {X : Type*} {l : Filter X} (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : PotentialNormBounded r (range x)) :
    Tendsto x l (𝓝 a) ↔ ∀ n : ℤ,
      Tendsto (fun k => (x k).toPotential.val.val (mode (-n))) l
        (𝓝 (a.toPotential.val.val (mode (-n)))) := by
  rw [(isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.tendsto_nhds_iff,
    WeightedCoeff.tendsto_weakStar_iff_coordinates_of_bounded r _ _
      (by simpa only [range_comp] using (potentialNormBounded_iff_coordinates r _).mp hb)]
  simp only [Function.comp_def, weakStarPotentialCoordinates, potentialCoordinates_apply]

/-- Only eventual membership in the norm ball is needed for the coefficient criterion. -/
theorem tendsto_source_iff_coefficients_of_eventually_normBound (r R : ℝ)
    {X : Type*} {l : Filter X} (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) :
    Tendsto x l (𝓝 a) ↔ ∀ n : ℤ,
      Tendsto (fun k => (x k).toPotential.val.val (mode (-n))) l
        (𝓝 (a.toPotential.val.val (mode (-n)))) := by
  let y : X → WeakStarPotential r := fun k =>
    if ‖(x k).toPotential.val‖ ≤ R then x k else a
  have he : x =ᶠ[l] y := hb.mono fun k hk => by simp only [y, if_pos hk]
  have hy : PotentialNormBounded r (range y) := by
    refine ⟨max R ‖a.toPotential.val‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    dsimp [y]
    split_ifs with hk
    · exact hk.trans (le_max_left _ _)
    · exact le_max_right _ _
  rw [tendsto_congr' he, tendsto_source_iff_coefficients_of_bounded r y a hy]
  exact forall_congr' fun n => (tendsto_congr' (he.mono fun k hk => congrArg
    (fun q : WeakStarPotential r => q.toPotential.val.val (mode (-n))) hk)).symm

/-- Pointwise Fourier limits of eventually bounded nets automatically represent
one original real mean-zero period-one endpoint potential. -/
theorem existsUnique_source_of_tendsto_coefficients_normBound (r R : ℝ)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (g : ℤ → ℂ) (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hg : ∀ n : ℤ, Tendsto (fun k => (x k).toPotential.val.val (mode (-n))) l (𝓝 (g n))) :
    ∃! a : WeakStarPotential r,
      (∀ n : ℤ, a.toPotential.val.val (mode (-n)) = g n) ∧
      ‖a.toPotential.val‖ ≤ R ∧ Tendsto x l (𝓝 a) := by
  let c := fun q : WeakStarPotential r =>
    WeightedCoeff.weakStarCoordinates r (weakStarPotentialCoordinates r q)
  have hc : Continuous c := (WeightedCoeff.continuous_weakStarCoordinates r).comp
    (isClosedEmbedding_weakStarPotentialCoordinates r).continuous
  have hi : Function.Injective c := (WeightedCoeff.weakStarCoordinates_injective r).comp
    (isClosedEmbedding_weakStarPotentialCoordinates r).injective
  have he (q : WeakStarPotential r) (n : ℤ) :
      c q n = q.toPotential.val.val (mode (-n)) := by
    simp only [c, weakStarPotentialCoordinates, potentialCoordinates_apply]
  have hg' : Tendsto (c ∘ x) l (𝓝 g) := by
    apply tendsto_pi_nhds.mpr
    intro n
    simpa only [Function.comp_def, he] using hg n
  have hm : g ∈ c '' {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R} :=
    ((isCompact_sourceNormBall r R).image hc).isClosed.mem_of_tendsto hg'
      (hb.mono fun k hk => mem_image_of_mem c hk)
  obtain ⟨a, ha, hag⟩ := hm
  have hag' (n : ℤ) : a.toPotential.val.val (mode (-n)) = g n :=
    (he a n).symm.trans (congrFun hag n)
  refine ⟨a, ⟨hag', ha, ?_⟩, ?_⟩
  · apply (tendsto_source_iff_coefficients_of_eventually_normBound r R x a hb).mpr
    intro n
    rw [hag' n]
    exact hg n
  · intro b hba
    apply hi
    funext n
    exact (he b n).trans ((hba.1 n).trans (congrFun hag n).symm)

/-- Any admissible original lower norm detects convergence of a bounded ambient family. -/
theorem tendsto_source_iff_lowerDistribution_of_bounded (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {X : Type*} {l : Filter X} (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : PotentialNormBounded r (range x)) :
    Tendsto x l (𝓝 a) ↔
      Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) l
        (𝓝 (sourceLowerDistribution r t hp h a)) := by
  let A := insert a (range x)
  have hA : PotentialNormBounded r A := by
    obtain ⟨R, hR⟩ := hb
    refine ⟨max R ‖a.toPotential.val‖, ?_⟩
    intro q hq
    rcases hq with rfl | hq
    · exact le_max_right _ _
    · exact (hR q hq).trans (le_max_left _ _)
  let y : X → A := fun k => ⟨x k, mem_insert_of_mem _ (mem_range_self k)⟩
  let b : A := ⟨a, mem_insert _ _⟩
  have hy : Tendsto y l (𝓝 b) ↔ Tendsto x l (𝓝 a) :=
    Topology.IsEmbedding.subtypeVal.tendsto_nhds_iff
  exact hy.symm.trans (tendsto_source_iff_lowerDistribution r t hp h A hA y b)

/-- Lower norm and weak-star convergence agree for every eventually bounded net. -/
theorem tendsto_source_iff_lowerDistribution_of_eventually_normBound (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {X : Type*} {l : Filter X} (x : X → WeakStarPotential r) (a : WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) :
    Tendsto x l (𝓝 a) ↔
      Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) l
        (𝓝 (sourceLowerDistribution r t hp h a)) := by
  let y : X → WeakStarPotential r := fun k =>
    if ‖(x k).toPotential.val‖ ≤ R then x k else a
  have he : x =ᶠ[l] y := hb.mono fun k hk => by simp only [y, if_pos hk]
  have hy : PotentialNormBounded r (range y) := by
    refine ⟨max R ‖a.toPotential.val‖, ?_⟩
    rintro _ ⟨k, rfl⟩
    dsimp [y]
    split_ifs with hk
    · exact hk.trans (le_max_left _ _)
    · exact le_max_right _ _
  rw [tendsto_congr' he, tendsto_source_iff_lowerDistribution_of_bounded r t hp h y a hy]
  exact (tendsto_congr' (he.mono fun k hk =>
    congrArg (sourceLowerDistribution r t hp h) hk)).symm

/-- A lower norm limit of an eventually bounded net is uniquely the same
physical distribution, and the net converges weak-star to it with the same bound. -/
theorem existsUnique_source_of_tendsto_lower_normBound (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (g : FourierLebesgueSpace (2:ℝ) t p)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hg : Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) l (𝓝 g)) :
    ∃! a : WeakStarPotential r, sourceLowerDistribution r t hp h a = g ∧
      ‖a.toPotential.val‖ ≤ R ∧ Tendsto x l (𝓝 a) := by
  obtain ⟨a, ha, he⟩ := exists_source_of_tendsto_lower_normBound r t R hp h x g hb hg
  refine ⟨a, ⟨he, ha, ?_⟩, ?_⟩
  · apply (tendsto_source_iff_lowerDistribution_of_eventually_normBound r t R hp h x a hb).mpr
    rwa [he]
  · intro b hba
    exact sourceLowerDistribution_injective r t hp h (hba.1.trans he.symm)

/-- In the article range, eventual endpoint bounds and an original H-minus-one
limit give a unique original physical weak-star limit with that same bound. -/
theorem existsUnique_source_of_tendsto_originalHminusOne_normBound (r R : ℝ)
    (hr : AdmissiblePredualOrder r)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (g : FourierLebesgueSpace (2:ℝ) (-1) 2)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hg : Tendsto (fun k => potentialHminusOne r hr (x k).toPotential) l (𝓝 g)) :
    ∃! a : WeakStarPotential r, potentialHminusOne r hr a.toPotential = g ∧
      ‖a.toPotential.val‖ ≤ R ∧ Tendsto x l (𝓝 a) := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using
    existsUnique_source_of_tendsto_lower_normBound r (-1) R (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) x g hb (by
        simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using hg)

end NLS.Articles.KdVPseudomeasures
