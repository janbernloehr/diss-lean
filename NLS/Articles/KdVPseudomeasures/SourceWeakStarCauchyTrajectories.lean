import NLS.FunctionalAnalysis.CompactwiseCauchyLimit
import NLS.Articles.KdVPseudomeasures.SourceWeakStarCauchy
import NLS.Articles.KdVPseudomeasures.SourceWeakStarTrajectories

/-!
# Continuous physical limits of compactwise Cauchy Fourier tests

The endpoint radius is fixed before time and the approximating index.
On a locally compact time domain, compactwise uniform Cauchy control of
each Fourier mode yields a continuous physical weak-star trajectory.
One limit works in every admissible lower finite-p norm on every compact
time set. The exact original endpoint bound and physical constraints remain.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

/-- Compactwise Cauchy Fourier tests and an eventual common endpoint bound
recover a unique continuous physical limit. Only eventual continuity of
each Fourier mode is needed; the index filter need not be sequential. -/
theorem existsUnique_sourceTrajectory_of_compactwiseCauchy_coefficients
    (r R : ℝ) {A T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {l : Filter A} [NeBot l] (F : A → T → WeakStarPotential r)
    (hb : ∀ᶠ a in l, ∀ s, ‖(F a s).toPotential.val‖ ≤ R)
    (hF : ∀ n : ℤ, ∀ᶠ a in l,
      Continuous (fun s => (F a s).toPotential.val.val (mode (-n))))
    (hc : ∀ S : Set T, IsCompact S → ∀ n : ℤ, UniformCauchySeqOn
      (fun a s => (F a s).toPotential.val.val (mode (-n))) l S) :
    ∃! g : C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}),
      (∀ s, Tendsto (fun a => F a s) l (𝓝 (g s).val)) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        ∀ S : Set T, IsCompact S → TendstoUniformlyOn
          (fun a s => sourceLowerDistribution r t hp h (F a s))
          (fun s => sourceLowerDistribution r t hp h (g s).val) l S := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  choose G hG using fun n => NLS.exists_continuous_limit_of_compactwise_uniformCauchy
    (fun a s => (F a s).toPotential.val.val (mode (-n))) (hF n)
      (fun S hS => hc S hS n)
  have hp (s : T) := existsUnique_source_of_tendsto_coefficients_normBound r R
    (fun a => F a s) (fun n => G n s) (hb.mono fun a ha => ha s)
      (fun n => (hG n {s} isCompact_singleton).tendsto_at (mem_singleton s))
  choose g hg using fun s => (hp s).exists
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  let g' : T → K := fun s => ⟨g s, (hg s).2.1⟩
  have he (n : ℤ) : (fun s => (g s).toPotential.val.val (mode (-n))) = G n :=
    funext fun s => (hg s).1 n
  have hgc : Continuous g' :=
    (continuous_source_iff_coefficients r K ⟨R, fun _ hq => hq⟩ g').mpr (by
      intro n
      change Continuous (fun s => (g s).toPotential.val.val (mode (-n)))
      rw [he n]
      exact (G n).continuous)
  refine ⟨⟨g', hgc⟩, ⟨fun s => (hg s).2.2, ?_⟩, ?_⟩
  · intro t p hp1 hp h S hS
    let : Fact (1 ≤ p) := ⟨hp1⟩
    apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    apply (tendstoUniformly_sourceLowerDistribution_iff_coefficients_of_eventually_normBound
      r t R hp h (fun a (s : S) => F a s) (fun s : S => g s) l
        (hb.mono fun a ha s => ha s) (fun s => (hg s).2.1)).mpr
    intro n
    have ht := hG n S hS
    rw [← he n] at ht
    exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mp ht
  · intro g₁ hg₁
    apply ContinuousMap.ext
    intro s
    apply Subtype.ext
    exact tendsto_nhds_unique (hg₁.1 s) (hg s).2.2

/-- For continuous trajectories in a fixed original endpoint norm ball,
compactwise Cauchy Fourier tests give convergence in the compact-open
weak-star topology, simultaneously with every admissible lower norm. -/
theorem existsUnique_sourceTrajectory_tendsto_of_compactwiseCauchy_coefficients
    (r R : ℝ) {A T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {l : Filter A} [NeBot l]
    (F : A → C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}))
    (hc : ∀ S : Set T, IsCompact S → ∀ n : ℤ, UniformCauchySeqOn
      (fun a s => (F a s).val.toPotential.val.val (mode (-n))) l S) :
    ∃! g : C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}),
      Tendsto F l (𝓝 g) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        ∀ S : Set T, IsCompact S → TendstoUniformlyOn
          (fun a s => sourceLowerDistribution r t hp h (F a s).val)
          (fun s => sourceLowerDistribution r t hp h (g s).val) l S := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  obtain ⟨g, hg, _⟩ := existsUnique_sourceTrajectory_of_compactwiseCauchy_coefficients
    r R (fun a s => (F a s).val)
      (Eventually.of_forall fun a s => (F a s).property)
      (fun n => Eventually.of_forall fun a =>
        (continuous_sourceCoefficient r n).comp
          (continuous_subtype_val.comp (F a).continuous)) hc
  have h₀ : 1 < (-r-(-r-2))*(1 : ℝ≥0∞).toReal := by norm_num
  have ht : Tendsto F l (𝓝 g) :=
    (tendsto_sourceTrajectory_iff_uniformOn_compacts r (-r-2) (p := 1)
      (by simp) h₀ _ ⟨R, fun _ hq => hq⟩ F g).mpr
      (hg.2 (-r-2) 1 (by simp) (by simp) h₀)
  exact ⟨g, ⟨ht, hg.2⟩, fun _ hg₁ => tendsto_nhds_unique hg₁.1 ht⟩

/-- On any testing set, uniform Cauchy lower norm control is equivalent
to uniform Cauchy control of every Fourier mode under one eventual bound.
Neither a topology nor compactness is required of the testing set. -/
theorem uniformCauchyOn_sourceLowerDistribution_iff_coefficients (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A T : Type*} {l : Filter A} [NeBot l] (F : A → T → WeakStarPotential r)
    (S : Set T) (hb : ∀ᶠ a in l, ∀ s ∈ S, ‖(F a s).toPotential.val‖ ≤ R) :
    UniformCauchySeqOn (fun a s => sourceLowerDistribution r t hp h (F a s)) l S ↔
      ∀ n : ℤ, UniformCauchySeqOn
        (fun a s => (F a s).toPotential.val.val (mode (-n))) l S := by
  rw [NLS.uniformCauchyOn_iff_subtype,
    uniformCauchy_sourceLowerDistribution_iff_coefficients r t R hp h
      (fun a (s : S) => F a s) (hb.mono fun a ha s => ha s s.property)]
  exact forall_congr' fun n => (NLS.uniformCauchyOn_iff_subtype
    (fun a s => (F a s).toPotential.val.val (mode (-n))) l S).symm

/-- A family of continuous physical trajectories in an endpoint ball
has a compact-open weak-star limit exactly when it is uniformly Cauchy
on every compact time set in one chosen admissible lower norm. -/
theorem exists_sourceTrajectory_tendsto_iff_compactwiseCauchy_lower
    (r t R : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {l : Filter A} [NeBot l]
    (F : A → C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R})) :
    (∃ g : C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}),
      Tendsto F l (𝓝 g)) ↔
      ∀ S : Set T, IsCompact S → UniformCauchySeqOn
        (fun a s => sourceLowerDistribution r t hp h (F a s).val) l S := by
  constructor
  · rintro ⟨g, hg⟩ S hS
    exact ((tendsto_sourceTrajectory_iff_uniformOn_compacts r t hp h _
      ⟨R, fun _ hq => hq⟩ F g).mp hg S hS).uniformCauchySeqOn
  · intro hc
    obtain ⟨g, hg, _⟩ :=
      existsUnique_sourceTrajectory_tendsto_of_compactwiseCauchy_coefficients r R F
        (fun S hS => (uniformCauchyOn_sourceLowerDistribution_iff_coefficients
          r t R hp h (fun a s => (F a s).val) S
            (Eventually.of_forall fun a s _ => (F a s).property)).mp (hc S hS))
    exact ⟨g, hg.1⟩

/-- In the article range, compactwise uniform Cauchy control in the norm
of the identical original H-minus-one distributions detects existence of
a continuous weak-star trajectory limit in the same endpoint ball. -/
theorem exists_sourceTrajectory_tendsto_iff_compactwiseCauchy_originalHminusOne
    (r R : ℝ) (hr : AdmissiblePredualOrder r)
    {A T : Type*} [TopologicalSpace T] [LocallyCompactSpace T]
    {l : Filter A} [NeBot l]
    (F : A → C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R})) :
    (∃ g : C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}),
      Tendsto F l (𝓝 g)) ↔
      ∀ S : Set T, IsCompact S → UniformCauchySeqOn
        (fun a s => potentialHminusOne r hr (F a s).val.toPotential) l S := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using
    exists_sourceTrajectory_tendsto_iff_compactwiseCauchy_lower r (-1) R
      (p := 2) (by norm_num) (admissible_hminusOne_threshold r hr) F

end NLS.Articles.KdVPseudomeasures
