import NLS.FunctionalAnalysis.CompactCoordinateEquicontinuity
import NLS.Articles.KdVPseudomeasures.SourceWeakStarUniformControl
import NLS.Articles.KdVPseudomeasures.SourceWeakStarTrajectories

/-!
# Fourier equicontinuity and compactness of physical trajectories

A common original endpoint norm bound makes equicontinuity of each Fourier
coefficient sufficient for equicontinuity in every admissible lower norm.
On compact time domains one subsequence converges uniformly in all those
norms to the same continuous physical weak-star trajectory.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

/-- Under a common original endpoint bound, equicontinuity in any admissible
lower norm is equivalent to equicontinuity of each original Fourier mode. -/
theorem equicontinuous_sourceLowerDistribution_iff_coefficients (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A T : Type*} [TopologicalSpace T] (F : A → T → WeakStarPotential r)
    (hF : ∀ a s, ‖(F a s).toPotential.val‖ ≤ R) :
    Equicontinuous (fun a s => sourceLowerDistribution r t hp h (F a s)) ↔
      ∀ n : ℤ, Equicontinuous
        (fun a s => (F a s).toPotential.val.val (mode (-n))) := by
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sourceNormBall r R)
  let c : K → ℤ → ℂ := fun q n => q.val.toPotential.val.val (mode (-n))
  have hc : ∀ n, Continuous (fun q => c q n) := fun n =>
    (continuous_sourceCoefficient r n).comp continuous_subtype_val
  have hi : Function.Injective c := fun a b hab =>
    Subtype.ext (sourceCoefficients_injective r hab)
  let f := fun q : K => sourceLowerDistribution r t hp h q.val
  have he := isEmbedding_sourceLowerDistribution_on_bounded r t hp h K
    ⟨R, fun _ hq => hq⟩
  let F' : A → T → K := fun a s => ⟨F a s, hF a s⟩
  constructor
  · intro ht n
    exact NLS.equicontinuous_observable_of_coordinates (fun q (_ : Unit) => f q)
      (fun _ => he.continuous) (fun a b hab => he.injective (congrFun hab ()))
      (fun q => c q n) (hc n) F' (fun _ => ht)
  · intro ht
    exact NLS.equicontinuous_observable_of_coordinates c hc hi f he.continuous F' ht

/-- The choice of admissible lower finite-p space does not change
equicontinuity on a common original endpoint norm ball. -/
theorem equicontinuous_sourceLowerDistribution_iff_other_lower (r t u R : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (ht : 1 < (-r-t)*p.toReal)
    (hq : q ≠ ⊤) (hu : 1 < (-r-u)*q.toReal)
    {A T : Type*} [TopologicalSpace T] (F : A → T → WeakStarPotential r)
    (hF : ∀ a s, ‖(F a s).toPotential.val‖ ≤ R) :
    Equicontinuous (fun a s => sourceLowerDistribution r t hp ht (F a s)) ↔
      Equicontinuous (fun a s => sourceLowerDistribution r u hq hu (F a s)) := by
  rw [equicontinuous_sourceLowerDistribution_iff_coefficients r t R hp ht F hF,
    equicontinuous_sourceLowerDistribution_iff_coefficients r u R hq hu F hF]

/-- A Fourier-equicontinuous, endpoint-bounded sequence has one subsequence
converging uniformly in every admissible lower norm. The limit is a continuous
physical weak-star trajectory in the same original norm ball. -/
theorem exists_sourceTrajectory_subseq_all_lower_of_equicontinuous_coefficients
    (r R : ℝ) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (F : ℕ → T → WeakStarPotential r)
    (hF : ∀ n s, ‖(F n s).toPotential.val‖ ≤ R)
    (he : ∀ k : ℤ, Equicontinuous
      (fun n s => (F n s).toPotential.val.val (mode (-k)))) :
    ∃ g : C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ s, Tendsto (fun n => F (φ n) s) atTop (𝓝 (g s).val)) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        TendstoUniformly (fun n s => sourceLowerDistribution r t hp h (F (φ n) s))
          (fun s => sourceLowerDistribution r t hp h (g s).val) atTop := by
  let t₀ := -r-2
  have h₀ : 1 < (-r-t₀)*(1 : ℝ≥0∞).toReal := by
    norm_num [t₀]
  let L := sourceLowerDistribution r t₀ (p := 1) (by simp) h₀
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  have hK : IsCompact (L '' K) :=
    ((isCompact_source_iff_bounded_lower_compact r t₀ (p := 1) (by simp) h₀ K).mp
      (isCompact_sourceNormBall r R)).2
  have heL := (equicontinuous_sourceLowerDistribution_iff_coefficients r t₀ R
    (p := 1) (by simp) h₀ F hF).mpr he
  obtain ⟨g₀, _, φ, hφ, ht⟩ :=
    NLS.exists_subseq_tendstoUniformly_of_equicontinuous_compact_range
      (fun n s => L (F n s)) (L '' K) hK
      (fun n s => ⟨F n s, hF n s, rfl⟩) heL
  have hex (s : T) := existsUnique_source_of_tendsto_lower_normBound r t₀ R
    (p := 1) (by simp) h₀ (fun n => F (φ n) s) (g₀ s)
      (Eventually.of_forall fun n => hF (φ n) s) (ht.tendsto_at s)
  choose g hg using fun s => (hex s).exists
  let g' : T → K := fun s => ⟨g s, (hg s).2.1⟩
  have hgc : Continuous g' :=
    (continuous_source_iff_lowerDistribution r t₀ (p := 1) (by simp) h₀ K
      ⟨R, fun _ hq => hq⟩ g').mpr (by
        have heq : (fun s => L (g s)) = g₀ := funext fun s => (hg s).1
        change Continuous (fun s => L (g s))
        rw [heq]
        exact g₀.continuous)
  refine ⟨⟨g', hgc⟩, φ, hφ, fun s => (hg s).2.2, ?_⟩
  intro t p hp1 hp h
  let : Fact (1 ≤ p) := ⟨hp1⟩
  apply (tendstoUniformly_sourceLowerDistribution_iff_coefficients r t R hp h
    (fun n s => F (φ n) s) g atTop (fun n s => hF (φ n) s)
      (fun s => (hg s).2.1)).mpr
  apply (tendstoUniformly_sourceLowerDistribution_iff_coefficients r t₀ R
    (p := 1) (by simp) h₀ (fun n s => F (φ n) s) g atTop
      (fun n s => hF (φ n) s) (fun s => (hg s).2.1)).mp
  have heq : (fun s => L (g s)) = g₀ := funext fun s => (hg s).1
  change TendstoUniformly (fun n s => L (F (φ n) s)) (fun s => L (g s)) atTop
  rw [heq]
  exact ht

/-- Compact-open extraction for continuous physical trajectories. The same
subsequence works in every admissible lower norm, chosen after the subsequence. -/
theorem exists_sourceTrajectory_subseq_tendsto_of_equicontinuous_coefficients
    (r R : ℝ) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (F : ℕ → C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}))
    (he : ∀ k : ℤ, Equicontinuous
      (fun n s => (F n s).val.toPotential.val.val (mode (-k)))) :
    ∃ g ∈ closure (range F), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (F ∘ φ) atTop (𝓝 g) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        TendstoUniformly (fun n s => sourceLowerDistribution r t hp h (F (φ n) s).val)
          (fun s => sourceLowerDistribution r t hp h (g s).val) atTop := by
  obtain ⟨g, φ, hφ, _, hl⟩ :=
    exists_sourceTrajectory_subseq_all_lower_of_equicontinuous_coefficients r R
      (fun n s => (F n s).val) (fun n s => (F n s).property) he
  have h₀ : 1 < (-r-(-r-2))*(1 : ℝ≥0∞).toReal := by norm_num
  have ht : Tendsto (F ∘ φ) atTop (𝓝 g) := by
    apply (tendsto_sourceTrajectory_iff_lowerDistribution r (-r-2) (p := 1)
      (by simp) h₀ _ ⟨R, fun _ hq => hq⟩ (F ∘ φ) g).mpr
    rw [ContinuousMap.tendsto_iff_tendstoUniformly]
    exact hl (-r-2) 1 (by simp) (by simp) h₀
  exact ⟨g, mem_closure_of_tendsto ht
    (Eventually.of_forall fun n => mem_range_self (φ n)), φ, hφ, ht, hl⟩

/-- In the article range, Fourier equicontinuity is exactly equicontinuity
in the norm of the identical original H-minus-one distributions. -/
theorem equicontinuous_originalHminusOne_iff_coefficients (r R : ℝ)
    (hr : AdmissiblePredualOrder r)
    {A T : Type*} [TopologicalSpace T] (F : A → T → WeakStarPotential r)
    (hF : ∀ a s, ‖(F a s).toPotential.val‖ ≤ R) :
    Equicontinuous (fun a s => potentialHminusOne r hr (F a s).toPotential) ↔
      ∀ n : ℤ, Equicontinuous
        (fun a s => (F a s).toPotential.val.val (mode (-n))) := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using
    equicontinuous_sourceLowerDistribution_iff_coefficients r (-1) R (p := 2)
      (by norm_num) (admissible_hminusOne_threshold r hr) F hF

/-- A closed Fourier-equicontinuous family of trajectories in an original
endpoint norm ball is compact in the compact-open weak-star topology. -/
theorem isCompact_sourceTrajectory_of_isClosed_equicontinuous_coefficients
    (r R : ℝ) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (S : Set C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}))
    (hS : IsClosed S)
    (he : ∀ k : ℤ, Equicontinuous
      (fun f : S => fun s => (f.val s).val.toPotential.val.val (mode (-k)))) :
    IsCompact S := by
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  let := metrizable_sourceNormBall r R
  let : MetricSpace K := TopologicalSpace.metrizableSpaceMetric K
  apply isCompact_iff_isSeqCompact.mpr
  intro F hF
  have heF : ∀ k : ℤ, Equicontinuous
      (fun n s => (F n s).val.toPotential.val.val (mode (-k))) :=
    fun k => (he k).comp (fun n => ⟨F n, hF n⟩)
  obtain ⟨g, _, φ, hφ, ht, _⟩ :=
    exists_sourceTrajectory_subseq_tendsto_of_equicontinuous_coefficients r R F heF
  exact ⟨g, hS.mem_of_tendsto ht (Eventually.of_forall fun n => hF (φ n)), φ, hφ, ht⟩

/-- Fourier-equicontinuous trajectories in a common original endpoint norm
ball have compact closure in the compact-open physical weak-star topology. -/
theorem isCompact_closure_sourceTrajectory_of_equicontinuous_coefficients
    (r R : ℝ) {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (S : Set C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}))
    (he : ∀ k : ℤ, Equicontinuous
      (fun f : S => fun s => (f.val s).val.toPotential.val.val (mode (-k)))) :
    IsCompact (closure S) := by
  apply isCompact_sourceTrajectory_of_isClosed_equicontinuous_coefficients r R
    (closure S) isClosed_closure
  intro k
  let u : C(T, {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}) → T → ℂ :=
    fun f s => (f s).val.toPotential.val.val (mode (-k))
  have hc : Continuous u := continuous_pi fun s =>
    ((continuous_sourceCoefficient r k).comp continuous_subtype_val).comp
      (continuous_eval_const s)
  have he' : Equicontinuous (u ∘ ((↑) : S → _)) := he k
  exact he'.closure' hc

end NLS.Articles.KdVPseudomeasures
