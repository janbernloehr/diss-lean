import NLS.FunctionalAnalysis.CompactCoordinateControl
import NLS.Articles.KdVPseudomeasures.SourceWeakStarCompactSets

/-!
# Uniform Fourier tests on physical endpoint norm balls

The endpoint bound is the norm of the original distribution. Finitely many
original Fourier coefficients control every admissible lower norm, uniformly
on that ball. Uniform convergence of each coefficient therefore suffices for
uniform lower norm convergence, even for families with no time continuity.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

/-- The original Fourier coefficients separate the entire physical weak-star space. -/
theorem sourceCoefficients_injective (r : ℝ) :
    Function.Injective (fun q : WeakStarPotential r =>
      fun n : ℤ => q.toPotential.val.val (mode (-n))) := by
  intro a b hab
  apply (isClosedEmbedding_weakStarPotentialCoordinates r).injective
  apply WeightedCoeff.weakStarCoordinates_injective r
  funext n
  simpa only [weakStarPotentialCoordinates, potentialCoordinates_apply] using congrFun hab n

/-- Finitely many original Fourier tests control any admissible lower norm
uniformly on a specified original endpoint norm ball. -/
theorem exists_finite_sourceCoefficient_control_lower_norm (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset ℤ, ∃ δ > 0, ∀ a b : WeakStarPotential r,
      ‖a.toPotential.val‖ ≤ R → ‖b.toPotential.val‖ ≤ R →
      (∀ n ∈ J, dist (a.toPotential.val.val (mode (-n)))
        (b.toPotential.val.val (mode (-n))) < δ) →
      dist (sourceLowerDistribution r t hp h a) (sourceLowerDistribution r t hp h b) < ε := by
  let K := {q : WeakStarPotential r | ‖q.toPotential.val‖ ≤ R}
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_sourceNormBall r R)
  let c : K → ℤ → ℂ := fun q n => q.val.toPotential.val.val (mode (-n))
  have hc : ∀ n, Continuous (fun q => c q n) := fun n =>
    (continuous_sourceCoefficient r n).comp continuous_subtype_val
  have hi : Function.Injective c := fun a b hab =>
    Subtype.ext (sourceCoefficients_injective r hab)
  have hf := (isEmbedding_sourceLowerDistribution_on_bounded r t hp h K
    ⟨R, fun _ hq => hq⟩).continuous
  obtain ⟨J, δ, hδ, hJ⟩ := NLS.exists_finite_coordinates_control_on_compact
    c hc hi (fun q : K => sourceLowerDistribution r t hp h q.val) hf ε hε
  exact ⟨J, δ, hδ, fun a b ha hb hab => hJ ⟨a, ha⟩ ⟨b, hb⟩ hab⟩

/-- Uniform convergence in one admissible lower norm is equivalent to uniform
convergence of each original Fourier coefficient, under a common endpoint bound.
The family parameter, testing set and convergence filter are arbitrary. -/
theorem tendstoUniformly_sourceLowerDistribution_iff_coefficients (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A B : Type*} (F : A → B → WeakStarPotential r) (g : B → WeakStarPotential r)
    (l : Filter A) (hF : ∀ a b, ‖(F a b).toPotential.val‖ ≤ R)
    (hg : ∀ b, ‖(g b).toPotential.val‖ ≤ R) :
    TendstoUniformly (fun a b => sourceLowerDistribution r t hp h (F a b))
      (fun b => sourceLowerDistribution r t hp h (g b)) l ↔
    ∀ n : ℤ, TendstoUniformly
      (fun a b => (F a b).toPotential.val.val (mode (-n)))
      (fun b => (g b).toPotential.val.val (mode (-n))) l := by
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
  let F' : A → B → K := fun a b => ⟨F a b, hF a b⟩
  let g' : B → K := fun b => ⟨g b, hg b⟩
  constructor
  · intro ht n
    exact NLS.tendstoUniformly_observable_of_coordinates (fun q (_ : Unit) => f q)
      (fun _ => he.continuous) (fun a b hab => he.injective (congrFun hab ()))
      (fun q => c q n) (hc n) F' g' l (fun _ => ht)
  · intro ht
    exact NLS.tendstoUniformly_observable_of_coordinates c hc hi f he.continuous F' g' l ht

/-- The uniform coefficient criterion needs only an eventual endpoint bound,
provided that the same bound holds for the proposed limit family. -/
theorem tendstoUniformly_sourceLowerDistribution_iff_coefficients_of_eventually_normBound
    (r t R : ℝ) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A B : Type*} (F : A → B → WeakStarPotential r) (g : B → WeakStarPotential r)
    (l : Filter A) (hF : ∀ᶠ a in l, ∀ b, ‖(F a b).toPotential.val‖ ≤ R)
    (hg : ∀ b, ‖(g b).toPotential.val‖ ≤ R) :
    TendstoUniformly (fun a b => sourceLowerDistribution r t hp h (F a b))
      (fun b => sourceLowerDistribution r t hp h (g b)) l ↔
    ∀ n : ℤ, TendstoUniformly
      (fun a b => (F a b).toPotential.val.val (mode (-n)))
      (fun b => (g b).toPotential.val.val (mode (-n))) l := by
  classical
  let F' : A → B → WeakStarPotential r := fun a b =>
    if ‖(F a b).toPotential.val‖ ≤ R then F a b else g b
  have hb : ∀ a b, ‖(F' a b).toPotential.val‖ ≤ R := by
    intro a b
    dsimp [F']
    split_ifs with he
    · exact he
    · exact hg b
  have he : F =ᶠ[l] F' := hF.mono fun a ha => by
    funext b
    simp only [F', if_pos (ha b)]
  have hl : (fun a b => sourceLowerDistribution r t hp h (F a b)) =ᶠ[l]
      (fun a b => sourceLowerDistribution r t hp h (F' a b)) :=
    he.mono fun a ha => congrArg
      (fun f : B → WeakStarPotential r => fun b => sourceLowerDistribution r t hp h (f b)) ha
  rw [tendstoUniformly_congr hl,
    tendstoUniformly_sourceLowerDistribution_iff_coefficients r t R hp h F' g l hb hg]
  exact forall_congr' fun n => (tendstoUniformly_congr
    (he.mono fun a ha => congrArg
      (fun f : B → WeakStarPotential r => fun b =>
        (f b).toPotential.val.val (mode (-n))) ha)).symm

/-- Uniform coefficient limits of eventually endpoint-bounded families uniquely
recover a physical limit family with the same bound. One recovered family works
for uniform convergence in every admissible lower finite-p norm. -/
theorem existsUnique_sourceFamily_of_uniform_coefficients_normBound (r R : ℝ)
    {A B : Type*} (F : A → B → WeakStarPotential r) (G : B → ℤ → ℂ)
    (l : Filter A) [NeBot l]
    (hF : ∀ᶠ a in l, ∀ b, ‖(F a b).toPotential.val‖ ≤ R)
    (hG : ∀ n : ℤ, TendstoUniformly
      (fun a b => (F a b).toPotential.val.val (mode (-n))) (fun b => G b n) l) :
    ∃! g : B → WeakStarPotential r,
      (∀ b n, (g b).toPotential.val.val (mode (-n)) = G b n) ∧
      (∀ b, ‖(g b).toPotential.val‖ ≤ R) ∧
      (∀ b, Tendsto (fun a => F a b) l (𝓝 (g b))) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        TendstoUniformly (fun a b => sourceLowerDistribution r t hp h (F a b))
          (fun b => sourceLowerDistribution r t hp h (g b)) l := by
  have hex (b : B) := existsUnique_source_of_tendsto_coefficients_normBound r R
    (fun a => F a b) (G b) (hF.mono fun a ha => ha b)
      (fun n => (hG n).tendsto_at b)
  choose g hg using fun b => (hex b).exists
  refine ⟨g, ⟨fun b => (hg b).1, fun b => (hg b).2.1,
    fun b => (hg b).2.2, ?_⟩, ?_⟩
  · intro t p hp1 hp h
    let : Fact (1 ≤ p) := ⟨hp1⟩
    apply (tendstoUniformly_sourceLowerDistribution_iff_coefficients_of_eventually_normBound
      r t R hp h F g l hF (fun b => (hg b).2.1)).mpr
    intro n
    have he : (fun b => (g b).toPotential.val.val (mode (-n))) = fun b => G b n :=
      funext fun b => (hg b).1 n
    rw [he]
    exact hG n
  · intro g' hg'
    funext b
    apply sourceCoefficients_injective r
    funext n
    exact (hg'.1 b n).trans ((hg b).1 n).symm

/-- On families with a common original endpoint bound, the choice of admissible
lower finite-p norm does not change uniform convergence. -/
theorem tendstoUniformly_sourceLowerDistribution_iff_other_lower (r t u R : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (ht : 1 < (-r-t)*p.toReal)
    (hq : q ≠ ⊤) (hu : 1 < (-r-u)*q.toReal)
    {A B : Type*} (F : A → B → WeakStarPotential r) (g : B → WeakStarPotential r)
    (l : Filter A) (hF : ∀ a b, ‖(F a b).toPotential.val‖ ≤ R)
    (hg : ∀ b, ‖(g b).toPotential.val‖ ≤ R) :
    TendstoUniformly (fun a b => sourceLowerDistribution r t hp ht (F a b))
      (fun b => sourceLowerDistribution r t hp ht (g b)) l ↔
    TendstoUniformly (fun a b => sourceLowerDistribution r u hq hu (F a b))
      (fun b => sourceLowerDistribution r u hq hu (g b)) l := by
  rw [tendstoUniformly_sourceLowerDistribution_iff_coefficients r t R hp ht F g l hF hg,
    tendstoUniformly_sourceLowerDistribution_iff_coefficients r u R hq hu F g l hF hg]

/-- In the article range, finitely many original Fourier tests control the
H-minus-one norm of the identical original distributions. -/
theorem exists_finite_sourceCoefficient_control_originalHminusOne (r R : ℝ)
    (hr : AdmissiblePredualOrder r) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset ℤ, ∃ δ > 0, ∀ a b : WeakStarPotential r,
      ‖a.toPotential.val‖ ≤ R → ‖b.toPotential.val‖ ≤ R →
      (∀ n ∈ J, dist (a.toPotential.val.val (mode (-n)))
        (b.toPotential.val.val (mode (-n))) < δ) →
      dist (potentialHminusOne r hr a.toPotential) (potentialHminusOne r hr b.toPotential) < ε := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using
    exists_finite_sourceCoefficient_control_lower_norm r (-1) R (p := 2)
      (by norm_num) (admissible_hminusOne_threshold r hr) ε hε

/-- Uniform Fourier convergence on a common endpoint ball is exactly uniform
convergence in the original physical H-minus-one norm in the article range. -/
theorem tendstoUniformly_originalHminusOne_iff_coefficients (r R : ℝ)
    (hr : AdmissiblePredualOrder r)
    {A B : Type*} (F : A → B → WeakStarPotential r) (g : B → WeakStarPotential r)
    (l : Filter A) (hF : ∀ a b, ‖(F a b).toPotential.val‖ ≤ R)
    (hg : ∀ b, ‖(g b).toPotential.val‖ ≤ R) :
    TendstoUniformly (fun a b => potentialHminusOne r hr (F a b).toPotential)
      (fun b => potentialHminusOne r hr (g b).toPotential) l ↔
    ∀ n : ℤ, TendstoUniformly
      (fun a b => (F a b).toPotential.val.val (mode (-n)))
      (fun b => (g b).toPotential.val.val (mode (-n))) l := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using
    tendstoUniformly_sourceLowerDistribution_iff_coefficients r (-1) R (p := 2)
      (by norm_num) (admissible_hminusOne_threshold r hr) F g l hF hg

end NLS.Articles.KdVPseudomeasures
