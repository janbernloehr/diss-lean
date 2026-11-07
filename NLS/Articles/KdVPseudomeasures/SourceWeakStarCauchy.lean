import NLS.FunctionalAnalysis.UniformCauchyLimit
import NLS.Articles.KdVPseudomeasures.SourceWeakStarUniformControl

/-!
# Cauchy criteria for bounded physical weak-star families

The original endpoint bound supplies compactness, while Cauchy Fourier tests
identify a unique limit. Every admissible lower norm converges to the same
original distribution. Index filters and testing sets are arbitrary; no
endpoint norm convergence or boundedness of general convergent nets is used.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest

/-- Cauchy Fourier coefficients and an eventual specified endpoint bound
give a unique physical weak-star limit with that bound. The same limit works
in every admissible lower finite-p space, selected after the limit. -/
theorem existsUnique_source_of_cauchy_coefficients_normBound (r R : ℝ)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R)
    (hc : ∀ n : ℤ, Cauchy (l.map (fun k => (x k).toPotential.val.val (mode (-n))))) :
    ∃! a : WeakStarPotential r, ‖a.toPotential.val‖ ≤ R ∧ Tendsto x l (𝓝 a) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        Tendsto (fun k => sourceLowerDistribution r t hp h (x k)) l
          (𝓝 (sourceLowerDistribution r t hp h a)) := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  choose g hg using fun n => cauchy_map_iff_exists_tendsto.mp (hc n)
  obtain ⟨a, ha, _⟩ := existsUnique_source_of_tendsto_coefficients_normBound r R x g hb hg
  refine ⟨a, ⟨ha.2.1, ha.2.2, ?_⟩, ?_⟩
  · intro t p hp1 hp h
    let : Fact (1 ≤ p) := ⟨hp1⟩
    exact (tendsto_source_iff_lowerDistribution_of_eventually_normBound
      r t R hp h x a hb).mp ha.2.2
  · intro b hba
    exact tendsto_nhds_unique hba.2.1 ha.2.2

/-- Under an eventual original endpoint bound, being Cauchy in one
admissible lower norm is equivalent to being Cauchy in every Fourier mode. -/
theorem cauchy_sourceLowerDistribution_iff_coefficients (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) :
    Cauchy (l.map (fun k => sourceLowerDistribution r t hp h (x k))) ↔
      ∀ n : ℤ, Cauchy (l.map (fun k => (x k).toPotential.val.val (mode (-n)))) := by
  constructor
  · intro hc
    obtain ⟨g, hg⟩ := cauchy_map_iff_exists_tendsto.mp hc
    obtain ⟨a, ha, _⟩ := existsUnique_source_of_tendsto_lower_normBound r t R hp h x g hb hg
    intro n
    exact cauchy_map_iff_exists_tendsto.mpr
      ⟨a.toPotential.val.val (mode (-n)), ((continuous_sourceCoefficient r n).tendsto a).comp ha.2.2⟩
  · intro hc
    obtain ⟨a, ha, _⟩ := existsUnique_source_of_cauchy_coefficients_normBound r R x hb hc
    exact cauchy_map_iff_exists_tendsto.mpr
      ⟨sourceLowerDistribution r t hp h a,
        (tendsto_source_iff_lowerDistribution_of_eventually_normBound
          r t R hp h x a hb).mp ha.2.1⟩

/-- Cauchy lower norm tests are independent of the chosen admissible
finite-p space for eventually endpoint-bounded physical families. -/
theorem cauchy_sourceLowerDistribution_iff_other_lower (r t u R : ℝ)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (ht : 1 < (-r-t)*p.toReal)
    (hq : q ≠ ⊤) (hu : 1 < (-r-u)*q.toReal)
    {X : Type*} {l : Filter X} [NeBot l] (x : X → WeakStarPotential r)
    (hb : ∀ᶠ k in l, ‖(x k).toPotential.val‖ ≤ R) :
    Cauchy (l.map (fun k => sourceLowerDistribution r t hp ht (x k))) ↔
      Cauchy (l.map (fun k => sourceLowerDistribution r u hq hu (x k))) := by
  rw [cauchy_sourceLowerDistribution_iff_coefficients r t R hp ht x hb,
    cauchy_sourceLowerDistribution_iff_coefficients r u R hq hu x hb]

/-- Uniformly Cauchy Fourier tests, with one eventual endpoint bound
for all testing parameters, give a unique physical limit family. Convergence
is uniform in every admissible lower norm, without time continuity hypotheses. -/
theorem existsUnique_sourceFamily_of_uniformCauchy_coefficients_normBound (r R : ℝ)
    {A B : Type*} {l : Filter A} [NeBot l] (F : A → B → WeakStarPotential r)
    (hb : ∀ᶠ a in l, ∀ b, ‖(F a b).toPotential.val‖ ≤ R)
    (hc : ∀ n : ℤ, UniformCauchySeqOn
      (fun a b => (F a b).toPotential.val.val (mode (-n))) l univ) :
    ∃! g : B → WeakStarPotential r,
      (∀ b, ‖(g b).toPotential.val‖ ≤ R) ∧
      (∀ b, Tendsto (fun a => F a b) l (𝓝 (g b))) ∧
      ∀ (t : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
        (h : 1 < (-r-t)*p.toReal),
        letI : Fact (1 ≤ p) := ⟨hp1⟩
        TendstoUniformly (fun a b => sourceLowerDistribution r t hp h (F a b))
          (fun b => sourceLowerDistribution r t hp h (g b)) l := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  choose G hG using fun n => NLS.exists_limit_of_uniformCauchyOn
    (fun a b => (F a b).toPotential.val.val (mode (-n))) univ (hc n)
  obtain ⟨g, hg, _⟩ := existsUnique_sourceFamily_of_uniform_coefficients_normBound
    r R F (fun b n => G n b) l hb
      (fun n => tendstoUniformlyOn_univ.mp (hG n))
  refine ⟨g, ⟨hg.2.1, hg.2.2.1, hg.2.2.2⟩, ?_⟩
  intro g' hg'
  funext b
  exact tendsto_nhds_unique (hg'.2.1 b) (hg.2.2.1 b)

/-- A uniformly Cauchy family in just one admissible lower norm has a
unique physical limit family with the same eventual original endpoint bound,
and converges uniformly in every other admissible lower norm as well. -/
theorem existsUnique_sourceFamily_of_uniformCauchy_lower_normBound (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A B : Type*} {l : Filter A} [NeBot l] (F : A → B → WeakStarPotential r)
    (hb : ∀ᶠ a in l, ∀ b, ‖(F a b).toPotential.val‖ ≤ R)
    (hc : UniformCauchySeqOn
      (fun a b => sourceLowerDistribution r t hp h (F a b)) l univ) :
    ∃! g : B → WeakStarPotential r,
      (∀ b, ‖(g b).toPotential.val‖ ≤ R) ∧
      (∀ b, Tendsto (fun a => F a b) l (𝓝 (g b))) ∧
      ∀ (u : ℝ) (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hq : q ≠ ⊤)
        (hu : 1 < (-r-u)*q.toReal),
        letI : Fact (1 ≤ q) := ⟨hq1⟩
        TendstoUniformly (fun a b => sourceLowerDistribution r u hq hu (F a b))
          (fun b => sourceLowerDistribution r u hq hu (g b)) l := by
  let : T2Space (WeakStarPotential r) :=
    (isClosedEmbedding_weakStarPotentialCoordinates r).isEmbedding.t2Space
  obtain ⟨G, hG⟩ := NLS.exists_limit_of_uniformCauchyOn
    (fun a b => sourceLowerDistribution r t hp h (F a b)) univ hc
  have ht := tendstoUniformlyOn_univ.mp hG
  have he (b : B) := existsUnique_source_of_tendsto_lower_normBound r t R hp h
    (fun a => F a b) (G b) (hb.mono fun a ha => ha b) (ht.tendsto_at b)
  choose g hg using fun b => (he b).exists
  have hEq : (fun b => sourceLowerDistribution r t hp h (g b)) = G :=
    funext fun b => (hg b).1
  have htl : TendstoUniformly (fun a b => sourceLowerDistribution r t hp h (F a b))
      (fun b => sourceLowerDistribution r t hp h (g b)) l := by rwa [hEq]
  have hcoeff := (tendstoUniformly_sourceLowerDistribution_iff_coefficients_of_eventually_normBound
    r t R hp h F g l hb (fun b => (hg b).2.1)).mp htl
  refine ⟨g, ⟨fun b => (hg b).2.1, fun b => (hg b).2.2, ?_⟩, ?_⟩
  · intro u q hq1 hq hu
    let : Fact (1 ≤ q) := ⟨hq1⟩
    exact (tendstoUniformly_sourceLowerDistribution_iff_coefficients_of_eventually_normBound
      r u R hq hu F g l hb (fun b => (hg b).2.1)).mpr hcoeff
  · intro g' hg'
    funext b
    exact tendsto_nhds_unique (hg'.2.1 b) (hg b).2.2

/-- Uniform Cauchy lower norm control is equivalent to uniform Cauchy
control of every Fourier mode under one eventual physical endpoint bound. -/
theorem uniformCauchy_sourceLowerDistribution_iff_coefficients (r t R : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    {A B : Type*} {l : Filter A} [NeBot l] (F : A → B → WeakStarPotential r)
    (hb : ∀ᶠ a in l, ∀ b, ‖(F a b).toPotential.val‖ ≤ R) :
    UniformCauchySeqOn (fun a b => sourceLowerDistribution r t hp h (F a b)) l univ ↔
      ∀ n : ℤ, UniformCauchySeqOn
        (fun a b => (F a b).toPotential.val.val (mode (-n))) l univ := by
  constructor
  · intro hc
    obtain ⟨g, hg, _⟩ := existsUnique_sourceFamily_of_uniformCauchy_lower_normBound
      r t R hp h F hb hc
    have ht := (tendstoUniformly_sourceLowerDistribution_iff_coefficients_of_eventually_normBound
      r t R hp h F g l hb hg.1).mp (hg.2.2 t p Fact.out hp h)
    exact fun n => (tendstoUniformlyOn_univ.mpr (ht n)).uniformCauchySeqOn
  · intro hc
    obtain ⟨g, hg, _⟩ := existsUnique_sourceFamily_of_uniformCauchy_coefficients_normBound r R F hb hc
    exact (tendstoUniformlyOn_univ.mpr (hg.2.2 t p Fact.out hp h)).uniformCauchySeqOn

end NLS.Articles.KdVPseudomeasures
