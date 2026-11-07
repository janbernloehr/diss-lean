import NLS.Articles.KdVPseudomeasures.SourceWeakStarLimits
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Uniform lower norm criteria for physical weak-star trajectories

On a bounded physical target the compact-open weak-star topology agrees with
uniform lower norm convergence on every compact time set. The compact-time
statements quantify a single error bound for all times, rather than only
pointwise convergence. These are topology lemmas, without any assumed KdV flow.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier.PeriodicFourierLebesgue

/-- Arbitrary-filter convergence of bounded physical trajectories is detected
in the compact-open topology of any admissible original lower norm space. -/
theorem tendsto_sourceTrajectory_iff_lowerDistribution (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K X : Type*} [TopologicalSpace K] {l : Filter X}
    (F : X → C(K,A)) (f : C(K,A)) :
    Tendsto F l (𝓝 f) ↔ Tendsto
      (fun x => (sourceLowerDistributionMapOn r t hp h A hb).comp (F x)) l
      (𝓝 ((sourceLowerDistributionMapOn r t hp h A hb).comp f)) :=
  (isEmbedding_sourceLowerDistributionTrajectory r t hp h A hb).tendsto_nhds_iff

/-- Compact-open convergence is uniform lower norm convergence on every compact time set. -/
theorem tendsto_sourceTrajectory_iff_uniformOn_compacts (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K X : Type*} [TopologicalSpace K] {l : Filter X}
    (F : X → C(K,A)) (f : C(K,A)) :
    Tendsto F l (𝓝 f) ↔ ∀ B : Set K, IsCompact B →
      TendstoUniformlyOn
        (fun x k => sourceLowerDistribution r t hp h (F x k).val)
        (fun k => sourceLowerDistribution r t hp h (f k).val) l B := by
  rw [tendsto_sourceTrajectory_iff_lowerDistribution r t hp h A hb F f,
    ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  rfl

/-- On compact time domains, one eventual lower norm error bound holds for every time. -/
theorem tendsto_sourceTrajectory_iff_uniform_lower (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K X : Type*} [TopologicalSpace K] [CompactSpace K] {l : Filter X}
    (F : X → C(K,A)) (f : C(K,A)) :
    Tendsto F l (𝓝 f) ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ k : K,
      ‖sourceLowerDistribution r t hp h (F x k).val -
        sourceLowerDistribution r t hp h (f k).val‖ < ε := by
  rw [tendsto_sourceTrajectory_iff_lowerDistribution r t hp h A hb F f,
    ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
  simp only [ContinuousMap.comp_apply, sourceLowerDistributionMapOn,
    ContinuousMap.coe_mk, dist_eq_norm, norm_sub_rev]

/-- Continuous dependence on compact-time trajectories is exactly the
neighborhood form of uniform lower norm dependence. -/
theorem continuous_sourceTrajectory_iff_uniform_lower (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K X : Type*} [TopologicalSpace K] [CompactSpace K] [TopologicalSpace X]
    (S : X → C(K,A)) :
    Continuous S ↔ ∀ x : X, ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, ∀ k : K,
      ‖sourceLowerDistribution r t hp h (S y k).val -
        sourceLowerDistribution r t hp h (S x k).val‖ < ε := by
  rw [continuous_iff_continuousAt]
  exact forall_congr' fun x => tendsto_sourceTrajectory_iff_uniform_lower r t hp h A hb S (S x)

/-- On a bounded physical initial-data set, sequential uniform lower norm
dependence suffices for continuity into the full weak-star trajectory space. -/
theorem continuous_sourceTrajectory_iff_seq_uniform_lower (r t : ℝ)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (h : 1 < (-r-t)*p.toReal)
    (A B : Set (WeakStarPotential r)) (hA : PotentialNormBounded r A)
    (hB : PotentialNormBounded r B)
    {K : Type*} [TopologicalSpace K] [CompactSpace K] (S : A → C(K,B)) :
    Continuous S ↔ ∀ (x : ℕ → A) (a : A), Tendsto x atTop (𝓝 a) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ k : K,
        ‖sourceLowerDistribution r t hp h (S (x n) k).val -
          sourceLowerDistribution r t hp h (S a k).val‖ < ε := by
  rw [continuous_from_source_iff_seqContinuous r A hA S]
  constructor
  · intro hS x a hx
    exact (tendsto_sourceTrajectory_iff_uniform_lower r t hp h B hB _ _).mp (hS hx)
  · intro hS x a hx
    exact (tendsto_sourceTrajectory_iff_uniform_lower r t hp h B hB _ _).mpr (hS x a hx)

/-- In the article range, compact-time weak-star convergence is uniform
convergence of the identical original physical H-minus-one distributions. -/
theorem tendsto_sourceTrajectory_iff_uniform_originalHminusOne (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (A : Set (WeakStarPotential r)) (hb : PotentialNormBounded r A)
    {K X : Type*} [TopologicalSpace K] [CompactSpace K] {l : Filter X}
    (F : X → C(K,A)) (f : C(K,A)) :
    Tendsto F l (𝓝 f) ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x in l, ∀ k : K,
      ‖potentialHminusOne r hr (F x k).val.toPotential -
        potentialHminusOne r hr (f k).val.toPotential‖ < ε := by
  simpa only [sourceLowerDistribution_eq_potentialHminusOne r hr] using
    tendsto_sourceTrajectory_iff_uniform_lower r (-1) (p := 2) (by norm_num)
      (admissible_hminusOne_threshold r hr) A hb F f

end NLS.Articles.KdVPseudomeasures
