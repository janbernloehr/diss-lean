import NLS.ZakharovShabat.SourceAbelianMomentLemma20_1
import NLS.ZakharovShabat.SourceFiniteGap

/-! # Finite-gap moment sums and their limits

Positive moments vanish outside the open-gap set. On finite-gap sources,
the infinite sum is therefore an actual finite sum, with one support for
all numerator indices and positive orders. A common finite gap support
also permits passage to limits when gaps collapse, as in Lemma 20.2.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable (A : SourceAbelianMomentAtlas hp hp1 W s)

theorem positive_moment_hasSum_of_gap_support (ψ : CoeffPair p) (hψ : ψ ∈ A.domain)
    (S : Finset ℤ)
    (hS : ∀ k ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k = 0)
    (n : ℤ) (m : ℕ) :
    HasSum (fun k => A.moment n k (m+1) ψ) (∑ k ∈ S, A.moment n k (m+1) ψ) :=
  hasSum_sum_of_ne_finset_zero (fun k hk => A.moment_succ_of_collapsed ψ hψ n k (hS k hk) m)

/-- One finite set of actual open gaps supports all positive moment sums. -/
theorem exists_finiteGap_moment_sums (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ S : Finset ℤ,
      (∀ k, k ∈ S ↔ canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) k ≠ 0) ∧
      ∀ (n : ℤ) (m : ℕ), HasSum (fun k => A.moment n k (m+1) φ.val)
        (∑ k ∈ S, A.moment n k (m+1) φ.val) := by
  classical
  refine ⟨hf.toFinset,fun k => hf.mem_toFinset,?_⟩
  intro n m
  apply A.positive_moment_hasSum_of_gap_support φ.val (A.realType_subset_domain φ.property)
  intro k hk
  by_contra hg
  exact hk (hf.mem_toFinset.mpr hg)

/-- A fixed finite support permits the total moment sum to pass through
a source limit. The limiting support need not remain open. -/
theorem positive_moment_sum_tendsto_of_eventually_fixed_gap_support
    {ι : Type*} {l : Filter ι} [l.NeBot] (ψ : ι → CoeffPair p) (φ : CoeffPair p)
    (hφ : φ ∈ A.domain) (hlim : Tendsto ψ l (𝓝 φ)) (S : Finset ℤ)
    (hS : ∀ᶠ i in l, ψ i ∈ A.domain ∧ ∀ k ∉ S,
      canonicalPeriodicGap hp hp1 (periodOnePotential (ψ i)) (periodOnePotential_mem (ψ i)) k = 0)
    (n : ℤ) (m : ℕ) :
    Tendsto (fun i => ∑' k : ℤ, A.moment n k (m+1) (ψ i)) l
      (𝓝 (∑' k : ℤ, A.moment n k (m+1) φ)) := by
  have hterm (k : ℤ) : Tendsto (fun i => A.moment n k (m+1) (ψ i)) l
      (𝓝 (A.moment n k (m+1) φ)) :=
    (A.analytic_moment n k (m+1) φ hφ).continuousAt.tendsto.comp hlim
  have hzero (k : ℤ) (hk : k ∉ S) : A.moment n k (m+1) φ = 0 := by
    have he : ∀ᶠ i in l, A.moment n k (m+1) (ψ i) = 0 := hS.mono (fun i hi =>
      A.moment_succ_of_collapsed (ψ i) hi.1 n k (hi.2 k hk) m)
    exact tendsto_nhds_unique (hterm k) (tendsto_const_nhds.congr' (he.mono (fun _ h => h.symm)))
  rw [tsum_eq_sum hzero]
  have hfinite := tendsto_finsetSum S (fun k _ => hterm k)
  apply hfinite.congr'
  filter_upwards [hS] with i hi
  exact (A.positive_moment_hasSum_of_gap_support (ψ i) hi.1 S hi.2 n m).tsum_eq.symm

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
