import NLS.ZakharovShabat.SourcePsiGapRootLimitPlacement
import NLS.ZakharovShabat.SourcePsiRootPlacementDomain

/-!
# Gap-contained roots belong to one isolating-disc family

The local spectral isolation theorem gives one family of discs around
the limiting real-type potential that contains every nearby periodic
gap. Thus every choice of deleted roots within those gaps belongs to
the same open retained-root placement set used by the psi Jacobian.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One local isolating-disc family contains every gap-contained
deleted-root vector over all nearby source potentials. -/
theorem exists_uniform_rootPlacement_of_gapRoots
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
        ∀ ψ ∈ U, ∀ a : DeletedCoeff p n,
          (∀ m : ℤ, m ≠ n →
            displacedRoots (a : Coeff p) m ∈
              sourcePeriodicSegment hp hp1 ψ m) →
          a ∈ sourcePsiRootPlacementSet hp hp1 φ N ε n := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,_,hφU,hcluster,_⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,U,hUopen,hφU,?_⟩
  intro ψ hψ a hgap m hmn
  exact sourcePeriodicSegment_subset_isolatingDisc
    hp hp1 φ ψ N ε m (hcluster ψ hψ m) (hgap m hmn)

/-- Along a convergent source sequence, gap-contained roots eventually
lie in one fixed open root-placement set. Their strong subsequence
limit lies in that same set. -/
theorem exists_tendsto_subseq_deletedGapRoots_in_common_rootPlacement
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (n : ℤ) (a : ℕ → DeletedCoeff p n)
    (hgap : ∀ k : ℕ, ∀ m : ℤ, m ≠ n →
      displacedRoots (a k : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (ψ k) m) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ b : DeletedCoeff p n, ∃ σ : ℕ → ℕ,
        StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 b) ∧
        (∀ᶠ k : ℕ in atTop,
          a (σ k) ∈ sourcePsiRootPlacementSet hp hp1 φ N ε n) ∧
        b ∈ sourcePsiRootPlacementSet hp hp1 φ N ε n := by
  obtain ⟨N,ε,hε,hεmax,U,hUopen,hφU,hplace⟩ :=
    exists_uniform_rootPlacement_of_gapRoots hp hp1 φ hφ n
  obtain ⟨b,σ,hσ,hb,hbgap⟩ :=
    exists_tendsto_subseq_deletedGapRoots_mem_limit_segments
      hp hp1 φ hφ ψ hψ n a hgap
  refine ⟨N,ε,hε,hεmax,b,σ,hσ,hb,?_,hplace φ hφU b hbgap⟩
  have hψU : ∀ᶠ k : ℕ in atTop, ψ k ∈ U :=
    hψ.eventually (hUopen.mem_nhds hφU)
  filter_upwards [hψU.filter_mono hσ.tendsto_atTop] with k hk
  exact hplace (ψ (σ k)) hk (a (σ k)) (hgap (σ k))

end NLS.ZakharovShabat
