import NLS.ZakharovShabat.SourceSpectralClusters
import NLS.ComplexAnalysis.RealIntervalDiscs
import NLS.ComplexAnalysis.FinitePositiveMargins

/-!
# Midpoint discs for source spectral clusters

Each real-type indexed cluster fits into a disc centered on the real line.
Margins smaller than the intervening periodic gap keep two such discs
disjoint. The margins can later be chosen uniformly for a finite block.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A complex disc centered at the midpoint of the indexed real periodic
gap, enlarged by an adjustable positive margin. -/
def sourceClusterDisc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (ε : ℤ → ℝ) (n : ℤ) : Set ℂ :=
  ball (((canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re +
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)/2 : ℝ)
    (((canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re -
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re)/2 + ε n)

/-- Any positive margin makes the entire real-type five-coordinate cluster
strictly interior to its midpoint disc. -/
theorem sourceSpectralCluster_subset_disc (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ε : ℤ → ℝ) (n : ℤ) (hε : 0 < ε n) :
    sourceSpectralCluster hp hp1 φ n ⊆ sourceClusterDisc hp hp1 φ ε n := by
  intro z hz
  exact real_mem_midpoint_disc_of_mem_Icc hε
    (sourceSpectralCluster_im_eq_zero hp hp1 φ hφ n hz)
    (sourceSpectralCluster_mem_gap hp hp1 φ hφ n hz)

/-- Two indexed midpoint discs are disjoint if their added margins fit
within the positive gap between the indexed periodic endpoint intervals. -/
theorem sourceClusterDiscs_disjoint_of_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (ε : ℤ → ℝ) {i j : ℤ}
    (hεi : 0 ≤ ε i) (hεj : 0 ≤ ε j)
    (hgap : ε i+ε j ≤
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re) :
    Disjoint (sourceClusterDisc hp hp1 φ ε i) (sourceClusterDisc hp hp1 φ ε j) := by
  have hi : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 i)
  have hj : (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re ≤
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 j)
  exact midpoint_discs_disjoint_of_gap hi hj hεi hεj hgap

/-- A finite central block of real-type source clusters fits in pairwise
disjoint complex discs with one shared positive enlargement margin. -/
theorem exists_sourceClusterDiscs_finite_block (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (s : Finset ℤ) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ n ∈ s, sourceSpectralCluster hp hp1 φ n ⊆
        sourceClusterDisc hp hp1 φ (fun _ => ε) n) ∧
      (∀ i ∈ s, ∀ j ∈ s, i < j →
        Disjoint (sourceClusterDisc hp hp1 φ (fun _ => ε) i)
          (sourceClusterDisc hp hp1 φ (fun _ => ε) j)) := by
  obtain ⟨ε, hε, hgap⟩ := exists_positive_margin_for_finite_pairs s
    (fun i j =>
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) j).re -
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) i).re)
    (by
      intro i hi j hj hij
      exact sub_pos.mpr (canonicalPeriodicRight_re_lt_left_of_lt hp hp1
        (periodOnePotential φ) (periodOnePotential_mem φ)
        (isRealType_periodOnePotential φ hφ) hij))
  refine ⟨ε, hε, ?_, ?_⟩
  · intro n hn
    exact sourceSpectralCluster_subset_disc hp hp1 φ hφ (fun _ => ε) n hε
  · intro i hi j hj hij
    apply sourceClusterDiscs_disjoint_of_gap hp hp1 φ (fun _ => ε) hε.le hε.le
    linarith [hgap i hi j hj hij]

end NLS.ZakharovShabat
