import NLS.ZakharovShabat.SourceOpenGapDensity
import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # Generic sources have every periodic gap open

The countable intersection of the previously proved dense open one-gap
loci is a dense G-delta in the complete real source space. In particular
infinitely many gaps are open generically, as stated in Section 7.
-/
noncomputable section
open Set Metric Filter Topology TopologicalSpace
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance sourceGenericOpenGaps_baire : BaireSpace (realTypeSourceSubmodule p) := by
  let : IsCompletelyPseudoMetrizableSpace (realTypeSourceSubmodule p) :=
    PseudoMetricSpace.toIsCompletelPseudoMetrizableSpace
  exact BaireSpace.of_completelyPseudoMetrizable

/-- The actual real source locus with every indexed periodic gap open. -/
def sourceAllOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Set (realTypeSourceSubmodule p) := ⋂ n : ℤ, sourceOpenGapRealLocus hp hp1 n

/-- All periodic gaps are simultaneously open on a dense G-delta. -/
theorem isGδ_and_dense_sourceAllOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsGδ (sourceAllOpenGapRealLocus hp hp1) ∧ Dense (sourceAllOpenGapRealLocus hp hp1) := by
  constructor
  · exact IsGδ.iInter (fun n => (isOpen_sourceOpenGapRealLocus hp hp1 n).isGδ)
  · exact dense_iInter_of_isOpen (isOpen_sourceOpenGapRealLocus hp hp1)
      (dense_sourceOpenGapRealLocus hp hp1)

/-- The all-open-gap property is residual in the actual real Banach source space. -/
theorem sourceAllOpenGapRealLocus_mem_residual (hp : p ≠ ⊤) (hp1 : 1 < p) :
    sourceAllOpenGapRealLocus hp hp1 ∈ residual (realTypeSourceSubmodule p) := by
  obtain ⟨hg,hd⟩ := isGδ_and_dense_sourceAllOpenGapRealLocus hp hp1
  exact mem_residual.mpr ⟨_,Subset.rfl,hg,hd⟩

/-- Every all-open-gap source has infinitely many actual open periodic gaps. -/
theorem infinite_open_gaps_of_mem_sourceAllOpenGapRealLocus (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∈ sourceAllOpenGapRealLocus hp hp1) :
    {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem _) n ≠ 0}.Infinite := by
  have he : {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
      (periodOnePotential_mem _) n ≠ 0} = univ := by
    apply eq_univ_of_forall
    intro n
    exact mem_iInter.mp hφ n
  rw [he]
  exact Set.infinite_univ

/-- Infinitely many actual periodic gaps are open for residual real sources. -/
theorem eventually_residual_infinite_source_open_gaps (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∀ᶠ φ : realTypeSourceSubmodule p in residual (realTypeSourceSubmodule p),
      {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential φ.val)
        (periodOnePotential_mem _) n ≠ 0}.Infinite := by
  filter_upwards [sourceAllOpenGapRealLocus_mem_residual hp hp1] with φ hφ
  exact infinite_open_gaps_of_mem_sourceAllOpenGapRealLocus hp hp1 φ hφ

end NLS.ZakharovShabat
