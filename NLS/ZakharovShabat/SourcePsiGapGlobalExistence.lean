import NLS.ZakharovShabat.SourcePsiGapSolvability
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Sequences

/-!
# Global existence of real gap psi solutions

The real-type source locus is connected. Solvability is locally open
there by the real implicit branch, and closed by compactness of
gap-contained roots and contour-independent passage to limits. Since
the free source is solvable, every real-type source is solvable.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- For each deleted index, every real-type source has gap-contained
roots solving the selected psi equation on a valid real-centered
contour family. -/
theorem sourcePsiGapSolvable_of_realType
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    SourcePsiGapSolvable hp hp1 n φ := by
  let S : Set (realTypeSourceLocus p) :=
    {x | SourcePsiGapSolvable hp hp1 n x.val}
  have hSopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hlocal := eventually_sourcePsiGapSolvable_of_solution
      hp hp1 n x.val hx
    have hlocal' := continuous_subtype_val.continuousAt.eventually hlocal
    apply hlocal'.mono
    intro y hy
    exact hy y.property
  have hSclosed : IsClosed S := by
    apply IsSeqClosed.isClosed
    intro ψ x hψ hlim
    have hval : Tendsto (fun k => (ψ k).val) atTop (𝓝 x.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp hlim
    exact sourcePsiGapSolvable_of_tendsto hp hp1 n x.val x.property
      (fun k => (ψ k).val) hval hψ
  letI : ConnectedSpace (realTypeSourceLocus p) :=
    Subtype.connectedSpace (isConnected_realTypeSourceLocus (p := p))
  have hSnonempty : S.Nonempty := by
    refine ⟨⟨0,by simp [realTypeSourceLocus]⟩,?_⟩
    exact sourcePsiGapSolvable_zero hp hp1 n
  have hSuniv : S = univ :=
    (show IsClopen S from ⟨hSclosed,hSopen⟩).eq_univ hSnonempty
  have hx : (⟨φ,hφ⟩ : realTypeSourceLocus p) ∈ S := by
    rw [hSuniv]
    trivial
  exact hx

end NLS.ZakharovShabat
