import NLS.SequenceSpaces.RealActionTorusConnected
import NLS.ZakharovShabat.SourceBirkhoffLemma17_5
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Connectedness of the actual real Hilbert isospectral sets

The original real Hilbert Birkhoff homeomorphism sends the actual
isospectral set, with all algebraic multiplicities, onto a complete
coordinate action torus. Connectedness transfers through that
homeomorphism, with no finite-gap assumption.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat
namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The actual Hilbert isospectral set is connected, also for infinitely many open gaps. -/
theorem isConnected_hilbertIsospectralSet
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    IsConnected (sourceIsospectralSet (by simp) φ) := by
  apply D.hilbertRealHomeomorph.isConnected_image.mp
  change IsConnected (sourceRealBirkhoffMap (by simp) (by norm_num) s ''
    sourceIsospectralSet (by simp) φ)
  rw [D.image_isospectralSet_eq_actionTorus (le_refl 2) φ]
  have he : (fun n => (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) =
      RealCoeff.pairAction (D.hilbertRealHomeomorph φ) :=
    funext (fun n => (D.hilbert_pairAction_eq φ n).symm)
  rw [he]
  exact RealCoeff.isConnected_actionTorus_self (by simp) _

end SourceBirkhoffMapComplexData

/-- The compactness and connectedness assertions in the real Hilbert overview on p.45. -/
theorem sourceHilbertIsospectralSet_compact_connected (φ : realTypeSourceSubmodule 2) :
    IsCompact (sourceIsospectralSet (by simp) φ) ∧
      IsConnected (sourceIsospectralSet (by simp) φ) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨D.isCompact_isospectralSet (le_refl 2) φ,D.isConnected_hilbertIsospectralSet φ⟩

end NLS.ZakharovShabat
