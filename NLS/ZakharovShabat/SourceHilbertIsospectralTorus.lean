import NLS.SequenceSpaces.RealActionTorusProduct
import NLS.ZakharovShabat.SourceBirkhoffLemma17_5

/-! # Actual Hilbert isospectral tori as products of circles

Restricting the original Birkhoff homeomorphism and then taking coordinate
phases identifies each real Hilbert isospectral set with a product of one
circle for each actual noncollapsed periodic gap. No finite-gap hypothesis
is needed; finite open-gap sets give the corresponding finite torus.
-/
noncomputable section
open Set
namespace NLS.ZakharovShabat
/-- Integer labels of the actual open periodic gaps of a real Hilbert source. -/
def sourceHilbertOpenGapIndex (φ : realTypeSourceSubmodule 2) :=
  {n : ℤ // sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n ≠ 0}

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The original Hilbert homeomorphism restricts to the entire actual isospectral torus. -/
def hilbertIsospectralHomeomorphActionTorus
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceIsospectralSet (by simp) φ ≃ₜ
      RealCoeff.actionTorus 2 (RealCoeff.pairAction (D.hilbertRealHomeomorph φ)) := by
  have he : D.hilbertRealHomeomorph '' sourceIsospectralSet (by simp) φ =
      RealCoeff.actionTorus 2 (RealCoeff.pairAction (D.hilbertRealHomeomorph φ)) := by
    change sourceRealBirkhoffMap (by simp) (by norm_num) s '' sourceIsospectralSet (by simp) φ = _
    rw [D.image_isospectralSet_eq_actionTorus (le_refl 2) φ]
    congr 1
    funext n
    exact (D.hilbert_pairAction_eq φ n).symm
  exact (D.hilbertRealHomeomorph.image _).trans (Homeomorph.setCongr he)

/-- Nonzero coordinate actions are exactly the actual open periodic gaps. -/
theorem hilbert_pairAction_ne_zero_iff_open_gap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    RealCoeff.pairAction (D.hilbertRealHomeomorph φ) n ≠ 0 ↔
      sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n ≠ 0 := by
  apply not_congr
  have hc := D.real_coordinates_zero_iff_gap_zero φ n
  change ((D.hilbertRealHomeomorph φ).1 n = 0 ∧
    (D.hilbertRealHomeomorph φ).2 n = 0) ↔ _ at hc
  rw [← hc]
  constructor
  · intro h
    exact RealCoeff.coordinates_zero_of_mem_actionTorus
      (RealCoeff.mem_actionTorus_self (D.hilbertRealHomeomorph φ)) n h
  · rintro ⟨hx,hy⟩
    simp only [RealCoeff.pairAction,hx,hy,zero_pow (by norm_num : 2 ≠ 0),zero_add,zero_div]

/-- The actual isospectral set is homeomorphic to one unit circle per open periodic gap. -/
def hilbertIsospectralHomeomorphCircles
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) :
    sourceIsospectralSet (by simp) φ ≃ₜ
      (sourceHilbertOpenGapIndex φ → Circle) := by
  let e : {n : ℤ // RealCoeff.pairAction (D.hilbertRealHomeomorph φ) n ≠ 0} ≃
      sourceHilbertOpenGapIndex φ :=
    Equiv.subtypeEquivRight (fun n => D.hilbert_pairAction_ne_zero_iff_open_gap φ n)
  exact ((D.hilbertIsospectralHomeomorphActionTorus φ).trans
    (RealCoeff.actionTorusHomeomorphCircles (by simp) (D.hilbertRealHomeomorph φ))).trans
      (Homeomorph.piCongrLeft (Y := fun _ => Circle) e)

/-- A finite open-gap index set gives a torus with exactly that many circle factors. -/
def hilbertIsospectralHomeomorphFiniteTorus
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2)
    [Fintype (sourceHilbertOpenGapIndex φ)] :
    sourceIsospectralSet (by simp) φ ≃ₜ
      (Fin (Fintype.card (sourceHilbertOpenGapIndex φ)) → Circle) :=
  (D.hilbertIsospectralHomeomorphCircles φ).trans
    (Homeomorph.piCongrLeft (Y := fun _ => Circle) (Fintype.equivFin _))

end SourceBirkhoffMapComplexData

/-- The circle-product description constructs its Birkhoff family internally. -/
theorem sourceHilbertIsospectralSet_homeomorphic_circles (φ : realTypeSourceSubmodule 2) :
    Nonempty (sourceIsospectralSet (by simp) φ ≃ₜ
      (sourceHilbertOpenGapIndex φ → Circle)) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  exact ⟨D.hilbertIsospectralHomeomorphCircles φ⟩

/-- An actual finite-gap source has precisely as many circle factors as its open-gap labels. -/
theorem sourceHilbertIsospectralSet_homeomorphic_finiteTorus (φ : realTypeSourceSubmodule 2)
    (hφ : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    Nonempty (sourceIsospectralSet (by simp) φ ≃ₜ
      (Fin (Nat.card (sourceHilbertOpenGapIndex φ)) → Circle)) := by
  have hf : {n : ℤ | sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n ≠ 0}.Finite := by
    change {n : ℤ | canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0}.Finite at hφ
    simpa only [sourcePeriodicGapDisplacement_apply] using hφ
  let : Fintype (sourceHilbertOpenGapIndex φ) := hf.fintype
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  rw [Nat.card_eq_fintype_card]
  exact ⟨D.hilbertIsospectralHomeomorphFiniteTorus φ⟩

end NLS.ZakharovShabat
