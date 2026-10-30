import NLS.ZakharovShabat.SourceCorollary12_8
import NLS.ZakharovShabat.SourcePsiDeletedIndexJacobian

/-!
# Injectivity and the inverse on literal retained indices

The original real-domain injectivity and bounded inverse of the actual
root Jacobian transfer through the exact deleted-index equivalence.
The full root input before omission and original source neighborhood are
preserved, and the isomorphism equals the actual Frechet derivative.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Jacobian is injective on the literal retained-index space. -/
theorem SourceLemma12_7Data.deletedIndexInjective
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_7Data hp hp1 W)
    {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V discs c)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (htΩ : t ∈ sourcePsiOriginalOmega V discs) (n : ℤ) :
    Function.Injective (sourcePsiDeletedIndexRootJacobian hp hp1 n t.1
      (DeletedCoeff.indexEquiv hp n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2)))) := by
  rw [H.previous.previous.previous.deletedIndexRootJacobian_eq t.1 htW n,
    (DeletedCoeff.indexEquiv hp n).symm_apply_apply]
  exact (DeletedCoeff.indexEquiv hp n).injective.comp
    ((H.injective hD t htW htΩ n).comp (DeletedCoeff.indexEquiv hp n).symm.injective)

/-- The original isomorphism represents exactly the derivative on literal retained indices. -/
theorem SourceCorollary12_8Data.deletedIndexIsomorphism
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary12_8Data hp hp1 W)
    {V : Set (CoeffPair p)} {discs : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V discs c) (hV : IsOpen V)
    (t : realTypeSourceSubmodule p × RealCoeff p) (htW : (t.1:CoeffPair p) ∈ W)
    (htΩ : t ∈ sourcePsiOriginalOmega V discs) (n : ℤ) :
    ∃ e : DeletedIndexCoeff p n ≃L[ℂ] DeletedIndexCoeff p n,
      e.toContinuousLinearMap = sourcePsiDeletedIndexRootJacobian hp hp1 n t.1
        (DeletedCoeff.indexEquiv hp n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2))) := by
  obtain ⟨D,_,hD',_,_⟩ := H.isomorphism hD hV t htW htΩ n
  let e := (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv
  refine ⟨(e.symm.trans D).trans e,?_⟩
  rw [H.previous.previous.previous.previous.deletedIndexRootJacobian_eq t.1 htW n,
    (DeletedCoeff.indexEquiv hp n).symm_apply_apply,← hD']
  rfl

end NLS.ZakharovShabat
