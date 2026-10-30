import NLS.ZakharovShabat.SourcePsiDeletedIndexEquation

/-!
# Real values of the literal deleted-index equation

Restriction and zero extension preserve real coefficient sequences.
The original real-data theorem therefore applies on the literal spaces
without any root-placement condition.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real source data and real retained inputs give real literal-index equation coordinates. -/
theorem SourceLemma12_4Data.deletedIndexEquation_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ)
    (a : DeletedIndexCoeff p n) (ha : ∀ k, (a k).im = 0)
    (m : {m : ℤ // m ≠ n}) :
    (sourcePsiDeletedIndexEquation hp hp1 n ψ a m).im = 0 := by
  rw [sourcePsiDeletedIndexEquation,DeletedCoeff.indexEquiv_apply]
  apply H.real ψ hψ hreal n _ ?_ m.val
  intro k
  by_cases hk : k = n
  · subst k
    have hn : (((DeletedCoeff.indexEquiv hp n).symm a : DeletedCoeff p n) : Coeff p) n = 0 :=
      ((DeletedCoeff.indexEquiv hp n).symm a).property
    rw [hn]
    rfl
  · rw [DeletedCoeff.indexEquiv_symm_apply_other hp n k hk]
    exact ha ⟨k,hk⟩

end NLS.ZakharovShabat
