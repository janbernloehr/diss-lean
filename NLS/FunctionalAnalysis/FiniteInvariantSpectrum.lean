import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Finite invariant subspaces of operators on possibly infinite-dimensional spaces. -/
noncomputable section
namespace NLS.FunctionalAnalysis
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- Only the invariant subspace, rather than the ambient space, needs to be finite dimensional. -/
theorem eq_iSup_inf_genEigenspace_of_finite (T : Module.End ℂ E)
    (W : Submodule ℂ E) [FiniteDimensional ℂ W]
    (hW : ∀ x ∈ W, T x ∈ W) : W = ⨆ μ : ℂ, W ⊓ T.genEigenspace μ ⊤ := by
  let S : Module.End ℂ W := T.restrict hW
  have hS := Module.End.iSup_maxGenEigenspace_eq_top S
  calc
    W = (⊤ : Submodule ℂ W).map W.subtype := (Submodule.map_subtype_top W).symm
    _ = (⨆ μ : ℂ, S.maxGenEigenspace μ).map W.subtype := by rw [hS]
    _ = _ := by
      rw [Submodule.map_iSup]
      apply iSup_congr
      intro μ
      exact (Submodule.inf_genEigenspace T W hW).symm

/-- An injective operator has no generalized vectors at zero, at any chain length. -/
theorem genEigenspace_zero_eq_bot_of_injective (T : Module.End ℂ E)
    (hT : Function.Injective T) : T.genEigenspace 0 ⊤ = ⊥ := by
  rw [Module.End.genEigenspace_top]
  apply le_antisymm _ bot_le
  apply iSup_le
  intro n
  rw [Module.End.genEigenspace_zero_nat]
  exact le_of_eq (LinearMap.ker_eq_bot.mpr (by
    simpa only [Module.End.coe_pow] using hT.iterate n))

/-- Dimensions add in every finite independent family, even in an infinite ambient space. -/
theorem finrank_finset_sup_of_iSupIndep {ι : Type*} (V : ι → Submodule ℂ E)
    (hV : iSupIndep V) [∀ i, FiniteDimensional ℂ (V i)] (s : Finset ι) :
    Module.finrank ℂ (s.sup V : Submodule ℂ E) = ∑ i ∈ s, Module.finrank ℂ (V i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    have hd : V i ⊓ s.sup V = ⊥ := by
      rw [Finset.sup_eq_iSup]
      exact (hV.disjoint_biSup (show i ∉ (s : Set ι) from hi)).eq_bot
    have he := Submodule.finrank_sup_add_finrank_inf_eq (V i) (s.sup V)
    rw [hd,finrank_bot,add_zero] at he
    rw [he,ih]

/-- Finite independent spectral families have their literal sum of dimensions. -/
theorem finrank_iSup_of_iSupIndep {ι : Type*} [Fintype ι] (V : ι → Submodule ℂ E)
    (hV : iSupIndep V) [∀ i, FiniteDimensional ℂ (V i)] :
    Module.finrank ℂ (⨆ i, V i : Submodule ℂ E) = ∑ i, Module.finrank ℂ (V i) := by
  have h := finrank_finset_sup_of_iSupIndep V hV Finset.univ
  have hs : Finset.univ.sup V = ⨆ i, V i := by
    simp only [Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos]
  rw [hs] at h
  exact h

end NLS.FunctionalAnalysis
