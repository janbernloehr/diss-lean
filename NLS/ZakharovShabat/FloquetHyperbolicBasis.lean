import NLS.ZakharovShabat.FloquetHyperbolicRoots
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Stable and unstable eigenbases of hyperbolic unimodular monodromy -/
noncomputable section
set_option autoImplicit false
open Complex Matrix Module
namespace NLS.ZakharovShabat

/-- Distinct characteristic roots of a two-dimensional matrix provide a
basis of actual nonzero eigenvectors. -/
theorem exists_eigenbasis_of_distinct_characteristic_roots
    (M : Matrix (Fin 2) (Fin 2) ℂ) (μ ν : ℂ) (hne : μ ≠ ν)
    (hμ : (M-μ • 1).det = 0) (hν : (M-ν • 1).det = 0) :
    ∃ b : Basis (Fin 2) ℂ (Fin 2 → ℂ),
      M *ᵥ b 0 = μ • b 0 ∧ M *ᵥ b 1 = ν • b 1 := by
  obtain ⟨v,hv0,hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hμ
  obtain ⟨w,hw0,hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hν
  simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero] at hv hw
  have hi : Function.Injective ![μ,ν] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hl : LinearIndependent ℂ ![v,w] :=
    Module.End.eigenvectors_linearIndependent' M.mulVecLin ![μ,ν] hi ![v,w] (by
      intro i
      fin_cases i
      · exact ⟨Module.End.mem_eigenspace_iff.mpr hv,hv0⟩
      · exact ⟨Module.End.mem_eigenspace_iff.mpr hw,hw0⟩)
  let b := basisOfLinearIndependentOfCardEqFinrank hl (by simp)
  refine ⟨b,?_,?_⟩
  · simpa only [b,coe_basisOfLinearIndependentOfCardEqFinrank,Matrix.cons_val_zero] using hv
  · simpa only [b,coe_basisOfLinearIndependentOfCardEqFinrank,Matrix.cons_val_one,
      Matrix.cons_val_zero] using hw

/-- Hyperbolic unimodular monodromy has a basis ordered by stable and
unstable directions, with reciprocal nonzero multipliers. -/
theorem exists_stable_unstable_eigenbasis
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1)
    (hunit : ¬ ∃ μ : ℂ, ‖μ‖ = 1 ∧ (M-μ • 1).det = 0) :
    ∃ (μ ν : ℂ) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ)),
      μ * ν = 1 ∧ 0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧
      M *ᵥ b 0 = μ • b 0 ∧ M *ᵥ b 1 = ν • b 1 := by
  obtain ⟨μ,ν,hmul,hμ0,hμ,hν,hrμ,hrν⟩ := exists_stable_unstable_characteristic_roots M hM hunit
  have hne : μ ≠ ν := by intro he; rw [he] at hμ; linarith
  obtain ⟨b,hb⟩ := exists_eigenbasis_of_distinct_characteristic_roots M μ ν hne hrμ hrν
  exact ⟨μ,ν,b,hmul,hμ0,hμ,hν,hb⟩

end NLS.ZakharovShabat
