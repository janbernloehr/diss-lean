import NLS.ZakharovShabat.SourceActionFiniteGapDifferential
import NLS.ZakharovShabat.SourceHamiltonianActionExtension
import NLS.ZakharovShabat.SourceHamiltonianRealGradient

/-! # The actual renormalized Hamiltonian differential at finite gap

The constructed action extension and real-form analytic uniqueness identify
the original source Hamiltonian germ. Its full complex differential is a
finite sum of action differentials weighted by the actual renormalized
frequencies. No auxiliary action Hamiltonian or Birkhoff family is assumed.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W Y P : Set (CoeffPair 4)} {u : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}

/-- The original FL⁴ Hamiltonian differential is the finite physical frequency pairing. -/
theorem renormalizedHamiltonian_fderiv_eq_finite_sum
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P u)
    (hP : IsOpen P) (hr : realTypeSourceLocus 4 ⊆ P)
    (φ : realTypeSourceSubmodule 4) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val = 0)
    (h : CoeffPair 4) :
    fderiv ℂ A.renormalizedHamiltonian φ.val h =
      ∑ n ∈ S, C.renormalizedFrequency n φ.val *
        ((fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val) h) := by
  obtain ⟨W₀,B,X,t,D,V,H,_,hcenter,_,_,_,hH,hrec,_,_⟩ := A.exists_hamiltonian_action_extension
  obtain ⟨U,_,_,hreal,_,hA,_,_⟩ := A.exists_renormalizedHamiltonian_analytic
  have he : (fun ψ => H (sourceActionSequence (q := 2) (by simp) (by norm_num) t ψ)) =ᶠ[𝓝 φ.val]
      A.renormalizedHamiltonian := by
    apply eventuallyEq_source_of_analyticAt_of_real_agreement (by simp) φ
    · exact (hH _ (hcenter φ)).comp (D.actionSequence_analytic φ.val (D.real_subset φ.property))
    · exact hA φ.val (hreal φ.property)
    · exact hrec
  rw [← he.fderiv_eq,D.fderiv_comp_actionSequence_eq_finite_sum φ S hS H
    (hH _ (hcenter φ)).differentiableAt h]
  apply Finset.sum_congr rfl
  intro n _
  rw [sourceHamiltonian_fderiv_real A D C hs hP hr H V hH hcenter hrec φ n]

/-- Every actual finite-gap FL⁴ source admits one finite formula for the full cotangent. -/
theorem exists_renormalizedHamiltonian_finiteGap_differential
    (A : SourcePrimitivePowerAtlas (by simp) (by norm_num) W)
    (C : SourceAbelianMomentAtlas (by simp) (by norm_num) Y u)
    (hs : SourcePsiSquaredGapComplexExtension (by simp) (by norm_num) P u)
    (hP : IsOpen P) (hr : realTypeSourceLocus 4 ⊆ P)
    (φ : realTypeSourceSubmodule 4) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ S : Finset ℤ, fderiv ℂ A.renormalizedHamiltonian φ.val =
      ∑ n ∈ S, C.renormalizedFrequency n φ.val •
        fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val := by
  obtain ⟨S,hS⟩ := exists_sourceComplexAction_fderiv_support (by simp) (by norm_num) φ hf
  refine ⟨S,?_⟩
  apply ContinuousLinearMap.ext
  intro h
  rw [A.renormalizedHamiltonian_fderiv_eq_finite_sum C hs hP hr φ S hS h]
  simp

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
