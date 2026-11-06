import NLS.ZakharovShabat.SourceOpenActionExtension
import NLS.ZakharovShabat.SourceLaurentActionIsospectral
import NLS.MKdV.MiuraActionLevelExtension

/-! # The physical mKdV actions as analytic NLS action functions

All original NLS actions are assembled in complex ℓ¹. Every positive
physical Hill action, and indeed every integer Laurent level, is an
analytic function on an open ℓ¹ neighborhood of the action image of the
entire real L2 diagonal. Agreement with the independently constructed
physical contour is proved at every original real H1 source.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
local instance : (2 : ℝ≥0∞).HolderTriple 2 1 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])

/-- The ℓ¹ map consists of the original NLS spectral actions. Each
integer mKdV action level has a holomorphic factor, hence a real analytic
factor, including at zero mean and every collapsed gap. The action-space
neighborhood may depend on the chosen index and level. -/
theorem exists_miuraActionLevel_action_extensions :
    ∃ I : CoeffPair 2 → Coeff 1, ∃ U : Set (CoeffPair 2),
      IsOpen U ∧ realTypeSourceLocus 2 ⊆ U ∧ AnalyticOnNhd ℂ I U ∧
      (∀ ψ ∈ U, ∀ m : ℤ, I ψ m = sourceComplexAction (by simp) (by norm_num) m ψ) ∧
      (∀ (a : ScalarDomain 2) (_ha : ∀ j, a.val j = conj (a.val (-j))),
        ∀ m : ℤ, I (sobolevSourceInclusion (a,a)) m = miuraNLSAction a m) ∧
      ∀ (n : ℕ), 1 ≤ n → ∀ k : ℤ, ∃ V : Set (Coeff 1), ∃ G : Coeff 1 → ℂ,
        IsOpen V ∧ (∀ ψ ∈ realDiagonalSourceLocus 2, I ψ ∈ V) ∧
          AnalyticOnNhd ℂ G V ∧ AnalyticOnNhd ℝ G V ∧
          ∀ (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))),
            G (I (sobolevSourceInclusion (a,a))) = miuraMKdVActionLevel a ha n k := by
  obtain ⟨W₀,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (p := 2) (by simp) (by norm_num)
  let I := sourceActionSequence (q := 1) (by simp) (by norm_num) t
  refine ⟨I,X,D.source_open,D.real_subset,D.actionSequence_analytic,D.actionSequence_apply,?_,?_⟩
  · intro a ha m
    let ψ := realDiagonalH1Source a ha
    change I ψ.val m = _
    rw [D.actionSequence_apply ψ.val (D.real_subset ψ.property),
      sourceComplexAction_eq_sourceRealAction _ _ m ψ.val ψ.property]
    exact (sourceIndexedAction_eq_sourceRealAction _ _ m ψ.val ψ.property).symm
  · intro n hn k
    obtain ⟨V,F,hV,hcenters,_,_,hF,hrec,_⟩ := D.exists_scalar_action_extension_on (q := 1)
      (sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2))
      (isOpen_sourceDiagonalLaurentDomain _ _)
      (analyticOnNhd_sourceDiagonalLaurentAction _ _ n (2*k-2) (by omega))
      (fun a b ha hb hab => sourceDiagonalLaurentAction_real_eq_of_actions
        _ _ a b ha hb hab n (2*k-2) (by omega))
    let G : Coeff 1 → ℂ := fun b => (1/2 : ℂ)*F b
    have hG : AnalyticOnNhd ℂ G V := fun b hb => analyticAt_const.mul (hF b hb)
    refine ⟨V,G,hV,?_,hG,hG.restrictScalars,?_⟩
    · intro ψ hψ
      exact hcenters ⟨ψ,hψ.1⟩ (realDiagonal_subset_sourceDiagonalLaurentDomain _ _ hψ)
    · intro a ha
      have he := hrec (realDiagonalH1Source a ha) (realDiagonalH1Source_mem_LaurentDomain a ha)
      change F (I (sobolevSourceInclusion (a,a))) =
        sourceDiagonalLaurentAction (by simp) (by norm_num) n (2*k-2)
          (sobolevSourceInclusion (a,a)) at he
      change (1/2 : ℂ)*F (I (sobolevSourceInclusion (a,a))) = _
      rw [he,sourceDiagonalLaurentAction_eq_two_miuraActionLevel a ha n hn k]
      ring

end NLS.MKdV
