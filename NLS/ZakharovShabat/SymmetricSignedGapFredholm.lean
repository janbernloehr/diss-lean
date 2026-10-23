import NLS.ZakharovShabat.SymmetricSignedGapCompactDerivative
import NLS.FunctionalAnalysis.CompactScalarPerturbation

/-! # Finite-dimensional obstruction to signed-gap local inversion

Every actual symmetric Hilbert signed-gap derivative has finite-dimensional
kernel. The compact-operator alternative makes injectivity sufficient for a
bounded inverse; injectivity at every source would imply global openness.
The kernel-vanishing hypothesis remains explicit throughout.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Only a finite-dimensional kernel can obstruct the actual signed-gap derivative. -/
theorem finiteDimensional_ker_fderiv_symmetricSourceSignedGapMap (a : RealCoeff 2) :
    FiniteDimensional ℝ
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a).ker := by
  exact CompactScalarPerturbation.finiteDimensional_ker _ (c := (2 : ℝ)) (by norm_num)
    (isCompactOperator_fderiv_symmetricSourceSignedGapMap_sub_two_id a)

/-- For each actual symmetric source, injectivity of its signed-gap derivative already
implies bijectivity; the premise still has to be proved away from zero. -/
theorem bijective_fderiv_symmetricSourceSignedGapMap_iff_injective (a : RealCoeff 2) :
    Function.Bijective (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a) ↔
      Function.Injective (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a) := by
  refine ⟨fun h => h.1,fun h => ?_⟩
  exact CompactScalarPerturbation.bijective_of_injective _ (c := (2 : ℝ)) (by norm_num)
    (isCompactOperator_fderiv_symmetricSourceSignedGapMap_sub_two_id a) h

/-- An injective actual signed-gap derivative has a bounded two-sided linear inverse. -/
theorem exists_equiv_fderiv_symmetricSourceSignedGapMap_of_injective
    (a : RealCoeff 2)
    (ha : Function.Injective
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a)) :
    ∃ e : RealCoeff 2 ≃L[ℝ] RealCoeff 2,
      e.toContinuousLinearMap =
        fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a := by
  have hb := (bijective_fderiv_symmetricSourceSignedGapMap_iff_injective a).mpr ha
  exact ⟨ContinuousLinearEquiv.ofBijective _
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

/-- Global openness reduces to injectivity of the actual derivative at each symmetric source. -/
theorem isOpenMap_symmetricSourceSignedGapMap_of_derivative_injective
    (h : ∀ a : RealCoeff 2, Function.Injective
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a)) :
    IsOpenMap (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) := by
  choose e he using fun a => exists_equiv_fderiv_symmetricSourceSignedGapMap_of_injective a (h a)
  apply isOpenMap_of_hasStrictFDerivAt_equiv (f' := e)
  intro a
  have hs := (analyticAt_symmetricSourceSignedGapMap (p := 2)
    (by simp) (by norm_num) a).contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  rw [← he a] at hs
  exact hs

end NLS.ZakharovShabat
