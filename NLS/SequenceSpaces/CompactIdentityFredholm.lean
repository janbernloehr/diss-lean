import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Complex.Basic

/-!
# Fredholm alternative for a compact perturbation of the identity

The injectivity argument in Lemma 12.7 is separate from the compact
decomposition in Lemma 12.6. This operator lemma isolates the final
Fredholm step: once the kernel of `1 - T` is zero for compact `T`,
the operator is bijective.
-/

noncomputable section
namespace NLS.Coeff

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [CompleteSpace X]

theorem bijective_id_sub_compact_of_injective
    (T : X →L[ℂ] X) (hT : IsCompactOperator T)
    (hinj : Function.Injective ((1 : X →L[ℂ] X) - T)) :
    Function.Bijective ((1 : X →L[ℂ] X) - T) := by
  have hnotEigen : ¬ Module.End.HasEigenvalue (T : Module.End ℂ X) 1 := by
    intro heigen
    obtain ⟨v,hv⟩ := heigen.exists_hasEigenvector
    have hTv : T v = v := by
      simpa using hv.apply_eq_smul
    have hvker : ((1 : X →L[ℂ] X) - T) v = 0 := by
      simp [hTv]
    have hvzero : v = 0 := hinj (by simpa using hvker)
    exact hv.2 hvzero
  have hres : (1 : ℂ) ∈ resolventSet ℂ T :=
    (hT.hasEigenvalue_or_mem_resolventSet (by norm_num)).resolve_left hnotEigen
  have hunit : IsUnit ((1 : X →L[ℂ] X) - T) := by
    simpa using (spectrum.mem_resolventSet_iff.mp hres)
  exact ContinuousLinearMap.isUnit_iff_bijective.mp hunit

/-- The operator form of the last step in Corollary 12.8: a compact
perturbation of an invertible diagonal is invertible once its kernel
vanishes. -/
theorem bijective_add_compact_of_bijective_of_injective
    (D K : X →L[ℂ] X)
    (hD : Function.Bijective D) (hK : IsCompactOperator K)
    (hinj : Function.Injective (D + K)) :
    Function.Bijective (D + K) := by
  have hDu : IsUnit D := ContinuousLinearMap.isUnit_iff_bijective.mpr hD
  obtain ⟨U, rfl⟩ := hDu
  let T : X →L[ℂ] X := -((↑(U⁻¹) : X →L[ℂ] X) * K)
  have hT : IsCompactOperator T := by
    have hc : IsCompactOperator (fun x : X => (↑(U⁻¹) : X →L[ℂ] X) (K x)) :=
      hK.clm_comp (↑(U⁻¹) : X →L[ℂ] X)
    change IsCompactOperator (fun x : X => -((↑(U⁻¹) : X →L[ℂ] X) (K x)))
    exact hc.neg
  have hfactor : (↑U : X →L[ℂ] X) * ((1 : X →L[ℂ] X) - T) = ↑U + K := by
    dsimp [T]
    rw [mul_sub, mul_one, mul_neg, ← mul_assoc]
    simp
  have hinjT : Function.Injective ((1 : X →L[ℂ] X) - T) := by
    intro x y hxy
    apply hinj
    rw [← hfactor]
    exact congrArg (U : X →L[ℂ] X) hxy
  have hbijT := bijective_id_sub_compact_of_injective T hT hinjT
  rw [← hfactor]
  exact hD.comp hbijT

end NLS.Coeff
