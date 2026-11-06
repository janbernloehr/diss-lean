import NLS.Articles.MKdVBelowL2.PhysicalBirkhoffCanonical
import NLS.ZakharovShabat.PhysicalPoissonBracket
import NLS.Articles.MKdVBelowL2.CompatibleBirkhoffFamily
import NLS.ZakharovShabat.PhysicalBirkhoffIntrinsicProperties

/-! # The p=2 family member is the accepted intrinsic physical map

The interval L² realization retains every original period-one distribution
coefficient. The Birkhoff comparison includes the rectangular-to-complex
normalization and therefore does not merely assert existence of an inverse. -/
noncomputable section
set_option autoImplicit false
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Fourier.SmoothPeriodicTest

/-- The physical Hilbert function represented by the original real-type distributions. -/
def physicalHilbertRealization (u : PhysicalRealInput 2) : physicalRealSubmodule :=
  realSourcePhysicalL2Equiv (physicalRealCoefficientsCL u)

@[simp] theorem physicalHilbertRealization_val (u : PhysicalRealInput 2) :
    (physicalHilbertRealization u).val = sourcePhysicalL2Equiv (physicalCoefficients u.val) := by
  change sourcePhysicalL2Equiv (physicalRealCoefficientsCL u).val = _
  rw [physicalRealCoefficientsCL_val]

/-- The realization has the exact Fourier coefficients of each input distribution. -/
theorem physicalHilbertRealization_coefficients (u : PhysicalRealInput 2) (n : ℤ) :
    NLS.Fourier.intervalFourierCoefficient 1 (physicalHilbertRealization u).val.ofLp.1 n =
      u.val.1.val (mode (-n)) ∧
    NLS.Fourier.intervalFourierCoefficient 1 (physicalHilbertRealization u).val.ofLp.2 n =
      u.val.2.val (mode (-n)) := by
  rw [physicalHilbertRealization_val,sourcePhysicalL2Equiv_apply]
  have h := sourcePhysicalL2_coefficients (physicalCoefficients u.val) n
  exact ⟨h.1.trans (physicalCoefficients_apply u.val n).1,
    h.2.trans (physicalCoefficients_apply u.val n).2⟩

/-- The chosen p=2 map equals the accepted action-angle construction in complex coordinates. -/
theorem compatibleBirkhoff_eq_intrinsic (u : PhysicalRealInput 2) :
    compatibleBirkhoff (by simp) (by norm_num) u.val =
      Birkhoff.rectangularToComplex
        (CoeffPair.toMax 2 (physicalRealTargetComplex
          (intrinsicPhysicalBirkhoffMap (physicalHilbertRealization u)))) := by
  have h := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.intrinsicPhysicalBirkhoffMap_complex (physicalHilbertRealization u)
  rw [h]
  unfold compatibleBirkhoff physicalBirkhoff physicalBirkhoffMap
  rw [physicalHilbertRealization_val,LinearIsometryEquiv.symm_apply_apply]
  rfl
/-- Complex Hilbert realization of both original distribution inputs. -/
def physicalHilbertPairEquiv : (PhysicalFL 2 × PhysicalFL 2) ≃L[ℂ] IntervalPairL2 :=
  (physicalCoefficients (p := 2)).trans sourcePhysicalL2Equiv.toContinuousLinearEquiv

/-- The Fourier-defined physical bracket is exactly the established integral bracket at p=2. -/
theorem physicalFLBracket_eq_integral_bracket
    (F G : IntervalPairL2 → ℂ) (u : PhysicalFL 2 × PhysicalFL 2)
    (hF : DifferentiableAt ℂ F (physicalHilbertPairEquiv u))
    (hG : DifferentiableAt ℂ G (physicalHilbertPairEquiv u)) :
    physicalFLBracket le_rfl (F ∘ physicalHilbertPairEquiv) (G ∘ physicalHilbertPairEquiv) u =
      physicalBracket F G (physicalHilbertPairEquiv u) := by
  rw [physicalBracket_eq_source F G _ hF hG]
  have he (f : IntervalPairL2 → ℂ) :
      (f ∘ physicalHilbertPairEquiv) ∘ (physicalCoefficients (p := 2)).symm =
        f ∘ sourcePhysicalL2 := by
    funext a
    simp only [Function.comp_apply,physicalHilbertPairEquiv,ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg f (sourcePhysicalL2Equiv_apply a)
  unfold physicalFLBracket
  rw [he F,he G]
  congr 1
  exact (sourcePhysicalL2Equiv.symm_apply_apply (physicalCoefficients u)).symm

end NLS.Articles.MKdVBelowL2
