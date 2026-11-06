import NLS.KdV.PseudomeasureMultiplicityOrder
import NLS.KdV.SingularHillAlgebraicMultiplicity

/-! # Exact free algebraic multiplicities in the full original Hill domain -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem endpointReducedFamily_zero (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (z : ℂ) :
    endpointReducedFamily r hr hr1 n (0,z) = (z-(freeHillValue n : ℂ)) • ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  simp only [endpointReducedFamily,endpointEffectiveFamily,endpointModePotentialFamily,
    map_zero,ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,sub_zero]

theorem endpointReducedDeterminant_zero (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ) (z : ℂ) :
    endpointReducedDeterminant r hr hr1 n (0,z) = (z-(freeHillValue n : ℂ))^2 := by
  rw [endpointReducedDeterminant,endpointReducedFamily_zero]
  change LinearMap.det ((z-(freeHillValue n : ℂ)) • (LinearMap.id : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ))) = _
  rw [LinearMap.det_smul]
  norm_num

theorem singularHillAlgebraicMultiplicity_zero_positive (n : ℕ) (hn : 1 ≤ n) :
    singularHillAlgebraicMultiplicity (0 : FourierLebesgueSpace (2 : ℝ) (-1) 2) (freeHillValue n : ℂ) = 2 := by
  have hs : endpointHillConstant 0*(n : ℝ)^((0 : ℝ)-1/2)*
      ‖(0 : WeightedCoeff (SpectralWeight.one.negativeSobolev 0) ⊤)‖ ≤ 1/2 := by simp
  have hz : (freeHillValue n : ℂ) ∈ reducedHillStrip n := by simp [reducedHillStrip]
  have h := endpointHillAlgebraicMultiplicity_eq_analyticOrderNatAt 0 (by norm_num) (by norm_num) n hn 0 hs
    (freeHillValue n : ℂ) hz
  rw [← singularHillAlgebraicMultiplicity_endpoint,map_zero] at h
  have he : (fun z => endpointReducedDeterminant 0 (by norm_num) (by norm_num) n (0,z)) =
      (fun z : ℂ => (z-(freeHillValue n : ℂ))^2) := funext (endpointReducedDeterminant_zero _ _ _ _)
  rw [he] at h
  refine h.trans ?_
  have ho := analyticOrderNatAt_pow (f := fun z : ℂ => z-(freeHillValue n : ℂ))
    (z₀ := (freeHillValue n : ℂ)) (by fun_prop) 2
  simpa only [analyticOrderNatAt,analyticOrderAt_id_sub_const_self,ENat.toNat_one,nsmul_eq_mul,mul_one] using! ho

end NLS.KdV
