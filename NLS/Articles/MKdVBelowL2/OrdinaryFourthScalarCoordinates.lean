import NLS.Articles.MKdVBelowL2.OrdinaryFourthClassicalMKdV
import NLS.Articles.MKdVBelowL2.FixedTimeFourthCoordinateObstruction

/-! # Original physical coordinates of the mass-restored native fourth flow

The scalar physical input and the Hilbert source have the same original
distributions. Compatibility of the fixed Birkhoff family transfers the
actual Hilbert coordinate evolution into every larger finite exponent.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual physical scalar coordinate is the unchanged Hilbert coordinate. -/
theorem compatibleBirkhoff_fourthClassicalScalarInput (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p)
    (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd) (n : ℤ) :
    (compatibleBirkhoff hp hp1 (physicalScalarPairCLM (fourthClassicalScalarInput h2p a ha)).val).1 n =
      (sourceComplexBirkhoffMap (p := 2) (by simp) (by norm_num)
        (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).roots (originalWeightedRealSource _ a).val).1 n := by
  let v : PhysicalRealInput 2 := fourthClassicalPhysicalInput a
  let w : PhysicalRealInput p := physicalScalarPairCLM (fourthClassicalScalarInput h2p a ha)
  have he : realTypeSourceExponentInclusion h2p (physicalRealCoefficientsCL v) = physicalRealCoefficientsCL w := by
    change realTypeSourceExponentInclusion h2p
      (physicalRealCoefficientsCL (physicalRealCoefficientsCL.symm (originalWeightedRealSource _ a))) = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change fourthClassicalSourceAtExponent h2p a = physicalRealCoefficientsCL w
    rw [show w = physicalRealCoefficientsCL.symm (fourthClassicalSourceAtExponent h2p a) from
      fourthClassicalScalarInput_pair h2p a ha,ContinuousLinearEquiv.apply_symm_apply]
  have hsame := same_distributions_of_physicalRealCoefficients_exponent h2p v w he
  have hc := (compatibleBirkhoff_coordinates_on_intersection (p := 2) (by simp) (by norm_num) hp hp1
    v.val w.val ((compatibleBirkhoffDomain_open_real (p := 2) (by simp) (by norm_num)).2 v)
    ((compatibleBirkhoffDomain_open_real hp hp1).2 w) hsame n).1
  have hv : physicalRealCoefficientsCL v = originalWeightedRealSource _ a :=
    physicalRealCoefficientsCL.apply_symm_apply _
  change (sourceComplexBirkhoffMap (by simp) (by norm_num)
    (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).roots (physicalRealCoefficientsCL v).val).1 n = _ at hc
  rw [hv] at hc
  exact hc.symm

/-- The actual ordinary physical flow has exactly the restored fourth
coordinate phase, at every signed mode and every real time. -/
theorem compatibleBirkhoff_ordinaryFourthClassicalSourceFlow
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) (a : FourthClassicalSource)
    (ha : (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd)
    (time : ℝ) (n : ℤ) :
    (compatibleBirkhoff hp hp1 (physicalScalarPairCLM
      (fourthClassicalScalarInput h2p (ordinaryFourthClassicalSourceFlow a time)
        (ordinaryFourthClassicalSourceFlow_diagonal a ha time))).val).1 n =
      fourthScalarOrdinaryCoordinate hp hp1 h2p n time a ha := by
  let F := fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)
  let D := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex
  let φ := originalWeightedRealSource _ a
  let v := fourthClassicalScalarInput h2p a ha
  have hv : physicalRealCoefficientsCL (physicalScalarPairCLM v) = fourthClassicalSourceAtExponent h2p a := by
    rw [show physicalScalarPairCLM v = physicalRealCoefficientsCL.symm (fourthClassicalSourceAtExponent h2p a) from
      fourthClassicalScalarInput_pair h2p a ha,ContinuousLinearEquiv.apply_symm_apply]
  have hfreq : (fourthSourcePhaseFrequency hp hp1).frequency
      (physicalRealCoefficientsCL (physicalScalarPairCLM v)) n = F.frequency φ n := by
    rw [hv]
    exact congrFun (fourthSourcePhaseFrequency_exponent (p := 2) (by simp) (by norm_num) hp hp1 h2p φ) n
  have hR : fourthScalarRenormalizedCoordinate hp hp1 n time v =
      Complex.exp (((-time*F.frequency φ n : ℝ) : ℂ)*Complex.I)*
        (sourceComplexBirkhoffMap (p := 2) (by simp) (by norm_num)
          (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).roots φ.val).1 n := by
    change Complex.exp (((-time*(fourthSourcePhaseFrequency hp hp1).frequency
      (physicalRealCoefficientsCL (physicalScalarPairCLM v)) n : ℝ) : ℂ)*Complex.I)*
        (compatibleBirkhoff hp hp1 (physicalScalarPairCLM v).val).1 n = _
    rw [hfreq,compatibleBirkhoff_fourthClassicalScalarInput hp hp1 h2p a ha n]
  rw [compatibleBirkhoff_fourthClassicalScalarInput hp hp1 h2p]
  rw [originalWeightedRealSource_ordinaryFourthClassicalSourceFlow]
  have hflow := congrArg (fun z : Coeff 2 × Coeff 2 => z.1 n)
    (ordinaryFourthSourcePhaseFrequency.complex_map_imageFlow D φ time
      (ordinaryFourthSourcePhaseFrequency.mem_imageDomain_of_le_two D le_rfl φ time))
  rw [hflow]
  change Complex.exp (((-time*(F.frequency φ n+12*Real.pi*(n:ℝ)*(sourceHilbertMass φ.val).re) : ℝ) : ℂ)*Complex.I)*_ = _
  unfold fourthScalarOrdinaryCoordinate
  rw [hR]
  have he : (((-time*(F.frequency φ n+12*Real.pi*(n:ℝ)*(sourceHilbertMass φ.val).re) : ℝ) : ℂ)*Complex.I) =
      (((-12*Real.pi*(n:ℝ)*time*(fourthClassicalMass a).re : ℝ) : ℂ)*Complex.I)+
        (((-time*F.frequency φ n : ℝ) : ℂ)*Complex.I) := by
    change (((-time*(F.frequency φ n+12*Real.pi*(n:ℝ)*(fourthClassicalMass a).re) : ℝ) : ℂ)*Complex.I) = _
    push_cast
    ring
  rw [he,Complex.exp_add,mul_assoc]

end NLS.Articles.MKdVBelowL2
