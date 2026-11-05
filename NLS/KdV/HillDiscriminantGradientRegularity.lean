import NLS.KdV.HillDiscriminantGradient
import NLS.KdV.HillSolutionProducts

/-! # Actual periodic H² regularity of the Hill trace cotangent -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillDiscriminantGradientCurve_eq_products (q : Coeff 2) (E : ℂ) :
    hillDiscriminantGradientCurve q E =
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1 •
        hillSolutionProductCurve q E (1,0) (1,0)+
      ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1) •
          hillSolutionProductCurve q E (1,0) (0,1)-
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 •
        hillSolutionProductCurve q E (0,1) (0,1) := by
  ext t
  dsimp only [hillDiscriminantGradientCurve,hillSolutionProductCurve,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.pow_apply,ContinuousMap.mul_apply,smul_eq_mul]
  ring

def hillDiscriminantGradientSpatialCurve (q : Coeff 2) (E : ℂ) : Curve ℂ :=
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1 •
    hillSolutionProductSpatialCurve q E (1,0) (1,0)+
  ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
    (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1) •
      hillSolutionProductSpatialCurve q E (1,0) (0,1)-
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 •
    hillSolutionProductSpatialCurve q E (0,1) (0,1)

def hillDiscriminantGradientSecond (q : Coeff 2) (E : ℂ) (x : ℝ) : ℂ :=
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1 *
    hillSolutionProductSecond q E (1,0) (1,0) x+
  ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
    (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1) *
      hillSolutionProductSecond q E (1,0) (0,1) x-
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 *
    hillSolutionProductSecond q E (0,1) (0,1) x

theorem absolutelyContinuousOnInterval_hillDiscriminantGradientCurve (q : Coeff 2) (E : ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillDiscriminantGradientCurve q E)) 0 1 := by
  rw [hillDiscriminantGradientCurve_eq_products]
  convert! (((absolutelyContinuousOnInterval_hillSolutionProductCurve q E (1,0) (1,0)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1).add
    ((absolutelyContinuousOnInterval_hillSolutionProductCurve q E (1,0) (0,1)).const_smul ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-(hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1))).sub
    ((absolutelyContinuousOnInterval_hillSolutionProductCurve q E (0,1) (0,1)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2) using 1

theorem absolutelyContinuousOnInterval_hillDiscriminantGradientSpatialCurve (q : Coeff 2) (E : ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillDiscriminantGradientSpatialCurve q E)) 0 1 := by
  convert! (((absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve q E (1,0) (1,0)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1).add
    ((absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve q E (1,0) (0,1)).const_smul ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-(hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1))).sub
    ((absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve q E (0,1) (0,1)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2) using 1

theorem ae_hasDerivAt_hillDiscriminantGradientCurve (q : Coeff 2) (E : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend (hillDiscriminantGradientCurve q E))
      (extend (hillDiscriminantGradientSpatialCurve q E) x) x := by
  rw [hillDiscriminantGradientCurve_eq_products]
  filter_upwards [ae_hasDerivAt_hillSolutionProductCurve q E (1,0) (1,0),
    ae_hasDerivAt_hillSolutionProductCurve q E (1,0) (0,1),
    ae_hasDerivAt_hillSolutionProductCurve q E (0,1) (0,1)] with x hCC hCS hSS
  exact ((hCC.const_mul _).add (hCS.const_mul _)).sub (hSS.const_mul _)

theorem ae_hasDerivAt_hillDiscriminantGradientSpatialCurve (q : Coeff 2) (E : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend (hillDiscriminantGradientSpatialCurve q E))
      (hillDiscriminantGradientSecond q E x) x := by
  filter_upwards [ae_hasDerivAt_hillSolutionProductSpatialCurve q E (1,0) (1,0),
    ae_hasDerivAt_hillSolutionProductSpatialCurve q E (1,0) (0,1),
    ae_hasDerivAt_hillSolutionProductSpatialCurve q E (0,1) (0,1)] with x hCC hCS hSS
  exact ((hCC.const_mul _).add (hCS.const_mul _)).sub (hSS.const_mul _)

theorem memLp_hillDiscriminantGradientSecond (q : Coeff 2) (E : ℂ) :
    MemLp (hillDiscriminantGradientSecond q E) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (((memLp_hillSolutionProductSecond q E (1,0) (1,0)).const_mul _).add
    ((memLp_hillSolutionProductSecond q E (1,0) (0,1)).const_mul _)).sub
    ((memLp_hillSolutionProductSecond q E (0,1) (0,1)).const_mul _)

theorem hillDiscriminantGradientCurve_endpoints (q : Coeff 2) (E : ℂ) :
    hillDiscriminantGradientCurve q E ⟨0,by norm_num⟩ = hillL2DirichletCharacteristic q E ∧
      hillDiscriminantGradientCurve q E ⟨1,by norm_num⟩ = hillL2DirichletCharacteristic q E := by
  let C := hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0)
  let S := hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)
  have hw := hillL2FrequencyStateCurve_wronskian q (Complex.sqrt E) ⟨1,by norm_num⟩
  constructor
  · dsimp only [hillDiscriminantGradientCurve,ContinuousMap.sub_apply,ContinuousMap.add_apply,
      ContinuousMap.smul_apply,ContinuousMap.pow_apply,ContinuousMap.mul_apply,
      ContinuousMap.comp_apply,ContinuousMap.fst,ContinuousMap.coe_mk,smul_eq_mul]
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    simp only [one_pow,mul_one,mul_zero,sub_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),add_zero]
    rfl
  · change (S ⟨1,by norm_num⟩).1*(C ⟨1,by norm_num⟩).1^2+
      ((S ⟨1,by norm_num⟩).2-(C ⟨1,by norm_num⟩).1)*
        ((C ⟨1,by norm_num⟩).1*(S ⟨1,by norm_num⟩).1)-
      (C ⟨1,by norm_num⟩).2*(S ⟨1,by norm_num⟩).1^2 = (S ⟨1,by norm_num⟩).1
    linear_combination (S ⟨1,by norm_num⟩).1*hw

theorem hillDiscriminantGradientSpatialCurve_endpoints (q : Coeff 2) (E : ℂ) :
    hillDiscriminantGradientSpatialCurve q E ⟨0,by norm_num⟩ =
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1 ∧
    hillDiscriminantGradientSpatialCurve q E ⟨1,by norm_num⟩ =
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1 := by
  have hw := hillL2FrequencyStateCurve_wronskian q (Complex.sqrt E) ⟨1,by norm_num⟩
  constructor
  · dsimp only [hillDiscriminantGradientSpatialCurve,hillSolutionProductSpatialCurve,ContinuousMap.sub_apply,
      ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
      ContinuousMap.comp_apply,ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    ring
  · dsimp only [hillDiscriminantGradientSpatialCurve,hillSolutionProductSpatialCurve,ContinuousMap.sub_apply,
      ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
      ContinuousMap.comp_apply,ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
    linear_combination
      ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1)*hw

end NLS.KdV
