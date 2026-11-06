import NLS.KdV.HillEnergyTraceGradient
import NLS.KdV.HillSolutionProducts

/-! # Actual periodic H² regularity of the Hill trace cotangent -/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillEnergyTraceGradientCurve_eq_products (q : Coeff 2) (E : ℂ) :
    hillEnergyTraceGradientCurve q E =
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1 •
        hillSolutionProductCurve q E (1,0) (1,0)+
      ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1) •
          hillSolutionProductCurve q E (1,0) (0,1)-
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 •
        hillSolutionProductCurve q E (0,1) (0,1) := by
  ext t
  dsimp only [hillEnergyTraceGradientCurve,hillSolutionProductCurve,ContinuousMap.sub_apply,
    ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.pow_apply,ContinuousMap.mul_apply,smul_eq_mul]
  ring

def hillEnergyTraceGradientSpatialCurve (q : Coeff 2) (E : ℂ) : Curve ℂ :=
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1 •
    hillSolutionProductSpatialCurve q E (1,0) (1,0)+
  ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
    (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1) •
      hillSolutionProductSpatialCurve q E (1,0) (0,1)-
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 •
    hillSolutionProductSpatialCurve q E (0,1) (0,1)

def hillEnergyTraceGradientSecond (q : Coeff 2) (E : ℂ) (x : ℝ) : ℂ :=
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1 *
    hillSolutionProductSecond q E (1,0) (1,0) x+
  ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
    (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1) *
      hillSolutionProductSecond q E (1,0) (0,1) x-
  (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2 *
    hillSolutionProductSecond q E (0,1) (0,1) x

theorem absolutelyContinuousOnInterval_hillEnergyTraceGradientCurve (q : Coeff 2) (E : ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillEnergyTraceGradientCurve q E)) 0 1 := by
  rw [hillEnergyTraceGradientCurve_eq_products]
  convert! (((absolutelyContinuousOnInterval_hillSolutionProductCurve q E (1,0) (1,0)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1).add
    ((absolutelyContinuousOnInterval_hillSolutionProductCurve q E (1,0) (0,1)).const_smul ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-(hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1))).sub
    ((absolutelyContinuousOnInterval_hillSolutionProductCurve q E (0,1) (0,1)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2) using 1

theorem absolutelyContinuousOnInterval_hillEnergyTraceGradientSpatialCurve (q : Coeff 2) (E : ℂ) :
    AbsolutelyContinuousOnInterval (extend (hillEnergyTraceGradientSpatialCurve q E)) 0 1 := by
  convert! (((absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve q E (1,0) (1,0)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).1).add
    ((absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve q E (1,0) (0,1)).const_smul ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-(hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1))).sub
    ((absolutelyContinuousOnInterval_hillSolutionProductSpatialCurve q E (0,1) (0,1)).const_smul (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).2) using 1

theorem ae_hasDerivAt_hillEnergyTraceGradientCurve (q : Coeff 2) (E : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend (hillEnergyTraceGradientCurve q E))
      (extend (hillEnergyTraceGradientSpatialCurve q E) x) x := by
  rw [hillEnergyTraceGradientCurve_eq_products]
  filter_upwards [ae_hasDerivAt_hillSolutionProductCurve q E (1,0) (1,0),
    ae_hasDerivAt_hillSolutionProductCurve q E (1,0) (0,1),
    ae_hasDerivAt_hillSolutionProductCurve q E (0,1) (0,1)] with x hCC hCS hSS
  exact ((hCC.const_mul _).add (hCS.const_mul _)).sub (hSS.const_mul _)

theorem ae_hasDerivAt_hillEnergyTraceGradientSpatialCurve (q : Coeff 2) (E : ℂ) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend (hillEnergyTraceGradientSpatialCurve q E))
      (hillEnergyTraceGradientSecond q E x) x := by
  filter_upwards [ae_hasDerivAt_hillSolutionProductSpatialCurve q E (1,0) (1,0),
    ae_hasDerivAt_hillSolutionProductSpatialCurve q E (1,0) (0,1),
    ae_hasDerivAt_hillSolutionProductSpatialCurve q E (0,1) (0,1)] with x hCC hCS hSS
  exact ((hCC.const_mul _).add (hCS.const_mul _)).sub (hSS.const_mul _)

theorem memLp_hillEnergyTraceGradientSecond (q : Coeff 2) (E : ℂ) :
    MemLp (hillEnergyTraceGradientSecond q E) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (((memLp_hillSolutionProductSecond q E (1,0) (1,0)).const_mul _).add
    ((memLp_hillSolutionProductSecond q E (1,0) (0,1)).const_mul _)).sub
    ((memLp_hillSolutionProductSecond q E (0,1) (0,1)).const_mul _)

theorem hillEnergyTraceGradientCurve_endpoints (q : Coeff 2) (E : ℂ) :
    hillEnergyTraceGradientCurve q E ⟨0,by norm_num⟩ = hillL2DirichletCharacteristic q E ∧
      hillEnergyTraceGradientCurve q E ⟨1,by norm_num⟩ = hillL2DirichletCharacteristic q E := by
  let C := hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0)
  let S := hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1)
  have hw := hillL2FrequencyStateCurve_wronskian q (Complex.sqrt E) ⟨1,by norm_num⟩
  constructor
  · dsimp only [hillEnergyTraceGradientCurve,ContinuousMap.sub_apply,ContinuousMap.add_apply,
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

theorem hillEnergyTraceGradientSpatialCurve_endpoints (q : Coeff 2) (E : ℂ) :
    hillEnergyTraceGradientSpatialCurve q E ⟨0,by norm_num⟩ =
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1 ∧
    hillEnergyTraceGradientSpatialCurve q E ⟨1,by norm_num⟩ =
      (hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1 := by
  have hw := hillL2FrequencyStateCurve_wronskian q (Complex.sqrt E) ⟨1,by norm_num⟩
  constructor
  · dsimp only [hillEnergyTraceGradientSpatialCurve,hillSolutionProductSpatialCurve,ContinuousMap.sub_apply,
      ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
      ContinuousMap.comp_apply,ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
    rw [hillL2FrequencyStateCurve_zero,hillL2FrequencyStateCurve_zero]
    ring
  · dsimp only [hillEnergyTraceGradientSpatialCurve,hillSolutionProductSpatialCurve,ContinuousMap.sub_apply,
      ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.mul_apply,
      ContinuousMap.comp_apply,ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
    linear_combination
      ((hillL2FrequencyStateCurve q (Complex.sqrt E) (0,1) ⟨1,by norm_num⟩).2-
        (hillL2FrequencyStateCurve q (Complex.sqrt E) (1,0) ⟨1,by norm_num⟩).1)*hw

end NLS.KdV
