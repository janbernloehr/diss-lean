import NLS.ZakharovShabat.ClassicalChainOperator

/-!
# Exact spectral perturbation through the chain operator

Changing the spectral parameter by `h` changes the Volterra coefficient by
minus `h` times the original signed source map. Factoring the inverse gives
the exact resolvent identity whose geometric series generates chain curves.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The spectral increment is minus the signed source coefficient. -/
theorem classicalCoefficientCurve_add_spectral (Φ : Curve (ℂ × ℂ)) (z h : ℂ) :
    classicalCoefficientCurveCLM (z+h,Φ) = classicalCoefficientCurveCLM (z,Φ)-
      h • ContinuousMap.const _ classicalSource := by
  apply ContinuousMap.ext
  intro t
  apply ContinuousLinearMap.ext
  intro y
  simp only [classicalCoefficientCurveCLM_apply,ContinuousMap.sub_apply,ContinuousMap.smul_apply,
    ContinuousMap.const_apply,sub_apply,smul_apply,classicalODECoefficient_apply,classicalSource_apply]
  apply Prod.ext <;> dsimp <;> ring

/-- The same signed spectral increment holds in the bounded Volterra operator algebra. -/
theorem classicalVolterra_add_spectral (Φ : Curve (ℂ × ℂ)) (z h : ℂ) :
    volterra (classicalCoefficientCurveCLM (z+h,Φ)) = volterra (classicalCoefficientCurveCLM (z,Φ))-
      h • volterra (ContinuousMap.const _ classicalSource) := by
  rw [classicalCoefficientCurve_add_spectral]
  change volterraCoefficientMap (_-h • _) = _
  rw [map_sub,map_smul]
  rfl

/-- The perturbed Volterra equation factors through the fixed chain operator. -/
theorem classicalVolterra_factorization (Φ : Curve (ℂ × ℂ)) (z h : ℂ) :
    (1-volterra (classicalCoefficientCurveCLM (z,Φ)))*(1+h • classicalChainOperator Φ z) =
      1-volterra (classicalCoefficientCurveCLM (z+h,Φ)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hQ : (1-volterra (classicalCoefficientCurveCLM (z,Φ))) (classicalChainOperator Φ z u) =
      volterra (ContinuousMap.const _ classicalSource) u := by
    change ((1-volterra (classicalCoefficientCurveCLM (z,Φ)))*
      solutionOperator (classicalCoefficientCurveCLM (z,Φ))) (volterra (ContinuousMap.const _ classicalSource) u) = _
    rw [mul_solutionOperator,one_apply_eq_self]
  simp only [mul_apply_eq_comp,add_apply,one_apply_eq_self,smul_apply,map_add,map_smul,hQ]
  rw [classicalVolterra_add_spectral]
  simp only [sub_apply,one_apply_eq_self,smul_apply]
  module

/-- The inverse at every shifted spectral parameter is expressed through the fixed chain operator. -/
theorem classicalSolutionOperator_add_spectral (Φ : Curve (ℂ × ℂ)) (z h : ℂ) :
    solutionOperator (classicalCoefficientCurveCLM (z+h,Φ)) =
      Ring.inverse (1+h • classicalChainOperator Φ z)*solutionOperator (classicalCoefficientCurveCLM (z,Φ)) := by
  unfold solutionOperator
  rw [← classicalVolterra_factorization,
    Ring.inverse_mul (Or.inl (isUnit_one_sub_volterra (classicalCoefficientCurveCLM (z,Φ))))]

/-- The exact shifted homogeneous curve is the geometric resolvent of minus the chain operator. -/
theorem classicalSolutionCurve_add_spectral (Φ : Curve (ℂ × ℂ)) (z h : ℂ) (v : ℂ × ℂ) :
    classicalSolutionCurve Φ (z+h) v =
      Ring.inverse (1-h • (-classicalChainOperator Φ z)) (classicalSolutionCurve Φ z v) := by
  rw [classicalSolutionCurve_eq_inverse,classicalSolutionOperator_add_spectral,
    mul_apply_eq_comp,← classicalSolutionCurve_eq_inverse]
  congr 1
  congr 1
  module

end NLS.ZakharovShabat
