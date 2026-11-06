import NLS.ZakharovShabat.ClassicalPeriodicWholeLine
import NLS.ZakharovShabat.ClassicalBoundaryDeterminants
import NLS.ZakharovShabat.L2WholeLineFloquetMass

/-! # Actual monodromy under a continuous periodic change of base point

The original whole-line fundamental solution conjugates the actual
translated unit-interval monodromy. Arbitrary real shifts and continuous
coefficients are included; no smoothness of the coefficient is required.
-/
noncomputable section
open Set Complex Matrix Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

def periodicProfileTranslate (Φ : C(ℝ,ℂ × ℂ)) (τ : ℝ) : C(ℝ,ℂ × ℂ) :=
  ⟨fun t => Φ (t+τ),Φ.continuous.comp (continuous_id.add_const τ)⟩

def periodicClassicalFundamentalMatrix (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  l2WholeLineFundamentalMatrix (continuousPotentialL2Class (periodicProfileUnitCurve Φ)) z t

theorem periodicClassicalFundamentalMatrix_on_unit (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (t : Icc (0:ℝ) 1) :
    periodicClassicalFundamentalMatrix Φ z t = classicalFundamentalMatrix (periodicProfileUnitCurve Φ) z t := by
  have h := l2WholeLineFundamentalMatrix_on_period (continuousPotentialL2Class (periodicProfileUnitCurve Φ)) z 0 t
    (by simpa only [Int.cast_zero,zero_add] using t.property)
  simpa only [periodicClassicalFundamentalMatrix,Int.cast_zero,sub_zero,zpow_zero,Units.val_one,mul_one,
    l2FundamentalMatrix_of_continuous] using h

theorem periodicClassicalFundamentalMatrix_add_one (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    periodicClassicalFundamentalMatrix Φ z (t+1) =
      periodicClassicalFundamentalMatrix Φ z t * classicalMonodromy (periodicProfileUnitCurve Φ) z := by
  have h := l2WholeLineFundamentalMatrix_add_int (continuousPotentialL2Class (periodicProfileUnitCurve Φ)) z t 1
  simpa only [periodicClassicalFundamentalMatrix,Int.cast_one,zpow_one,coe_l2MonodromyUnit,
    l2Monodromy,l2FundamentalMatrix_of_continuous,classicalMonodromy] using h

theorem isUnit_periodicClassicalFundamentalMatrix (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (t : ℝ) :
    IsUnit (periodicClassicalFundamentalMatrix Φ z t) := isUnit_l2WholeLineFundamentalMatrix _ _ _

theorem periodicClassicalSolution_shift_basepoint (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) (z : ℂ) (v : ℂ × ℂ) (τ : ℝ) (t : Icc (0:ℝ) 1) :
    classicalSolution (periodicProfileUnitCurve (periodicProfileTranslate Φ τ)) z
      (periodicClassicalSolution Φ z v τ) t = periodicClassicalSolution Φ z v (t+τ) := by
  symm
  apply classicalSolution_unique _ z (periodicClassicalSolution Φ z v τ) _
    ((continuous_periodicClassicalSolution Φ z v).comp (continuous_id.add_const τ)).continuousOn
    (by simp only [Function.comp_apply,id_eq,zero_add]) _ t.property
  intro s _
  exact (hasDerivAt_periodicClassicalSolution Φ hp z v (s+τ)).comp_add_const s.val τ

private theorem vector_pair_eta (v : Fin 2 → ℂ) : ![v 0,v 1] = v := by
  funext i
  fin_cases i <;> rfl

theorem classicalMonodromy_translate_intertwine (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) (z : ℂ) (τ : ℝ) :
    classicalMonodromy (periodicProfileUnitCurve (periodicProfileTranslate Φ τ)) z *
      periodicClassicalFundamentalMatrix Φ z τ =
    periodicClassicalFundamentalMatrix Φ z τ * classicalMonodromy (periodicProfileUnitCurve Φ) z := by
  apply Matrix.mulVec_injective
  funext v
  have h := periodicClassicalSolution_shift_basepoint Φ hp z (v 0,v 1) τ ⟨1,by norm_num⟩
  have hv := congrArg (fun p : ℂ × ℂ => ![p.1,p.2]) h
  have hleft := classicalFundamentalMatrix_mulVec
    (periodicProfileUnitCurve (periodicProfileTranslate Φ τ)) z
    (periodicClassicalFundamentalMatrix Φ z τ *ᵥ v) ⟨1,by norm_num⟩
  simp only [periodicClassicalSolution,l2WholeLineSolution,vector_pair_eta] at hv
  change classicalMonodromy (periodicProfileUnitCurve (periodicProfileTranslate Φ τ)) z *ᵥ
      (periodicClassicalFundamentalMatrix Φ z τ *ᵥ v) = _ at hleft
  rw [← Matrix.mulVec_mulVec,← periodicClassicalFundamentalMatrix_add_one]
  exact hleft.trans (by simpa only [periodicClassicalFundamentalMatrix,vector_pair_eta,add_comm (1:ℝ) τ] using hv)

theorem classicalMonodromy_translate_conjugate (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) (z : ℂ) (τ : ℝ) :
    classicalMonodromy (periodicProfileUnitCurve (periodicProfileTranslate Φ τ)) z =
      periodicClassicalFundamentalMatrix Φ z τ * classicalMonodromy (periodicProfileUnitCurve Φ) z *
        (periodicClassicalFundamentalMatrix Φ z τ)⁻¹ := by
  have h := congrArg (fun M => M*(periodicClassicalFundamentalMatrix Φ z τ)⁻¹)
    (classicalMonodromy_translate_intertwine Φ hp z τ)
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_periodicClassicalFundamentalMatrix Φ z τ)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hu,Matrix.mul_one] at h
  exact h

end NLS.ZakharovShabat
