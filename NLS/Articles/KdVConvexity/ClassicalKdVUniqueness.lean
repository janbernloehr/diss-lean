import NLS.Articles.KdVConvexity.ClassicalKdVActionConservation

/-! # Every strong classical KdV solution is the same global physical phase orbit

Action conservation makes every physical frequency constant along an
arbitrary actual classical solution. Scalar uniqueness identifies all
signed coordinates; the same native global bijection identifies the
entire original source trajectory.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem classicalKdV_signedComponent_eq_phase
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (σ : Bool) (n : ℕ+) (t : ℝ) :
    hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u t).val)=
    Complex.exp ((I*(signedPositiveFrequency
      (B.fourierLebesguePhysicalFrequency 4 (by norm_num) 2 (by simp) (by norm_num)
        (D.fourierLebesgueForward 4 (by norm_num) 2 (by simp) (by norm_num) (u 0)))
      (if σ then (n : ℤ) else -(n : ℤ)) : ℂ))*t)*
    hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u 0).val) := by
  refine NLS.ComplexAnalysis.global_scalar_evolution_eq_exp _
    (fun r : ℝ => hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u r).val)) ?_ t
  intro r
  have hd := D.classicalKdV_hasDerivAt_signedComponent B u hu σ n r
  rwa [D.classicalKdV_physicalFrequency_constant B u hu r] at hd

theorem classicalKdV_eq_fourierLebesguePhaseEvolution
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (t : ℝ) :
    u t=D.fourierLebesguePhaseEvolution B 4 (by norm_num) 2 (by simp) (by norm_num) t (u 0) := by
  apply (D.fourierLebesgueForward_bijective 4 (by norm_num) 2 (by simp) (by norm_num)).injective
  apply physicalRealMeanZeroWeightedExponent_ext_positive
  intro j hj
  let n : ℕ+ := ⟨j.toNat,by omega⟩
  have hn : (n : ℤ)=j := by change (j.toNat : ℤ)=j; omega
  rw [←hn]
  rw [D.fourierLebesguePhaseEvolution_coordinates,B.fourierLebesguePhysicalPhaseFlow_apply,
    D.fourierLebesgueForward_apply,D.fourierLebesgueForward_apply]
  have he := D.classicalKdV_signedComponent_eq_phase B u hu true n t
  simp only [hillRoughSignedAbelianComponent,ite_true] at he
  change (D.signed (fourierLebesgueSourceInclusion 4 (by norm_num) 2 (by simp) (by norm_num) (u t).val)).val (n : ℤ)=_
  refine he.trans ?_
  congr 2
  push_cast
  ring

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
