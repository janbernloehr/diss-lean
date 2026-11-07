import NLS.ZakharovShabat.AppendixOperatorConvention
import NLS.ZakharovShabat.ClassicalDiagonalConstantMonodromy
import NLS.ZakharovShabat.ContinuousPotentialSource

/-! # The literal Appendix operator contradicts its printed phase formula

The actual real-type H0 witness comes from the smooth constant physical
profile (1,1). Its monodromy has a nonzero off-diagonal hyperbolic sine.
At phase pi/2 the Appendix operator gives the inverse of the printed phase.
The Section2 matrix identities are retained by correcting the Appendix
operator's component order, or by using the explicit convention adapter.
-/
noncomputable section
open Set Complex NLS.LinearVolterra NLS.Articles.MKdVNLSHierarchies
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

def appendixRealConstantWitness : CoeffPair 2 :=
  sourceComponentSwap (continuousPotentialSource classicalDiagonalOnePotential)

theorem appendixRealConstantWitness_realType : appendixRealConstantWitness ∈ realTypeSourceSubmodule 2 := by
  change IsRealType (CoeffPair.toMax 2 (sourceComponentSwap (continuousPotentialSource classicalDiagonalOnePotential)))
  apply sourceComponentSwap_realType
  exact continuousPotentialSource_realType classicalDiagonalOnePotential (by intro t; simp [classicalDiagonalOnePotential])

theorem appendixRealConstantWitness_monodromy :
    appendixFundamentalMatrix appendixRealConstantWitness 0 1 =
      !![(Real.cosh 1:ℂ),I*(Real.sinh 1:ℂ);-I*(Real.sinh 1:ℂ),(Real.cosh 1:ℂ)] := by
  unfold appendixFundamentalMatrix appendixRealConstantWitness
  rw [sourceComponentSwap_involutive]
  have hp : sourcePhysicalL2 (continuousPotentialSource classicalDiagonalOnePotential) =
      continuousPotentialL2Class classicalDiagonalOnePotential := by
    change sourcePhysicalL2 (sourcePhysicalL2Equiv.symm (continuousPotentialL2CLM classicalDiagonalOnePotential)) = _
    rw [sourcePhysicalL2_equiv_symm,continuousPotentialL2CLM_apply]
  change l2WholeLineFundamentalMatrix _ _ (⟨1,by norm_num⟩ : Icc (0:ℝ) 1) = _
  rw [l2WholeLineFundamentalMatrix_on_unit,hp,l2FundamentalMatrix_of_continuous]
  exact classicalMonodromy_diagonalOne

theorem appendix_printed_phase_formula_false :
    appendixFundamentalMatrix (sourcePhaseRotation (Real.pi/2) appendixRealConstantWitness) 0 1 ≠
      reciprocalScalingMatrix (exp ((((Real.pi/2:ℝ):ℂ))*I))
        (appendixFundamentalMatrix appendixRealConstantWitness 0 1) := by
  rw [appendixFundamentalMatrix_phase,appendixRealConstantWitness_monodromy]
  have he : exp ((((Real.pi/2:ℝ):ℂ))*I) = I := by
    simpa only [ofReal_div,ofReal_ofNat] using exp_pi_div_two_mul_I
  rw [he]
  intro h
  have hh := congrArg (fun M => M 0 1) h
  change I⁻¹*(I*(Real.sinh 1:ℂ)) = I*(I*(Real.sinh 1:ℂ)) at hh
  have hi : (I:ℂ)⁻¹ = -I := inv_eq_of_mul_eq_one_left (by norm_num [I_sq])
  have hii : I*I = (-1:ℂ) := by norm_num
  have hs : (Real.sinh 1:ℂ) = -(Real.sinh 1:ℂ) := by
    simpa only [hi,neg_mul,← mul_assoc,hii,neg_one_mul,neg_neg,one_mul] using hh
  have hr := congrArg Complex.re hs
  simp only [ofReal_re,neg_re] at hr
  have hpos : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr (by norm_num)
  linarith

end NLS.ZakharovShabat
