import NLS.SequenceSpaces.PositiveDeletedProjection
import NLS.SequenceSpaces.PositiveIndexPowerWeight
import NLS.SequenceSpaces.HolderEmbedding
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition

/-! # Native positive Hilbert coordinates for normalized quadratic energy shifts -/
noncomputable section
open Set Complex
namespace NLS.Coeff

def positiveEnergyDisplacements (c : ℝ) (d : Coeff 2) : Coeff 2 :=
  let a := positiveDeletedProjection 2 0 d
  let R := multiplierCLM (p := 2) positiveIndexReciprocal
  (2*(Real.pi : ℂ)) • a +
    R (exponentInclusion (by norm_num : (1 : ENNReal) ≤ 2)
      (holderProduct (p := 2) (r := 2) (q := 1) a a)) - (c : ℂ)^2 • positiveReciprocalHilbert

theorem analyticOnNhd_positiveEnergyDisplacements (c : ℝ) :
    AnalyticOnNhd ℂ (positiveEnergyDisplacements c) univ := by
  intro d _
  let P := positiveDeletedProjection 2 0
  let R := multiplierCLM (p := 2) positiveIndexReciprocal
  have hp := P.analyticAt d
  have hs := ((holderProduct (p := 2) (r := 2) (q := 1)).analyticAt_bilinear _).comp₂ hp hp
  have hi := ((exponentInclusion (by norm_num : (1 : ENNReal) ≤ 2)).analyticAt _).comp hs
  exact ((hp.const_smul (c := 2*(Real.pi : ℂ))).add ((R.analyticAt _).comp hi)).sub analyticAt_const

theorem positiveEnergyDisplacements_positive (c : ℝ) (d : Coeff 2) (n : ℕ+) :
    positiveEnergyDisplacements c d (n : ℤ) =
      (((Real.pi : ℂ)*(n : ℕ)+d (n : ℤ))^2-(c : ℂ)^2-((Real.pi : ℂ)*(n : ℕ))^2)/(n : ℂ) := by
  have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast n.property
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast n.ne_zero
  simp only [positiveEnergyDisplacements,lp.coeFn_add,Pi.add_apply,lp.coeFn_sub,Pi.sub_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,multiplierCLM_apply,multiplier_apply,
    exponentInclusion_apply,holderProduct_apply,positiveDeletedProjection_apply,
    if_pos (show 0 < (n : ℤ) ∧ (n : ℤ) ≠ 0 from ⟨hn,ne_of_gt hn⟩),
    positiveIndexReciprocal_apply,positiveIndexWeight,if_pos hn,positiveReciprocalHilbert_apply]
  simp only [Int.cast_natCast]
  field_simp [hn0]
  ring

theorem positiveEnergyDisplacements_nonpositive (c : ℝ) (d : Coeff 2) (j : ℤ) (hj : j ≤ 0) :
    positiveEnergyDisplacements c d j = 0 := by
  simp only [positiveEnergyDisplacements,lp.coeFn_add,Pi.add_apply,lp.coeFn_sub,Pi.sub_apply,
    lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,multiplierCLM_apply,multiplier_apply,
    exponentInclusion_apply,holderProduct_apply,positiveDeletedProjection_apply,
    if_neg (show ¬ (0 < j ∧ j ≠ 0) by omega),positiveReciprocalHilbert_apply,
    if_neg (not_lt.mpr hj),mul_zero,zero_add,sub_self]

end NLS.Coeff
