import NLS.SequenceSpaces.PeriodOneMiuraConjugation

/-! # Real scalar paths of physical rough potentials -/
noncomputable section
open Complex
open scoped ComplexConjugate
namespace NLS

theorem periodOneHminusConjugation_real_smul (r : ℝ) (q : PeriodOneHminusOne) :
    periodOneHminusConjugation ((r : ℂ) • q) =
      (r : ℂ) • periodOneHminusConjugation q := by
  apply Subtype.ext
  funext k
  rw [periodOneHminusConjugation_apply]
  change conj ((r : ℂ)*q.val (-k)) = (r : ℂ)*(periodOneHminusConjugation q).val k
  rw [map_mul,conj_ofReal,periodOneHminusConjugation_apply]

theorem periodOneHminusConjugation_real_smul_fixed (r : ℝ) (q : PeriodOneHminusOne)
    (hq : periodOneHminusConjugation q = q) :
    periodOneHminusConjugation ((r : ℂ) • q) = (r : ℂ) • q := by
  rw [periodOneHminusConjugation_real_smul,hq]

@[simp] theorem periodOneHminusConjugation_zero :
    periodOneHminusConjugation (0 : PeriodOneHminusOne) = 0 := by
  apply Subtype.ext
  funext k
  rw [periodOneHminusConjugation_apply]
  change conj (0 : ℂ) = 0
  exact map_zero _

end NLS
