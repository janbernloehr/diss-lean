import NLS.SequenceSpaces.PeriodOneMiuraRealCharts

/-! # Reality along the actual rough Miura source path -/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

theorem IsRealPeriodOneHminusOne.sub {q p : PeriodOneHminusOne}
    (hq : IsRealPeriodOneHminusOne q) (hp : IsRealPeriodOneHminusOne p) :
    IsRealPeriodOneHminusOne (q-p) := by
  intro k
  simp only [WeightedCoeff.sub_val,map_sub,hq k,hp k]

theorem periodOneL2Inclusion_single_zero_real (c : ℝ) :
    IsRealPeriodOneHminusOne (periodOneL2Inclusion (lp.single 2 0 (c : ℂ))) := by
  intro k
  by_cases hk : k = 0
  · simp [periodOneL2Inclusion_apply,hk]
  · simp [periodOneL2Inclusion_apply,lp.single_apply,hk,neg_ne_zero.mpr hk]

theorem periodOneMiura_real (u : Coeff 2) (hu : ∀ k : ℤ, u (-k) = conj (u k)) :
    IsRealPeriodOneHminusOne (periodOneMiura u) := by
  have he : coeffRealConjugation u = u := by
    ext k
    rw [coeffRealConjugation_apply,hu k,conj_conj]
  have hQ : IsRealPeriodOneHminusOne (periodOneShiftedMiura 0 u) := by
    intro k
    have hh := congrArg (fun q : PeriodOneHminusOne => q.val (-k))
      (periodOneShiftedMiura_realConjugation 0 u)
    simpa only [he,WeightedCoeff.conjugateReflection_apply,neg_neg] using hh
  exact hQ.sub (fun k => by simpa only [periodOneL2Inclusion_apply] using hu k)

end NLS
