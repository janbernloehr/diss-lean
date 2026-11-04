import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity

/-! Literal bounded constant-potential inclusion in the native source. -/
noncomputable section
namespace NLS

def periodOneConstantCLM : ℂ →L[ℂ] PeriodOneHminusOne :=
  periodOneL2Inclusion.comp (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 0)

theorem periodOneConstantCLM_eq_L2_single (c : ℂ) :
    periodOneConstantCLM c = periodOneL2Inclusion (lp.single 2 0 c) := rfl

@[simp] theorem periodOneConstantCLM_apply (c : ℂ) (k : ℤ) :
    (periodOneConstantCLM c).val k = if k=0 then c else 0 := by
  simp [periodOneConstantCLM,periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply]

theorem isReal_periodOneConstantCLM (c : ℝ) :
    IsRealPeriodOneHminusOne (periodOneConstantCLM (c:ℂ)) := by
  intro k
  simp only [periodOneConstantCLM_apply,neg_eq_zero]
  split_ifs <;> simp

end NLS
