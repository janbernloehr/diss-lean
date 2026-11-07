import NLS.KdV.HillDirichletSpectralLocalFlow
import NLS.SequenceSpaces.PeriodOneMiuraReality

/-! Remove exactly the real constant Fourier coefficient of an arbitrary
physical real Hminus source, retaining EVERY nonzero original mode. -/
noncomputable section
open Complex
namespace NLS.KdV

theorem exists_hillRealMeanZero_normalization (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ p : HillRealMeanZeroSource, ∃ c : ℝ,
      (c:ℂ)=q.val 0 ∧ q=hillRealMeanZeroInclusion p+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)) := by
  have hi : (q.val 0).im=0 := by
    have h := congrArg Complex.im (hr 0)
    simp only [neg_zero,conj_im] at h
    linarith
  let c : ℝ := (q.val 0).re
  have hc : (c:ℂ)=q.val 0 := by
    exact Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi.symm)
  let a := q-periodOneL2Inclusion (lp.single 2 0 (c:ℂ))
  have ha : IsRealPeriodOneHminusOne a := hr.sub (periodOneL2Inclusion_single_zero_real c)
  have ha0 : a.val 0=0 := by
    simp only [a,WeightedCoeff.sub_val,periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,ite_true,hc,sub_self]
  let p : HillRealMeanZeroSource := ⟨⟨a,ha0⟩,ha⟩
  refine ⟨p,c,hc,?_⟩
  change q=(q-periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))+periodOneL2Inclusion (lp.single 2 0 (c:ℂ))
  abel

end NLS.KdV
