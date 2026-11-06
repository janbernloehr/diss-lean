import NLS.KdV.HillHminusFiniteGapSobolev
import NLS.Fourier.PeriodOneSmoothSynthesis

/-! # Actual smooth physical realization of real finite-gap rough sources -/
noncomputable section
set_option autoImplicit false
open NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.KdV

/-- Every real finite-gap distributional Hill source is the Fourier sequence
of an everywhere smooth unit-period function, without initial L2 regularity. -/
theorem hillHminus_real_finiteGap_exists_smooth
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (N : ℕ) (hN : 1≤N)
    (hclosed : ∀ n : ℕ, N≤n → hillHminusRealLabels q hq (2*n)=hillHminusRealLabels q hq (2*n-1)) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      ∀ n : ℤ, q.val n=periodOneCoefficient f n := by
  have hr := hillHminus_real_finiteGap_mem_sobolev q hq N hN hclosed
  let a : Coeff 1 := WeightedCoeff.sobolevToL1CLM 2 (by simp) ⟨q.val,hr 1 zero_le_one⟩
  have ha (n : ℤ) : a n=q.val n := WeightedCoeff.sobolevToL1CLM_apply 2 (by simp) _ n
  refine ⟨periodOneSynthesis a,?_,periodOneSynthesis_periodic a,?_⟩
  · apply contDiff_periodOneSynthesis_of_all_sobolev (p := 2) (by simp)
    intro s hs
    simpa only [ha] using hr s hs
  · intro n
    rw [periodOneCoefficient_synthesis,ha]

end NLS.KdV
