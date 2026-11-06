import NLS.KdV.HillRoughFinitePairRegularity
import NLS.Fourier.PeriodOneSmoothSynthesis

/-! # Finite physical Birkhoff support supplies an actual smooth potential

Every higher Sobolev membership follows from the already-proved global
physical regularity criterion. Smooth synthesis retains all literal
unit-period Fourier coefficients, without an initial regularity premise.
-/
noncomputable section
set_option autoImplicit false
open NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_smooth_of_finite_positive_support (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (hf : (Function.support (D.positive q)).Finite) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      ∀ n : ℤ, q.val n=periodOneCoefficient f n := by
  have hm (s : ℝ) (hs : 0≤s) : Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) 2 := by
    apply (D.sobolev_iff_positive_mem q hr s (by linarith)).mpr
    have hfin : (Function.support (fun j => (Weight.sobolev (s+1) j : ℂ)*D.positive q j)).Finite := by
      apply hf.subset
      intro j hj hz
      apply hj
      exact mul_eq_zero_of_right _ hz
    exact (memℓp_zero_iff.mpr hfin).of_exponent_ge bot_le
  let a : Coeff 1 := WeightedCoeff.sobolevToL1CLM 2 (by simp) ⟨q.val,hm 1 zero_le_one⟩
  have ha (n : ℤ) : a n=q.val n := WeightedCoeff.sobolevToL1CLM_apply 2 (by simp) _ n
  refine ⟨periodOneSynthesis a,?_,periodOneSynthesis_periodic a,?_⟩
  · apply contDiff_periodOneSynthesis_of_all_sobolev (p := 2) (by simp)
    intro s hs
    simpa only [ha] using hm s hs
  · intro n
    rw [periodOneCoefficient_synthesis,ha]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
