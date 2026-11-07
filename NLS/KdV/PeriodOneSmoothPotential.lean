import NLS.KdV.PeriodOneClassicalKdVCurve
import NLS.Fourier.PeriodOneSmoothSynthesis
import NLS.Fourier.PeriodOneFourierUniqueness
import NLS.Fourier.SmoothPeriodicCoefficients

/-! # Smooth physical potentials and their original Fourier sequences

All Sobolev orders are equivalent to an actual smooth unit-period
representative, with every signed coefficient equal to its Fourier integral.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier
open scoped ContDiff
namespace NLS.KdV

def IsSmoothPeriodOnePotential
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2) : Prop :=
  ∀ s : ℝ, 0≤s → Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val.val n) 2

theorem isSmoothPeriodOnePotential_iff_exists_smooth
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2) :
    IsSmoothPeriodOnePotential q ↔
      ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
        ∀ n : ℤ, q.val.val n=periodOneCoefficient f n := by
  constructor
  · intro hq
    let a := WeightedCoeff.sobolevToL1CLM 2 (by simp)
      (WeightedCoeff.sobolevInclusion (by norm_num : (1 : ℝ)≤4) q.val)
    have ha (n : ℤ) : a n=q.val.val n := by
      simp only [a,WeightedCoeff.sobolevToL1CLM_apply,WeightedCoeff.sobolevInclusion_apply]
    refine ⟨periodOneSynthesis a,?_,periodOneSynthesis_periodic a,?_⟩
    · apply contDiff_periodOneSynthesis_of_all_sobolev (p := 2) (by simp)
      intro s hs
      simpa only [ha] using hq s hs
    · intro n
      rw [periodOneCoefficient_synthesis,ha]
  · rintro ⟨f,hf,hp,hc⟩ s hs
    simp_rw [hc]
    exact (memlp_periodOneCoefficient_sobolev_one s hs f hf hp).of_exponent_ge (by norm_num)

end NLS.KdV
