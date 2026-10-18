import NLS.ZakharovShabat.NLSWKBComparison
import NLS.ZakharovShabat.HigherSobolevH1Realization
import NLS.ZakharovShabat.SourcePeriodicH1Norm
import NLS.ZakharovShabat.ClassicalSobolevRemainderTimeBounds
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # Free solution comparison on original Sobolev balls

Period doubling preserves the physical potential and gives the exact factor-two H1 bound used in the free-column estimate.
-/

noncomputable section
open Set Complex NLS.Fourier NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Period doubling realizes the original unit-period Hs source as the
same classical potential, with an explicit factor-two H1 norm bound. -/
theorem classicalPotentialOfFunctions_eq_higherSobolev
    (s : ℕ) (hs : 1 ≤ s) (ab : SobolevSource s) (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j) :
    classicalPotentialOfFunctions a b ha hb =
      classicalSobolevPotential
        (Coeff.periodDoubleSobolev (hierarchySobolevToScalarDomain s hs ab.1),
         Coeff.periodDoubleSobolev (hierarchySobolevToScalarDomain s hs ab.2)) := by
  have h1 := periodOneSobolevSynthesis_eq_of_coefficients
    (hierarchySobolevToScalarDomain s hs ab.1) a ha hpa (by intro j; simpa using hca j)
  have h2 := periodOneSobolevSynthesis_eq_of_coefficients
    (hierarchySobolevToScalarDomain s hs ab.2) b hb hpb (by intro j; simpa using hcb j)
  apply ContinuousMap.ext
  intro t
  have h := sourcePeriodicH1Potential_eq_classical (higherSobolevToH1 s hs ab) t
  rw [extend_coe] at h
  simpa only [classicalPotentialOfFunctions_apply,sourcePeriodicH1Potential,higherSobolevToH1,← h1,← h2] using h

/-- The original Hs source has an actual free-solution comparison uniform
on its coefficient norm ball, with no smoothness beyond continuity. -/
theorem norm_classicalSolution_sub_free_higherSobolev_le
    (s : ℕ) (hs : 1 ≤ s) (R H : ℝ)
    (ab : SobolevSource s) (hab : ‖ab‖ ≤ R) (a b : ℝ → ℂ)
    (ha : Continuous a) (hb : Continuous b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = periodOneCoefficient b j)
    (z : ℂ) (hz : z ≠ 0) (hzH : |z.im| ≤ H) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    ‖classicalSolution (classicalPotentialOfFunctions a b ha hb) z v t-classicalFreeVector z v t‖ ≤
      (2*classicalSobolevErrorConstant (2*R) H)*‖v‖*‖(2*I*z)⁻¹‖ := by
  let c := (Coeff.periodDoubleSobolev (hierarchySobolevToScalarDomain s hs ab.1),
    Coeff.periodDoubleSobolev (hierarchySobolevToScalarDomain s hs ab.2))
  have hc : ‖c‖ ≤ 2*R := by
    apply norm_prod_le_iff.mpr
    constructor
    · exact (Coeff.norm_periodDoubleSobolev_le _).trans (mul_le_mul_of_nonneg_left
        ((WeightedCoeff.norm_sobolevInclusion_le _ ab.1).trans ((norm_fst_le ab).trans hab)) (by norm_num))
    · exact (Coeff.norm_periodDoubleSobolev_le _).trans (mul_le_mul_of_nonneg_left
        ((WeightedCoeff.norm_sobolevInclusion_le _ ab.2).trans ((norm_snd_le ab).trans hab)) (by norm_num))
  rw [classicalPotentialOfFunctions_eq_higherSobolev s hs ab a b ha hb hpa hpb hca hcb]
  have he := norm_classicalSolutionRemainder_sobolev_strip_le (2*R) H c hc z hz hzH v t
  change ‖classicalSolution (classicalSobolevPotential c) z v t-classicalFreeVector z v t‖ ≤ _ at he
  apply he.trans_eq
  simp only [classicalSobolevErrorConstant,norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
  ring

end NLS.ZakharovShabat
