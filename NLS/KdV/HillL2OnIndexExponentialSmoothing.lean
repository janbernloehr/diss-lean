import NLS.KdV.HillL2OnIndexOneSmoothingNeighborhood
import NLS.SequenceSpaces.WeightedInfinityExponentialRemainder

/-! The ORIGINAL on-index phase factor minus one has analytic one-order
decay on a common complex L2 neighborhood of every real source. The
actual signed exponent, its exponential and every mode are retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def l2OnIndexExponentialRemainder (P : HillProductEquationPatch) (q : Coeff 2) :
    WeightedCoeff (Weight.sobolev 1) ⊤ :=
  WeightedCoeff.weightedExpRemainder (Weight.sobolev 1) (P.l2OnIndexSobolevExponent q)

private theorem sobolev_one_ge_one (k : ℤ) : 1 ≤ Weight.sobolev 1 k := by
  simp only [Weight.sobolev_apply,Real.rpow_one]
  linarith [abs_nonneg (k : ℝ)]

end NLS.KdV.HillProductEquationPatch
namespace NLS.KdV

theorem exists_hillL2OnIndex_exponential_one_smoothing (q : Coeff 2)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ P : HillProductEquationPatch, ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧
      (∀ r ∈ U, periodOneL2Inclusion r ∈ P.physicalDirichletSource) ∧
      ∃ M : ℝ, 0 ≤ M ∧ AnalyticOnNhd ℂ P.l2OnIndexExponentialRemainder U ∧
        ∀ r ∈ U, ‖P.l2OnIndexExponentialRemainder r‖ ≤ M ∧ ∀ k : ℤ,
          (P.l2OnIndexExponentialRemainder r).val k =
            Complex.exp (P.physicalOnIndexSignedExponent (periodOneL2Inclusion r) k) - 1 := by
  obtain ⟨P,U,hU,hqU,hUP,C,hC,ha,hraw⟩ := exists_hillL2OnIndex_one_smoothing_neighborhood q hr
  refine ⟨P,U,hU,hqU,hUP,C * Real.exp C,by positivity,?_,?_⟩
  · intro r hrU
    exact (WeightedCoeff.analyticAt_weightedExpRemainder (Weight.sobolev 1)
      HillProductEquationPatch.sobolev_one_ge_one _).comp (ha r hrU)
  · intro r hrU
    have hn := WeightedCoeff.norm_weightedExpRemainder_le (Weight.sobolev 1)
      HillProductEquationPatch.sobolev_one_ge_one (P.l2OnIndexSobolevExponent r)
    refine ⟨hn.trans (mul_le_mul (hraw r hrU).1 (Real.exp_le_exp.mpr (hraw r hrU).1)
      (Real.exp_pos _).le hC.le),?_⟩
    intro k
    rw [HillProductEquationPatch.l2OnIndexExponentialRemainder,
      WeightedCoeff.weightedExpRemainder_apply _ HillProductEquationPatch.sobolev_one_ge_one,
      (hraw r hrU).2 k]

end NLS.KdV
