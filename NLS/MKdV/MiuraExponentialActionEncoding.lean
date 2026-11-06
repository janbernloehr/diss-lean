import NLS.MKdV.MiuraCartesianRealActionLifts
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # A positive central coordinate for gluing signed-mean action factors

Only the auxiliary action parameter is exponentiated. Decoding by the
principal logarithm recovers every real signed mean, including negative
and zero means. No recovery of signed mean from NLS actions is asserted.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraExponentialActionParameters (b : MiuraActionMeanTarget) : Coeff 1 :=
  miuraActionQuadraticParameters b+lp.single 1 0 (Complex.exp b.2-b.2)

theorem miuraExponentialActionParameters_apply (b : MiuraActionMeanTarget) (n : ℤ) :
    miuraExponentialActionParameters b n =
      if 0 < n then (Weight.sobolev 1 n : ℂ)*b.1.val n else if n = 0 then Complex.exp b.2 else 0 := by
  change miuraActionQuadraticParameters b n+(lp.single (E := fun _ : ℤ => ℂ) 1 0 (Complex.exp b.2-b.2)) n = _
  rw [miuraActionQuadraticParameters_apply]
  by_cases hn : n = 0
  · subst n
    simp only [lt_self_iff_false,if_false,ite_true,zero_add,lp.single_apply,Pi.single_eq_same]
    ring
  · simp only [if_neg hn,add_zero,lp.single_apply,Pi.single_eq_of_ne hn]

theorem miuraExponentialActionParameters_zero (b : MiuraActionMeanTarget) :
    miuraExponentialActionParameters b 0 = Complex.exp b.2 := by
  rw [miuraExponentialActionParameters_apply]
  simp

theorem analyticAt_miuraExponentialActionParameters (b : MiuraActionMeanTarget) :
    AnalyticAt ℂ miuraExponentialActionParameters b :=
  (miuraActionQuadraticParameters.analyticAt b).add
    (((lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 1 0).analyticAt _).comp
      (analyticAt_snd.cexp.sub analyticAt_snd))

def miuraLogActionParameters (q : Coeff 1) : MiuraActionMeanTarget :=
  ((WeightedCoeff.positiveFromCoeff (Weight.sobolev 1) 1 q).val,Complex.log (q 0))

theorem miuraLogActionParameters_apply (q : Coeff 1) (n : ℤ) :
    (miuraLogActionParameters q).1.val n = if 0 < n then q n/(Weight.sobolev 1 n : ℂ) else 0 :=
  WeightedCoeff.positiveFromCoeff_apply (Weight.sobolev 1) 1 q n

theorem analyticAt_miuraLogActionParameters (q : Coeff 1) (hq : q 0 ∈ Complex.slitPlane) :
    AnalyticAt ℂ miuraLogActionParameters q :=
  (((WeightedCoeff.positiveSubmodule (Weight.sobolev 1) 1).subtypeL.comp
    (WeightedCoeff.positiveFromCoeff (Weight.sobolev 1) 1)).analyticAt q).prod
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 0).analyticAt q).clog hq)

theorem miuraLogActionParameters_exponential (b : MiuraActionMeanTarget)
    (hzero : ∀ n : ℤ, ¬0 < n → b.1.val n = 0) (hmean : b.2.im = 0) :
    miuraLogActionParameters (miuraExponentialActionParameters b) = b := by
  apply Prod.ext
  · apply Subtype.ext
    funext n
    rw [miuraLogActionParameters_apply]
    by_cases hn : 0 < n
    · rw [if_pos hn,miuraExponentialActionParameters_apply,if_pos hn,
        mul_div_cancel_left₀ _ ((Weight.sobolev 1).complex_ne_zero n)]
    · rw [if_neg hn,hzero n hn]
  · change Complex.log (miuraExponentialActionParameters b 0) = b.2
    rw [miuraExponentialActionParameters_zero]
    exact Complex.log_exp (by rw [hmean]; linarith [Real.pi_pos]) (by rw [hmean]; exact Real.pi_pos.le)

theorem miuraRealActionMean_mean_im (a : MiuraRealL2) : (miuraRealL2ActionMeanMap a).2.im = 0 :=
  (miuraPositiveCartesianMap_physicalReal a).2

theorem miuraLogActionParameters_exponential_physical (a : MiuraRealL2) :
    miuraLogActionParameters (miuraExponentialActionParameters (miuraRealL2ActionMeanMap a)) =
      miuraRealL2ActionMeanMap a :=
  miuraLogActionParameters_exponential _ (fun n hn => miuraL2ActionSequence_nonpositive a.val n hn)
    (miuraRealActionMean_mean_im a)

theorem miuraExponentialActionParameters_physical_slitPlane (a : MiuraRealL2) :
    miuraExponentialActionParameters (miuraRealL2ActionMeanMap a) 0 ∈ Complex.slitPlane := by
  rw [miuraExponentialActionParameters_zero]
  have hreal : (miuraRealL2ActionMeanMap a).2 = ((miuraRealL2ActionMeanMap a).2.re : ℂ) := by
    apply Complex.ext <;> simp [miuraRealActionMean_mean_im a]
  rw [hreal,← Complex.ofReal_exp]
  exact Complex.ofReal_mem_slitPlane.mpr (Real.exp_pos _)

theorem miuraExponentialActionParameters_physical_nonnegative (a : MiuraRealL2) :
    miuraExponentialActionParameters (miuraRealL2ActionMeanMap a) ∈ Coeff.nonnegativeLocus 1 := by
  intro n
  rw [miuraExponentialActionParameters_apply]
  by_cases hn : 0 < n
  · rw [if_pos hn]
    exact miuraNormalizedActions_nonnegative a n
  · rw [if_neg hn]
    by_cases hz : n = 0
    · rw [if_pos hz]
      have hm := miuraRealActionMean_mean_im a
      simp only [Complex.exp_re,Complex.exp_im,hm,Real.cos_zero,Real.sin_zero,mul_one,mul_zero]
      exact ⟨trivial,(Real.exp_pos _).le⟩
    · simp only [if_neg hz,Complex.zero_im,Complex.zero_re,le_refl,and_self]

end NLS.MKdV
