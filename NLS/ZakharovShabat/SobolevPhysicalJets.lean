import NLS.ZakharovShabat.SobolevHierarchyOperations
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.Fourier.PeriodOneSobolev
import NLS.DifferentialPolynomial.PeriodicEvaluation

/-! # Physical derivatives on the integer Sobolev scale

The kth derivative is a bounded map Hˢ → H^(s-k). For k<s its physical
representative is a continuous periodic function. Smooth comparison uses
actual Fourier integrals and fixes the period-one multiplier at every order.
-/
noncomputable section
open NLS.Fourier
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Repeated period-one differentiation as a bounded map with exact regularity loss. -/
def hierarchySobolevJet (s : ℕ) : (k : ℕ) → k ≤ s → ScalarSobolev s →L[ℂ] ScalarSobolev (s-k)
  | 0, _ => ContinuousLinearMap.id ℂ _
  | k+1, hk => (hierarchySobolevDerivative (s-k) (s-(k+1)) (by omega)).comp
      (hierarchySobolevJet s k (by omega))

@[simp] theorem hierarchySobolevJet_apply (s k : ℕ) (hk : k ≤ s) (a : ScalarSobolev s) (j : ℤ) :
    (hierarchySobolevJet s k hk a).val j = (2*Complex.I*(Real.pi:ℂ)*j)^k*a.val j := by
  induction k with
  | zero => simp [hierarchySobolevJet]
  | succ k ih =>
    simp only [hierarchySobolevJet,ContinuousLinearMap.comp_apply,hierarchySobolevDerivative_apply,ih]
    rw [pow_succ]
    ring

/-- The top derivative is represented in L² by the original Fourier coefficients. -/
def hierarchySobolevJetL2 (s k : ℕ) (hk : k ≤ s) : ScalarSobolev s →L[ℂ] Coeff 2 :=
  (WeightedCoeff.sobolevToL2 (Nat.cast_nonneg (s-k))).comp (hierarchySobolevJet s k hk)

@[simp] theorem hierarchySobolevJetL2_apply (s k : ℕ) (hk : k ≤ s) (a : ScalarSobolev s) (j : ℤ) :
    hierarchySobolevJetL2 s k hk a j = (2*Complex.I*(Real.pi:ℂ)*j)^k*a.val j := by
  simp [hierarchySobolevJetL2]

/-- Coefficient-preserving inclusion into the established H¹ scalar domain. -/
def hierarchySobolevToScalarDomain (s : ℕ) (hs : 1 ≤ s) : ScalarSobolev s →L[ℂ] ScalarDomain 2 :=
  WeightedCoeff.sobolevInclusion (show (1:ℝ) ≤ (s:ℝ) by exact_mod_cast hs)

@[simp] theorem hierarchySobolevToScalarDomain_apply (s : ℕ) (hs : 1 ≤ s)
    (a : ScalarSobolev s) (j : ℤ) : (hierarchySobolevToScalarDomain s hs a).val j = a.val j :=
  WeightedCoeff.sobolevInclusion_apply _ _ _

/-- Lower derivatives have a bounded continuous Fourier realization. -/
def hierarchySobolevJetContinuous (s k : ℕ) (hk : k < s) :
    ScalarSobolev s →L[ℂ] C(AddCircle (2:ℝ),ℂ) :=
  periodOneSobolevSynthesis.comp ((hierarchySobolevToScalarDomain (s-k) (by omega)).comp
    (hierarchySobolevJet s k (by omega)))

/-- Every lower-jet representative is unit-periodic, including nonsmooth source data. -/
theorem hierarchySobolevJetContinuous_periodic (s k : ℕ) (hk : k < s) (a : ScalarSobolev s) :
    Function.Periodic (fun x : ℝ => hierarchySobolevJetContinuous s k hk a (x : AddCircle (2:ℝ))) 1 :=
  periodOneSobolevSynthesis_periodic (hierarchySobolevToScalarDomain (s-k) (by omega)
    (hierarchySobolevJet s k (by omega) a))

/-- Smoothness of every classical iterated derivative. -/
theorem contDiff_iteratedDeriv_of_smooth (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

/-- The kth classical derivative has exactly the kth Fourier multiplier. -/
theorem periodOneCoefficient_iteratedDeriv_of_smooth (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (k : ℕ) (j : ℤ) :
    periodOneCoefficient (iteratedDeriv k f) j = (2*Complex.I*(Real.pi:ℂ)*j)^k*periodOneCoefficient f j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ,periodOneCoefficient_deriv_of_smooth_periodic _
      (contDiff_iteratedDeriv_of_smooth f hf k) (DifferentialPolynomial.periodic_iteratedDeriv f 1 hp k),ih,pow_succ]
    ring

/-- Every lower Sobolev jet is the actual classical derivative for smooth periodic data. -/
theorem hierarchySobolevJetContinuous_eq_classical (s k : ℕ) (hk : k < s)
    (a : ScalarSobolev s) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (ha : ∀ j, a.val j = periodOneCoefficient f j) :
    (fun x : ℝ => hierarchySobolevJetContinuous s k hk a (x : AddCircle (2:ℝ))) = iteratedDeriv k f := by
  let c : ScalarDomain 2 := hierarchySobolevToScalarDomain (s-k) (by omega)
    (hierarchySobolevJet s k (by omega) a)
  change (fun x : ℝ => periodOneSobolevSynthesis c (x : AddCircle (2:ℝ))) = iteratedDeriv k f
  apply eq_of_periodOneCoefficient_eq _ _ (continuous_periodOneSobolevSynthesis c)
    (contDiff_iteratedDeriv_of_smooth f hf k).continuous (periodOneSobolevSynthesis_periodic c)
    (DifferentialPolynomial.periodic_iteratedDeriv f 1 hp k)
  intro j
  simp only [periodOneCoefficient_periodOneSobolevSynthesis,c,
    hierarchySobolevToScalarDomain_apply,hierarchySobolevJet_apply,ha,
    periodOneCoefficient_iteratedDeriv_of_smooth f hf hp]

end NLS.ZakharovShabat
