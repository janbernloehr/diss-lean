import NLS.KdV.RiccatiEnergy
import NLS.KdV.HillPeriodOnePotential
import NLS.Fourier.PeriodOneCircleMean
import NLS.ZakharovShabat.PeriodOneSobolevHamiltonian

/-! # Continuous physical KdV energy on the native H1 coefficient domain

The quadratic derivative pairing and cubic physical mean give an independent
continuous energy functional. Its value is the literal unit-period integral
of q_x^2/2+q^3 for the actual absolutely continuous Sobolev representative.
The native inclusion preserves every coefficient and its 2*pi differentiation
normalization.
-/

noncomputable section
open Set Complex MeasureTheory Filter Topology
namespace NLS.KdV
open NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate

def hillSobolevEnergy (a : ScalarDomain 2) : ℂ :=
  periodOneSobolevKinetic (a,a)/2 + periodOneCircleMean ((periodOneSobolevSynthesis a)^3)

theorem continuous_hillSobolevEnergy : Continuous hillSobolevEnergy := by
  unfold hillSobolevEnergy
  have hk : Continuous (fun ab : ScalarDomain 2 × ScalarDomain 2 => periodOneSobolevKinetic ab) :=
    continuous_iff_continuousAt.mpr (fun ab => (analyticAt_periodOneSobolevKinetic ab).continuousAt)
  exact ((hk.comp (continuous_id.prodMk continuous_id)).div_const 2).add
    (periodOneCircleMean.continuous.comp (periodOneSobolevSynthesis.continuous.pow 3))

theorem hillSobolevEnergy_eq_classical (a : ScalarDomain 2) :
    hillSobolevEnergy a =
      classicalHamiltonian (fun x : ℝ => periodOneSobolevSynthesis a (x : AddCircle (2 : ℝ))) := by
  let Q := periodOneSobolevSynthesis a
  have hP := periodOneSobolevSynthesis_periodic a
  have hP3 : Function.Periodic (fun x : ℝ => (Q^3) (x : AddCircle (2 : ℝ))) 1 := by
    intro x
    change (Q ((x+1 : ℝ) : AddCircle (2 : ℝ)))^3 = (Q (x : AddCircle (2 : ℝ)))^3
    have hx : Q ((x+1 : ℝ) : AddCircle (2 : ℝ)) = Q (x : AddCircle (2 : ℝ)) := hP x
    rw [hx]
  have hd : IntervalIntegrable (fun x : ℝ =>
      deriv (fun t : ℝ => Q (t : AddCircle (2 : ℝ))) x *
        deriv (fun t : ℝ => Q (t : AddCircle (2 : ℝ))) x) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
    exact (memLp_deriv_periodOneSobolevSynthesis a).integrable_mul
      (memLp_deriv_periodOneSobolevSynthesis a)
  rw [hillSobolevEnergy, periodOneSobolevKinetic_eq_integral,
    periodOneCircleMean_eq_integral (Q^3) hP3, ← intervalIntegral.integral_div]
  have hd2 : IntervalIntegrable (fun x : ℝ =>
      deriv (fun t : ℝ => Q (t : AddCircle (2 : ℝ))) x *
        deriv (fun t : ℝ => Q (t : AddCircle (2 : ℝ))) x / 2) volume 0 1 := hd.div_const 2
  have hc : IntervalIntegrable (fun x : ℝ => (Q (x : AddCircle (2 : ℝ)))^3) volume 0 1 :=
    ((continuous_periodOneSobolevSynthesis a).pow 3).intervalIntegrable 0 1
  simp only [ContinuousMap.pow_apply]
  rw [← intervalIntegral.integral_add hd2 hc]
  unfold classicalHamiltonian
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [Q, pow_two]

def hillH1Weight : SpectralWeight := SpectralWeight.piSobolev 1 (by norm_num)

theorem hillH1Weight_dominate_scalar (k : ℤ) :
    Weight.sobolev 1 k ≤ hillH1Weight.doubleIndex.toWeight k := by
  unfold hillH1Weight
  rw [Weight.sobolev_apply, SpectralWeight.toWeight_apply, SpectralWeight.doubleIndex_apply,
    SpectralWeight.piSobolev_apply, Real.rpow_one, Real.rpow_one]
  push_cast
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [Real.pi_gt_three, abs_nonneg (k : ℝ)]

def hillNativeH1ToScalar : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2 →L[ℂ] ScalarDomain 2 :=
  WeightedCoeff.inclusionCLM _ _ hillH1Weight_dominate_scalar

@[simp] theorem hillNativeH1ToScalar_apply
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) (k : ℤ) :
    (hillNativeH1ToScalar p).val k = p.val k :=
  WeightedCoeff.inclusionCLM_apply _ _ _ p k

theorem hillH1Weight_growth (n : ℕ) : (n : ℝ)^1 ≤ hillH1Weight (2*(n : ℤ)) := by
  rw [pow_one, hillH1Weight, SpectralWeight.piSobolev_apply, Real.rpow_one]
  push_cast
  rw [abs_of_nonneg (by positivity)]
  nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) n]

def hillNativeH1Energy (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) : ℂ :=
  hillSobolevEnergy (hillNativeH1ToScalar p)

theorem continuous_hillNativeH1Energy : Continuous hillNativeH1Energy := by
  unfold hillNativeH1Energy
  exact continuous_hillSobolevEnergy.comp hillNativeH1ToScalar.continuous

theorem hillNativeH1Energy_eq_classical
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) :
    hillNativeH1Energy p = classicalHamiltonian (fun x : ℝ =>
      periodOneSobolevSynthesis (hillNativeH1ToScalar p) (x : AddCircle (2 : ℝ))) :=
  hillSobolevEnergy_eq_classical _


theorem hillH1Weight_le_scalar_scaled (k : ℤ) :
    hillH1Weight.doubleIndex.toWeight k ≤ (2*Real.pi)*Weight.sobolev 1 k := by
  unfold hillH1Weight
  rw [SpectralWeight.toWeight_apply, SpectralWeight.doubleIndex_apply,
    SpectralWeight.piSobolev_apply, Weight.sobolev_apply, Real.rpow_one, Real.rpow_one]
  push_cast
  rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [Real.pi_gt_three]

def hillScalarToNativeH1 : ScalarDomain 2 →L[ℂ] WeightedCoeff hillH1Weight.doubleIndex.toWeight 2 :=
  WeightedCoeff.weightedMultiplierCLM _ _ (fun _ => 1) (2*Real.pi) (by positivity)
    (fun k => by simpa only [norm_one, mul_one] using hillH1Weight_le_scalar_scaled k)

@[simp] theorem hillScalarToNativeH1_apply (a : ScalarDomain 2) (k : ℤ) :
    (hillScalarToNativeH1 a).val k = a.val k := by
  change (1 : ℂ)*a.val k = a.val k
  exact one_mul _

@[simp] theorem hillNativeH1ToScalar_scalarToNativeH1 (a : ScalarDomain 2) :
    hillNativeH1ToScalar (hillScalarToNativeH1 a) = a := by
  apply Subtype.ext
  funext k
  rw [hillNativeH1ToScalar_apply, hillScalarToNativeH1_apply]

@[simp] theorem hillScalarToNativeH1_nativeH1ToScalar
    (p : WeightedCoeff hillH1Weight.doubleIndex.toWeight 2) :
    hillScalarToNativeH1 (hillNativeH1ToScalar p) = p := by
  apply Subtype.ext
  funext k
  rw [hillScalarToNativeH1_apply, hillNativeH1ToScalar_apply]


end NLS.KdV
