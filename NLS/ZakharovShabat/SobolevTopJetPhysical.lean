import NLS.ZakharovShabat.SobolevPhysicalJets
import NLS.Fourier.PeriodOneH1Norm
import NLS.Fourier.DistributionDerivative

/-! # Physical top derivatives of arbitrary integer Sobolev sources -/
noncomputable section
open NLS.Fourier MeasureTheory Set
open scoped SchwartzMap FourierTransform ContDiff
namespace NLS.ZakharovShabat

/-- The last continuous jet retains H¹ regularity. -/
def sobolevPenultimateJet (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) : ScalarDomain 2 :=
  hierarchySobolevToScalarDomain (m-(m-1)) (by omega)
    (hierarchySobolevJet m (m-1) (by omega) a)

/-- An actual almost-everywhere representative of the highest weak derivative. -/
def sobolevTopJetPhysical (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) : ℝ → ℂ :=
  deriv (fun x : ℝ => periodOneSobolevSynthesis (sobolevPenultimateJet m hm a)
    (x : AddCircle (2 : ℝ)))

theorem memLp_sobolevTopJetPhysical (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    MemLp (sobolevTopJetPhysical m hm a) 2 (volume.restrict (Ioc 0 1)) :=
  memLp_deriv_periodOneSobolevSynthesis _

/-- The physical highest derivative has exactly the original unit-period coefficients. -/
@[simp] theorem periodOneCoefficient_sobolevTopJetPhysical
    (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) (j : ℤ) :
    periodOneCoefficient (sobolevTopJetPhysical m hm a) j = hierarchySobolevJetL2 m m le_rfl a j := by
  rw [sobolevTopJetPhysical,periodOneCoefficient_deriv_periodOneSobolevSynthesis]
  simp only [sobolevPenultimateJet,hierarchySobolevToScalarDomain_apply,hierarchySobolevJet_apply,
    hierarchySobolevJetL2_apply]
  have hp (z : ℂ) : z^m = z^(m-1)*z := by
    conv_lhs => rw [show m = (m-1)+1 by omega]
    exact pow_succ _ _
  rw [hp]
  ring

/-- Parseval at the full H^m endpoint, for the actual physical derivative. -/
theorem integral_sq_sobolevTopJetPhysical (m : ℕ) (hm : 1 ≤ m) (a : ScalarSobolev m) :
    (∫ x in (0 : ℝ)..1, ‖sobolevTopJetPhysical m hm a x‖^2) =
      ‖hierarchySobolevJetL2 m m le_rfl a‖^2 := by
  have h := hasSum_sq_periodOneCoefficient (memLp_sobolevTopJetPhysical m hm a)
  simp only [periodOneCoefficient_sobolevTopJetPhysical] at h
  exact h.unique (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.hasSum_norm (p := 2) (by norm_num) (hierarchySobolevJetL2 m m le_rfl a)))

/-- Every coefficient jet is the actual distributional derivative of the preceding jet. -/
theorem hierarchySobolevJetL2_distribution_succ (s k : ℕ) (hk : k+1 ≤ s) (a : ScalarSobolev s) :
    distributionSynthesis (Coeff.periodDouble (hierarchySobolevJetL2 s (k+1) hk a)) =
      TemperedDistribution.derivCLM ℂ
        (distributionSynthesis (Coeff.periodDouble (hierarchySobolevJetL2 s k (by omega) a))) := by
  ext g
  rw [distributionSynthesis_apply,distributionDerivative_apply]
  apply tsum_congr
  intro n
  by_cases hn : n%2 = 0
  · have he : n = 2*(n/2) := by omega
    rw [he,Coeff.periodDouble_even,Coeff.periodDouble_even]
    simp only [hierarchySobolevJetL2_apply,Int.cast_mul,Int.cast_ofNat,pow_succ]
    ring
  · have he : n = 2*(n/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd,Coeff.periodDouble_odd]
    simp

/-- Smooth comparison fixes the highest physical derivative at every point. -/
theorem sobolevTopJetPhysical_eq_classical (m : ℕ) (hm : 1 ≤ m)
    (a : ScalarSobolev m) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (ha : ∀ j, a.val j = periodOneCoefficient f j) :
    sobolevTopJetPhysical m hm a = iteratedDeriv m f := by
  have he := hierarchySobolevJetContinuous_eq_classical m (m-1) (by omega) a f hf hp ha
  change (fun x : ℝ => periodOneSobolevSynthesis (sobolevPenultimateJet m hm a)
    (x : AddCircle (2 : ℝ))) = iteratedDeriv (m-1) f at he
  rw [sobolevTopJetPhysical,he,← iteratedDeriv_succ]
  congr 1
  omega

/-- The entire coefficient hierarchy is the iterated actual weak derivative of its zeroth jet. -/
theorem hierarchySobolevJetL2_distribution_iterate (s k : ℕ) (hk : k ≤ s) (a : ScalarSobolev s) :
    distributionSynthesis (Coeff.periodDouble (hierarchySobolevJetL2 s k hk a)) =
      (fun T => TemperedDistribution.derivCLM ℂ T)^[k]
        (distributionSynthesis (Coeff.periodDouble (hierarchySobolevJetL2 s 0 (by omega) a))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [hierarchySobolevJetL2_distribution_succ s k hk a,ih (by omega),Function.iterate_succ_apply']

end NLS.ZakharovShabat
