import NLS.KdV.SobolevHamiltonian
import NLS.KdV.HillRealWeightedTruncation
import NLS.KdV.HillFinitePhysicalPotential
import NLS.SequenceSpaces.WeightedMultiplier

/-! # Literal native H1 Hill coefficients, physical representatives and energy -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.KdV

def hillH1SpectralWeight : SpectralWeight := SpectralWeight.sobolev 1 (by norm_num)

abbrev HillNativeH1 := WeightedCoeff hillH1SpectralWeight.doubleIndex.toWeight 2

theorem hillH1SpectralWeight_doubleIndex (k : ℤ) :
    hillH1SpectralWeight.doubleIndex k = 1+2*|(k : ℝ)| := by
  simp [hillH1SpectralWeight,SpectralWeight.doubleIndex_apply,SpectralWeight.sobolev_apply,
    Weight.sobolev_apply,abs_mul]

def hillNativeH1ToSobolev : HillNativeH1 →L[ℂ] ScalarDomain 2 :=
  WeightedCoeff.inclusionCLM _ _ (fun k => by
    rw [hillH1SpectralWeight_doubleIndex]
    simp only [Weight.sobolev_apply,Real.rpow_one]
    linarith [abs_nonneg (k : ℝ)])

@[simp] theorem hillNativeH1ToSobolev_apply (q : HillNativeH1) (k : ℤ) :
    (hillNativeH1ToSobolev q).val k = q.val k := WeightedCoeff.inclusionCLM_apply _ _ _ q k

def hillNativeH1Continuous : HillNativeH1 →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  periodOneSobolevSynthesis.comp hillNativeH1ToSobolev

def hillNativeH1Hamiltonian (q : HillNativeH1) : ℂ := sobolevKdVHamiltonian (hillNativeH1ToSobolev q)

theorem analyticAt_hillNativeH1Hamiltonian (q : HillNativeH1) : AnalyticAt ℂ hillNativeH1Hamiltonian q :=
  (analyticAt_sobolevKdVHamiltonian _).comp (hillNativeH1ToSobolev.analyticAt q)

theorem continuous_hillNativeH1Hamiltonian : Continuous hillNativeH1Hamiltonian :=
  continuous_sobolevKdVHamiltonian.comp hillNativeH1ToSobolev.continuous

theorem hillNativeH1Hamiltonian_eq_physical_integral (q : HillNativeH1) :
    hillNativeH1Hamiltonian q = classicalHamiltonian
      (fun x : ℝ => hillNativeH1Continuous q (x : AddCircle (2 : ℝ))) :=
  sobolevKdVHamiltonian_eq_integral _

theorem hillContinuousCoefficients_hillNativeH1Continuous (q : HillNativeH1) :
    hillContinuousCoefficients (hillNativeH1Continuous q) = hillPeriodOneUnitPotential hillH1SpectralWeight q := by
  apply Subtype.ext
  funext k
  rw [hillContinuousCoefficients_apply]
  change fourierCoeff (continuousSynthesis (Coeff.periodDouble
    (WeightedCoeff.sobolevToL1CLM 2 (by simp) (hillNativeH1ToSobolev q)))) k = _
  rw [fourierCoeff_continuousSynthesis]
  change Coeff.periodDouble _ k = (hillForgetWeight hillH1SpectralWeight 2
    (hillPeriodOnePotential hillH1SpectralWeight q)).val k
  rw [hillForgetWeight_apply]
  by_cases hk : k%2=0
  · have he : k=2*(k/2) := by omega
    rw [he,Coeff.periodDouble_even,hillPeriodOnePotential_even]
    simp only [WeightedCoeff.sobolevToL1CLM_apply,hillNativeH1ToSobolev_apply]
  · have he : k=2*(k/2)+1 := by omega
    rw [he,Coeff.periodDouble_odd,hillPeriodOnePotential_odd]

theorem hillNativeH1Continuous_ofFinsupp (a : ℤ →₀ ℂ) :
    hillNativeH1Continuous (WeightedCoeff.ofFinsupp hillH1SpectralWeight.doubleIndex.toWeight 2 a) =
      hillFinitePhysicalPotential a := by
  apply ContinuousMap.ext
  intro x
  change continuousSynthesis (Coeff.periodDouble
    (WeightedCoeff.sobolevToL1CLM 2 (by simp) (hillNativeH1ToSobolev _))) x = _
  have he : WeightedCoeff.sobolevToL1CLM 2 (by simp)
      (hillNativeH1ToSobolev (WeightedCoeff.ofFinsupp hillH1SpectralWeight.doubleIndex.toWeight 2 a)) =
        Coeff.ofFinsupp (p := 1) a := by
    ext k
    simp only [WeightedCoeff.sobolevToL1CLM_apply,hillNativeH1ToSobolev_apply,
      WeightedCoeff.ofFinsupp_apply,Coeff.ofFinsupp_apply]
  rw [he]
  rfl

end NLS.KdV
