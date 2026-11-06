import NLS.ZakharovShabat.SourceNativeFunctionalActionDependence
import NLS.ZakharovShabat.SourceSobolevFourthComplexGerm
import NLS.ZakharovShabat.SourceSobolevFourthLowerHamiltonians

/-! # Independent physical momentum in the actual fractional Birkhoff chart -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original complex fractional source is included coefficient-for-
coefficient in the established physical H¹ pair. -/
def fourthNativeComplexH1PairCLM :
    WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2 →L[ℂ]
      (ScalarDomain 2 × ScalarDomain 2) :=
  let L := (hierarchySobolevToScalarDomain 1 le_rfl).comp fourthSobolevToH1
  (L.prodMap L).comp fourthNativeComplexSourceCLM

theorem fourthNativeComplexH1PairCLM_real (a : NativeFourthSobolevSource) :
    fourthNativeComplexH1PairCLM a.val = fourthNativeH1PairCLM a := rfl

/-- The independently defined physical momentum on the whole complex
native source, retaining its original period-one normalization. -/
def sourceComplexNativeMomentum
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) : ℂ :=
  periodOneSobolevMomentum (fourthNativeComplexH1PairCLM a)

theorem sourceComplexNativeMomentum_real (a : NativeFourthSobolevSource) :
    sourceComplexNativeMomentum a.val = sourceFourthSobolevMomentum a := rfl

theorem analyticAt_sourceComplexNativeMomentum
    (a : WeightedCoeffPair (sourceFrequencyWeight fourthSobolevSpectralWeight) 2) :
    AnalyticAt ℂ sourceComplexNativeMomentum a :=
  (analyticAt_periodOneSobolevMomentum _).comp (fourthNativeComplexH1PairCLM.analyticAt a)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Actual physical momentum pulled back by the full native inverse. -/
def nativeMomentumBirkhoff
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) : ℂ :=
  sourceFourthSobolevMomentum ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm z)

theorem nativeMomentumBirkhoff_map
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource) :
    D.nativeMomentumBirkhoff (D.originalWeightedRealMap fourthSobolevSpectralWeight a) =
      sourceFourthSobolevMomentum a :=
  congrArg sourceFourthSobolevMomentum
    ((D.originalWeightedRealSobolevEquiv (by rfl) (3/2) (by norm_num)).symm_apply_apply a)

theorem analyticAt_nativeMomentumBirkhoff
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) : AnalyticAt ℝ D.nativeMomentumBirkhoff z :=
  (analyticAt_sourceFourthSobolevMomentum _).comp
    (D.originalWeightedRealSobolevEquiv_symm_analytic (by rfl) (3/2) (by norm_num) z (mem_univ _))

/-- Momentum is constant on the full original native action levels, by
physical finite-gap invariance and actual weighted inverse approximation. -/
theorem nativeMomentumBirkhoff_eq_of_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z r : FourthSobolevBirkhoffTarget)
    (h : ∀ n : ℤ, RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight r) n =
      RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n) :
    D.nativeMomentumBirkhoff r = D.nativeMomentumBirkhoff z := by
  apply D.nativeFunctional_inverse_eq_of_actions sourceFourthSobolevMomentum
    (continuous_iff_continuousAt.mpr fun a => (analyticAt_sourceFourthSobolevMomentum a).continuousAt) _ z r h
  intro a b hf hg hlevel
  rw [sourceFourthSobolevMomentum_eq_finiteGap a hf,sourceFourthSobolevMomentum_eq_finiteGap b hg]
  exact sourceFiniteGapNLSHamiltonian_eq_of_actions (by simp) (by norm_num) _ _ hf hg hlevel 2

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
