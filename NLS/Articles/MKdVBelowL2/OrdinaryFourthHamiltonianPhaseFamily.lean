import NLS.Articles.MKdVBelowL2.FourthFrequencySwap
import NLS.ZakharovShabat.SourceHilbertMassActionInvariance
import NLS.ZakharovShabat.SourceActionPhaseSwap
import NLS.ZakharovShabat.SourceNativeMomentumCotangent

/-! # The mass-restored fourth phase family on the actual Hilbert source

Restoring 12πnM removes the mass translation in the physical vector field.
The momentum phase correction remains on general real-type pairs and
vanishes on the original scalar mKdV diagonal. No rough mass extension is
assumed: this family is defined on the actual Hilbert source.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat

def ordinaryFourthSourcePhaseFrequency : SourceActionFrequency (p := 2) (by simp) (by norm_num) where
  frequency φ n := (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).frequency φ n+
    12*Real.pi*(n:ℝ)*(sourceHilbertMass φ.val).re
  continuous n := (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).continuous n |>.add
    (continuous_const.mul (Complex.continuous_re.comp
      ((continuousOn_univ.mp analyticOnNhd_sourceHilbertMass.continuousOn).comp continuous_subtype_val)))
  invariant φ ψ h := by
    have hf := (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).invariant φ ψ h
    have hm := (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.hilbertMass_eq_of_actions φ ψ h
    funext n
    rw [hf,hm]

theorem ordinaryFourthSourcePhaseFrequency_componentSwap (φ : realTypeSourceSubmodule 2) (n : ℤ) :
    ordinaryFourthSourcePhaseFrequency.frequency (realSourceComponentSwap φ) n =
      -ordinaryFourthSourcePhaseFrequency.frequency φ (-n) := by
  change (fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).frequency (realSourceComponentSwap φ) n+_ = -(_+_)
  rw [fourthSourcePhaseFrequency_componentSwap,sourceHilbertMass_componentSwap]
  push_cast
  ring

/-- The mass-restored frequency has the independently defined physical H₄
normalization, retaining only the momentum phase term on general pairs. -/
theorem ordinaryFourthSourcePhaseFrequency_eq_physical_derivative (a : NativeFourthSobolevSource) (n : ℤ) :
    (ordinaryFourthSourcePhaseFrequency.frequency (originalWeightedRealSource fourthSobolevSpectralWeight a) n : ℂ) =
      (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.sobolevFourthFrequency a n-
        6*sourceFourthSobolevMomentum a := by
  have hm : ((sourceHilbertMass (originalWeightedRealSource fourthSobolevSpectralWeight a).val).re : ℂ) =
      sourceFourthSobolevMass a := by
    rw [sourceFourthSobolevMass_eq_sourceHilbertMass]
    rw [sourceHilbertMass_eq_half_norm_sq_of_realType _ (originalWeightedRealSource fourthSobolevSpectralWeight a).property]
    rfl
  change (((fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).frequency
    (originalWeightedRealSource fourthSobolevSpectralWeight a) n+
    12*Real.pi*(n:ℝ)*(sourceHilbertMass (originalWeightedRealSource fourthSobolevSpectralWeight a).val).re : ℝ) : ℂ) = _
  rw [Complex.ofReal_add,fourthSourcePhaseFrequency_eq_physical_derivative]
  push_cast
  rw [hm]
  ring

theorem ordinaryFourthHilbertImageFlow_preserves_diagonal (φ : realTypeSourceSubmodule 2)
    (hφ : φ.val.fst = φ.val.snd) (time : ℝ) :
    (ordinaryFourthSourcePhaseFrequency.imageFlow (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex φ time).val.fst =
      (ordinaryFourthSourcePhaseFrequency.imageFlow (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex φ time).val.snd :=
  SourceActionFrequency.imageFlow_preserves_diagonal _ _ le_rfl le_rfl
    ordinaryFourthSourcePhaseFrequency_componentSwap φ hφ time

end NLS.Articles.MKdVBelowL2
