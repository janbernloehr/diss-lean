import NLS.ZakharovShabat.SourceSobolevFourthHamiltonian
import NLS.ZakharovShabat.PeriodOneSobolevMomentum
import NLS.ZakharovShabat.SobolevPhysicalJets

/-! # The physical lower renormalization terms on the native H₄ domain

Mass and momentum retain their independent physical H¹ definitions after
coefficient-preserving inclusion of the original fractional source.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Include the physical fractional source in the established H¹ pair. -/
def fourthNativeH1PairCLM : NativeFourthSobolevSource →L[ℝ] (ScalarDomain 2 × ScalarDomain 2) :=
  let L := (hierarchySobolevToScalarDomain 1 le_rfl).comp fourthSobolevToH1
  ((L.restrictScalars ℝ).prodMap (L.restrictScalars ℝ)).comp fourthNativeSourceCLM

@[simp] theorem fourthNativeH1PairCLM_fst (a : NativeFourthSobolevSource) (n : ℤ) :
    (fourthNativeH1PairCLM a).1.val n =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.fst n := by
  change (hierarchySobolevToScalarDomain 1 le_rfl (fourthSobolevToH1 (fourthNativeSourceCLM a).1)).val n = _
  rw [hierarchySobolevToScalarDomain_apply,fourthSobolevToH1_apply,fourthNativeSourceCLM_fst]

@[simp] theorem fourthNativeH1PairCLM_snd (a : NativeFourthSobolevSource) (n : ℤ) :
    (fourthNativeH1PairCLM a).2.val n =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val.snd n := by
  change (hierarchySobolevToScalarDomain 1 le_rfl (fourthSobolevToH1 (fourthNativeSourceCLM a).2)).val n = _
  rw [hierarchySobolevToScalarDomain_apply,fourthSobolevToH1_apply,fourthNativeSourceCLM_snd]

/-- At a finite-gap source, the H¹ inclusion is its actual smooth representative. -/
theorem fourthNativeH1PairCLM_eq_finiteGap (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) :
    fourthNativeH1PairCLM a = sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight a) hf := by
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact fourthNativeH1PairCLM_fst a n
  · exact fourthNativeH1PairCLM_snd a n

/-- The first independent physical Hamiltonian on the full H₄ source. -/
def sourceFourthSobolevMass (a : NativeFourthSobolevSource) : ℂ :=
  periodOneSobolevMass (fourthNativeH1PairCLM a)

/-- The second independent physical Hamiltonian on the full H₄ source. -/
def sourceFourthSobolevMomentum (a : NativeFourthSobolevSource) : ℂ :=
  periodOneSobolevMomentum (fourthNativeH1PairCLM a)

theorem analyticAt_sourceFourthSobolevMass (a : NativeFourthSobolevSource) :
    AnalyticAt ℝ sourceFourthSobolevMass a :=
  (analyticAt_periodOneSobolevMass _).restrictScalars.comp (fourthNativeH1PairCLM.analyticAt a)

theorem analyticAt_sourceFourthSobolevMomentum (a : NativeFourthSobolevSource) :
    AnalyticAt ℝ sourceFourthSobolevMomentum a :=
  (analyticAt_periodOneSobolevMomentum _).restrictScalars.comp (fourthNativeH1PairCLM.analyticAt a)

theorem sourceFourthSobolevMass_eq_finiteGap (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFourthSobolevMass a = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight a) hf 1 := by
  unfold sourceFourthSobolevMass
  rw [fourthNativeH1PairCLM_eq_finiteGap a hf]
  exact periodOneSobolevMass_sourceFiniteGapSobolevPair _ _ _ hf

theorem sourceFourthSobolevMomentum_eq_finiteGap (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈
      sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFourthSobolevMomentum a = sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
      (originalWeightedRealSource fourthSobolevSpectralWeight a) hf 2 := by
  unfold sourceFourthSobolevMomentum
  rw [fourthNativeH1PairCLM_eq_finiteGap a hf]
  exact periodOneSobolevMomentum_sourceFiniteGapSobolevPair _ _ _ hf

end NLS.ZakharovShabat
