import NLS.Articles.KdVKdV2Frequencies.RawEllOneKdVFrequency
import NLS.SequenceSpaces.NonnegativeSobolevActionInclusion

/-! The complete s=-1/2 target clause of Theorem1.2(i), in ORIGINAL
raw ell1 actions and unweighted ellr frequencies for EVERY r>1. One
coherent physical map is retained, with exact all-native H1 recovery. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

def nativeRawKdVActions (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) : Coeff 1 :=
  WeightedCoeff.nonnegativeSobolevToCoeffCLM 3 (by norm_num)
    (D.nativeSourceActionSequence 1 3 (by norm_num) q)

@[simp] theorem nativeRawKdVActions_coefficient (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (j : ℤ) :
    D.nativeRawKdVActions q j=(D.nativeSourceActionSequence 1 3 (by norm_num) q).val j :=
  WeightedCoeff.nonnegativeSobolevToCoeffCLM_apply _ _ _ _

theorem nativeRawKdVActions_nonnegative (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) :
    D.nativeRawKdVActions q∈Coeff.nonnegativeLocus 1 := by
  obtain ⟨b,hb,_hphys⟩ := exists_original_actions_of_native_source D q
  apply WeightedCoeff.nonnegativeSobolevToCoeffCLM_nonnegative
  rw [hb]
  exact originalPositiveActionInsertion_nonnegative b.val b.property

theorem nativeRawKdVActions_nonpositive (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ))) (j : ℤ) (hj : j≤0) :
    D.nativeRawKdVActions q j=0 := by
  rw [D.nativeRawKdVActions_coefficient,nativeSourceActionSequence_apply,if_neg (by omega)]

theorem nativeRawKdVActions_enumeration (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)))
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1)
    (hb : D.nativeSourceActionSequence 1 3 (by norm_num) q=originalPositiveActionInsertion b.val) :
    weakActionEnumeration (D.nativeRawKdVActions q)=originalActionToCoeffOne b.val := by
  ext k
  rw [weakActionEnumeration_apply,D.nativeRawKdVActions_coefficient,hb,
    originalPositiveActionInsertion_apply,originalActionToCoeffOne_apply,Equiv.symm_apply_apply]

/-- ONE raw physical frequency map on the ENTIRE original positive ell1
action cone has genuine unweighted ellr analytic extensions for EVERY
r>1, with exact original native actions and Hamiltonian frequencies. -/
theorem theorem_1_2_i_strong_endpoint (D : GlobalRoughAbelianForwardData) :
    ∃ ω : Coeff 1 → ℤ → ℂ,
      (∀ a : Coeff 1, ∀ j : ℤ, j≤0 → ω a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (ω a j).im=0) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeRawKdVActions q∈Coeff.nonnegativeLocus 1 ∧ ∀ n : ℕ+,
          ω (D.nativeRawKdVActions q) (n : ℤ)=
            (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ r : ℝ≥0∞, ∀ hr : 1<r, letI : Fact (1 ≤ r) := ⟨hr.le⟩;
        ∃ U : Set (Coeff 1), ∃ F : Coeff 1 → Coeff r,
          IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ F U ∧
          (∀ a∈U, ∀ j : ℤ, j≤0 → F a j=0) ∧
          ∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, F a j=ω a j := by
  obtain ⟨Ω,hzero,hreal,hphysical,hall⟩ := D.exists_actual_raw_ellOne_kdv_frequency
  let ω := fun a : Coeff 1 => Ω (weakActionEnumeration a)
  refine ⟨ω,(fun a j hj => hzero _ j hj),
    (fun a ha => hreal _ (weakActionEnumeration_nonnegative a ha)),?_,?_⟩
  · intro q
    refine ⟨D.nativeRawKdVActions_nonnegative q,?_⟩
    intro n
    obtain ⟨b,hb,_hphys⟩ := exists_original_actions_of_native_source D q
    change Ω (weakActionEnumeration (D.nativeRawKdVActions q)) (n : ℤ)=_
    rw [D.nativeRawKdVActions_enumeration q b hb,hphysical b n,
      nativeSourceFrequency_eq_originalPhysicalFrequency D q b hb n]
  · intro r hr
    let : Fact (1 ≤ r) := ⟨hr.le⟩
    obtain ⟨V,F,hV,hcone,hF,hFzero,hrec⟩ := hall r hr
    let U := weakActionEnumeration ⁻¹' V
    let g := fun a => F (weakActionEnumeration a)
    have hga : AnalyticOnNhd ℂ g U := fun a ha => (hF _ ha).comp (weakActionEnumeration.analyticAt a)
    exact ⟨U,g,hV.preimage weakActionEnumeration.continuous,
      (fun a ha => hcone (weakActionEnumeration_nonnegative a ha)),hga,
      (fun a ha => hFzero _ ha),(fun a ha => hrec _ (weakActionEnumeration_nonnegative a ha))⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
