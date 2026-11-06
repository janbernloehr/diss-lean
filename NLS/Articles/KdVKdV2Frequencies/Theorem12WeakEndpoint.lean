import NLS.Articles.KdVKdV2Frequencies.WeakKdVAllExponents
import NLS.SequenceSpaces.WeightedAnalyticPullback

/-! The complete s=-1 target clause of Theorem1.2(i), in the ORIGINAL
weighted raw action norm and original weighted frequency targets. One
actual map on the whole positive cone has values in every ell(-1,r), r>1,
with genuine complex Banach-analytic extensions and physical recovery. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

abbrev WeakActionSpace := WeightedCoeff (Weight.sobolev (-1)) 1

def weakActionNormalization : WeakActionSpace ≃L[ℂ] Coeff 1 :=
  (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 1).toContinuousLinearEquiv

theorem weakActionNormalization_positive (a : WeakActionSpace)
    (ha : a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1) :
    weakActionNormalization a∈Coeff.nonnegativeLocus 1 :=
  (WeightedCoeff.mem_nonnegativeLocus_iff (Weight.sobolev (-1)) 1 a).mp ha.1

theorem weakAction_analytic_pullback {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (F : Coeff 1 → WeightedCoeff (Weight.sobolev (-1)) r) (V : Set (Coeff 1))
    (hF : AnalyticOnNhd ℂ F V) :
    AnalyticOnNhd ℂ (fun a : WeakActionSpace => F (weakActionNormalization a))
      (weakActionNormalization ⁻¹' V) :=
  WeightedCoeff.analyticOnNhd_comp_weightIsometry (Weight.sobolev (-1)) (Weight.sobolev (-1)) F V hF

theorem weak_endpoint_target_pullback {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (ω : Coeff 1 → ℤ → ℂ) (V : Set (Coeff 1))
    (F : Coeff 1 → WeightedCoeff (Weight.sobolev (-1)) r)
    (hV : IsOpen V) (hcone : Coeff.nonnegativeLocus 1⊆V) (hF : AnalyticOnNhd ℂ F V)
    (hzero : ∀ a : Coeff 1, ∀ j : ℤ, j≤0 → (F a).val j=0)
    (hrec : ∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (F a).val j=ω a j) :
    ∃ U : Set WeakActionSpace, ∃ G : WeakActionSpace → WeightedCoeff (Weight.sobolev (-1)) r,
      IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1⊆U ∧
      AnalyticOnNhd ℂ G U ∧ (∀ a : WeakActionSpace, ∀ j : ℤ, j≤0 → (G a).val j=0) ∧
      ∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1, ∀ j : ℤ,
        (G a).val j=ω (weakActionNormalization a) j :=
  NLS.ComplexAnalysis.exists_analytic_coordinate_pullback weakActionNormalization
    (WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1) (Coeff.nonnegativeLocus 1) V
    (fun b j => b.val j) ω F weakActionNormalization_positive hV hcone hF hzero hrec

namespace GlobalRoughAbelianForwardData

def nativeWeakRawActions (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) : WeakActionSpace :=
  weakActionNormalization.symm (D.nativeWeakActionSequence 1 q)

theorem nativeWeakRawActions_coefficient (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) (j : ℤ) :
    (D.nativeWeakRawActions q).val j=(D.nativeSourceActionSequence 1 3 (by norm_num) q).val j := by
  change D.nativeWeakActionSequence 1 q j/(Weight.sobolev (-1) j : ℂ)=_
  rw [D.nativeWeakActionSequence_apply 1 3 (by norm_num) q,
    mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]

theorem nativeWeakRawActions_positive (D : GlobalRoughAbelianForwardData)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ))) :
    D.nativeWeakRawActions q∈WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1 := by
  constructor
  · apply (WeightedCoeff.mem_nonnegativeLocus_iff (Weight.sobolev (-1)) 1 _).mpr
    change weakActionNormalization (D.nativeWeakRawActions q)∈Coeff.nonnegativeLocus 1
    rw [nativeWeakRawActions,weakActionNormalization.apply_symm_apply]
    exact Coeff.quadraticActions_mem_nonnegativeLocus _
      (Coeff.signedToCartesian_real (D.nativeWeakSignedTarget 1 q))
  · intro j hj
    rw [D.nativeWeakRawActions_coefficient q j,D.nativeSourceActionSequence_apply,if_neg (by omega)]

/-- The s=-1, EVERY r>1 target assertion of Theorem1.2(i), with a SINGLE
raw frequency map on the entire original positive weak-action cone.
The remaining regularities, asymptotics and compactness are separate. -/
theorem theorem_1_2_i_weak_endpoint (D : GlobalRoughAbelianForwardData) :
    ∃ ω : WeakActionSpace → ℤ → ℂ,
      (∀ a : WeakActionSpace, ∀ j : ℤ, j≤0 → ω a j=0) ∧
      (∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1, ∀ j : ℤ, (ω a j).im=0) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)),
        D.nativeWeakRawActions q∈WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1 ∧
        ∀ n : ℕ+, ω (D.nativeWeakRawActions q) (n : ℤ)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ r : ℝ≥0∞, ∀ hr : 1<r, letI : Fact (1 ≤ r) := ⟨hr.le⟩;
        ∃ U : Set WeakActionSpace, ∃ F : WeakActionSpace → WeightedCoeff (Weight.sobolev (-1)) r,
          IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1⊆U ∧
          AnalyticOnNhd ℂ F U ∧
          (∀ a : WeakActionSpace, ∀ j : ℤ, j≤0 → (F a).val j=0) ∧
          ∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (-1)) 1, ∀ j : ℤ,
            (F a).val j=ω a j := by
  obtain ⟨ω,hzero,hreal,hnative,hall⟩ := D.exists_actual_weak_kdv_frequency_all_exponents
  let Ω := fun a : WeakActionSpace => ω (weakActionNormalization a)
  refine ⟨Ω,(fun a j hj => hzero _ j hj),(fun a ha => hreal _ (weakActionNormalization_positive a ha)),?_,?_⟩
  · intro q
    refine ⟨D.nativeWeakRawActions_positive q,?_⟩
    intro n
    change ω (weakActionNormalization (weakActionNormalization.symm (D.nativeWeakActionSequence 1 q))) (n : ℤ)=_
    rw [weakActionNormalization.apply_symm_apply]
    exact hnative q n
  · intro r hr
    let : Fact (1 ≤ r) := ⟨hr.le⟩
    obtain ⟨V,F,hV,hcone,hF,hFzero,hrec⟩ := hall r hr
    exact weak_endpoint_target_pullback ω V F hV hcone hF hFzero hrec

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
