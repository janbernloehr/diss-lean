import NLS.Articles.KdVKdV2Frequencies.NativeCorrectedFrequencyBounds
import NLS.Articles.KdVKdV2Frequencies.OriginalL2ActionBound
import NLS.Articles.KdVKdV2Frequencies.RoughFrequencySourceRecovery
import NLS.SequenceSpaces.PhysicalRealCompactSobolevInclusion
import NLS.SequenceSpaces.CompactCorrectedFrequencyBound
import NLS.Articles.KdVKdV2Frequencies.NativeSourceSobolevCompatibility

/-! Corollary 1.5(iii): uniform O(1/n) on EVERY bounded original real
mean-zero L2 set. Compactness is used only for the corrected frequency
in H^(-1/3); the exact quadratic trace controls the leading action. -/
noncomputable section
open Set Metric Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def OriginalPhysicalFrequencyBoundedL2 (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) : Prop :=
  ∀ S : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))),
    Bornology.IsBounded S → ∃ B : ℝ, 0≤B ∧ ∀ q∈S, ∀ n : ℕ+,
      (n:ℝ)*‖roughKdVFrequency D G n (nativeHillSource 0 q.val)-
        8*(n:ℂ)^3*(Real.pi:ℂ)^3‖≤B

theorem exists_native_bounded_l2_frequency_bound
    (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    ∀ S : Set physicalRealDeletedSubmodule, Bornology.IsBounded S →
      ∃ B : ℝ, 0≤B ∧ ∀ a∈S, ∀ n : ℕ+, (n:ℝ)*
        ‖roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)-
          8*(n:ℂ)^3*(Real.pi:ℂ)^3‖≤B := by
  intro S hS
  let J := physicalRealSobolevInclusion (by norm_num : (-1/3:ℝ)≤0)
  exact @Coeff.exists_bounded_frequency_bound_of_compact_corrected
    physicalRealDeletedSubmodule physicalRealDeletedSubmodule
    physicalRealDeletedSubmodule.seminormedAddCommGroup physicalRealDeletedSubmodule.normedSpace
    physicalRealDeletedSubmodule.seminormedAddCommGroup physicalRealDeletedSubmodule.normedSpace
    inferInstance J
    (isCompactOperator_physicalRealSobolevInclusion (by norm_num : (-1/3:ℝ)<0))
    (fun n a => roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)-
      8*(n:ℂ)^3*(Real.pi:ℂ)^3)
    (fun n a => D.roughActionCoordinate n (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a))
    (nativeCorrectedKdVFrequency D (2/3) (by norm_num) G) (Weight.sobolev 1)
    (fun n => by
      simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_natCast,
        abs_of_nonneg (by positivity : (0:ℝ)≤n)]
      linarith)
    (fun a n => by rw [nativeCorrectedKdVFrequency_eq_physical,realNativeSource_two_thirds_inclusion])
    (fun K hK => exists_compact_native_corrected_frequency_bound D G V hV hCV hG hrec K hK)
    (native_l2_action_weight_bound D) S hS

theorem exists_original_bounded_l2_frequency_bound
    (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1)) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n, G n (quadraticActionsExponent (q := 1) z)=P.correction n z) :
    OriginalPhysicalFrequencyBoundedL2 D G := by
  intro S hS
  let e := physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ)) (Weight.sobolev_neg ((0:ℕ):ℝ))
  exact @Coeff.exists_bounded_frequency_bound_isometry
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))) physicalRealDeletedSubmodule
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))).seminormedAddCommGroup
    (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))).normedSpace
    physicalRealDeletedSubmodule.seminormedAddCommGroup physicalRealDeletedSubmodule.normedSpace e.symm
    (fun n a => roughKdVFrequency D G n (GlobalRoughAbelianForwardData.realNativeSource 1 (by norm_num) a)-
      8*(n:ℂ)^3*(Real.pi:ℂ)^3)
    (fun n q => roughKdVFrequency D G n (nativeHillSource 0 q.val)-8*(n:ℂ)^3*(Real.pi:ℂ)^3)
    (fun n q => by rw [realNativeSource_original_l2])
    (exists_native_bounded_l2_frequency_bound D G V hV hCV hG hrec) S hS

theorem GlobalRoughAbelianForwardData.corollary_1_5_iii (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
        IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
          roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1:ℕ):ℝ)), ∀ n : ℕ+,
        roughKdVFrequency D G n (nativeHillSource 1 q.val)=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n:ℂ)) ∧
      OriginalPhysicalFrequencyBoundedL2 D G := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  refine ⟨V,G,hV,hCV,hG,?_,roughKdVFrequency_native_recovery D G hrec,
    exists_original_bounded_l2_frequency_bound D G V hV hCV hG hrec⟩
  intro B q hr hm hq n
  rw [roughKdVFrequency,roughKdVFrequencyCorrection_eq_physical D G hrec B q hr hm hq n]

end NLS.Articles.KdVKdV2Frequencies
