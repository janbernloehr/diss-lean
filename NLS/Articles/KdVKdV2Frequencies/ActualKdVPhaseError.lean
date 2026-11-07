import NLS.Articles.KdVKdV2Frequencies.ActualKdVPhaseSmoothing
import NLS.Articles.KdVKdV2Frequencies.ActualL2FlowEnergy

/-! The ACTUAL phase error, canonically lifted to h^(3/2), is bounded
linearly in time on EVERY bounded ORIGINAL L2 set. Physical coordinate
remainders and PDE identification are still needed for Corollary 1.7. -/
noncomputable section
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem exists_nativeKdVPhaseError (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (time : ℝ) (a : physicalRealDeletedSubmodule) :
    ∃ E : WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2+1)) 2,
      WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)-1/2≤1-1/2+1) E=
        D.realNativeTarget 1 (by norm_num) (nativeKdVSourceFlow D 1 (by norm_num) G time a)-
          WeightedCoeff.phaseFlow (Weight.sobolev ((1:ℝ)-1/2)) airySignedFrequency time
            (D.realNativeTarget 1 (by norm_num) a) := by
  obtain ⟨C,_hC,hgain⟩ := h {a} Bornology.isBounded_singleton
  obtain ⟨T,_hT,_hc,he⟩ := hgain a (mem_singleton a) time
  exact ⟨T (D.realNativeTarget 1 (by norm_num) a),he⟩

def nativeKdVPhaseError (D : GlobalRoughAbelianForwardData) (G : ℕ+ → Coeff 1 → ℂ)
    (h : ActualNativeKdVPhaseGain D G) (time : ℝ) (a : physicalRealDeletedSubmodule) :
    WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2+1)) 2 :=
  Classical.choose (exists_nativeKdVPhaseError D G h time a)

theorem nativeKdVPhaseError_inclusion (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (time : ℝ) (a : physicalRealDeletedSubmodule) :
    WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)-1/2≤1-1/2+1)
      (nativeKdVPhaseError D G h time a)=
        D.realNativeTarget 1 (by norm_num) (nativeKdVSourceFlow D 1 (by norm_num) G time a)-
          WeightedCoeff.phaseFlow (Weight.sobolev ((1:ℝ)-1/2)) airySignedFrequency time
            (D.realNativeTarget 1 (by norm_num) a) :=
  Classical.choose_spec (exists_nativeKdVPhaseError D G h time a)

theorem nativeKdVPhaseError_eq_multiplier (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (time : ℝ) (a : physicalRealDeletedSubmodule)
    (T : WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2)) 2 →L[ℂ]
      WeightedCoeff (Weight.sobolev ((1:ℝ)-1/2+1)) 2)
    (he : WeightedCoeff.sobolevInclusion (by norm_num : (1:ℝ)-1/2≤1-1/2+1)
        (T (D.realNativeTarget 1 (by norm_num) a))=
        D.realNativeTarget 1 (by norm_num) (nativeKdVSourceFlow D 1 (by norm_num) G time a)-
          WeightedCoeff.phaseFlow (Weight.sobolev ((1:ℝ)-1/2)) airySignedFrequency time
            (D.realNativeTarget 1 (by norm_num) a)) :
    nativeKdVPhaseError D G h time a=T (D.realNativeTarget 1 (by norm_num) a) := by
  apply WeightedCoeff.sobolevInclusion_injective (by norm_num : (1:ℝ)-1/2≤1-1/2+1)
  exact (nativeKdVPhaseError_inclusion D G h time a).trans he.symm

theorem nativeKdVPhaseError_apply (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (time : ℝ) (a : physicalRealDeletedSubmodule) (j : ℤ) :
    (nativeKdVPhaseError D G h time a).val j=
      (Complex.exp (((time*nativeTargetKdVSignedFrequency 1 (by norm_num) G
        (D.realNativeForward 1 (by norm_num) a) j:ℝ):ℂ)*I)-
        Complex.exp (((time*airySignedFrequency j:ℝ):ℂ)*I))*
          (D.realNativeTarget 1 (by norm_num) a).val j := by
  obtain ⟨C,_hC,hgain⟩ := h {a} Bornology.isBounded_singleton
  obtain ⟨T,_hT,hc,he⟩ := hgain a (mem_singleton a) time
  rw [nativeKdVPhaseError_eq_multiplier D G h time a T he]
  exact hc _ j

theorem norm_nativeKdVPhaseError_le (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (S : Set physicalRealDeletedSubmodule) (C : ℝ) (hC : 0≤C)
    (hb : ∀ a∈S, NativeKdVPhaseGainAt D G C a) (a : physicalRealDeletedSubmodule)
    (ha : a∈S) (time : ℝ) : ‖nativeKdVPhaseError D G h time a‖≤|time| * C*‖a‖ := by
  obtain ⟨T,hT,_hc,he⟩ := hb a ha time
  rw [nativeKdVPhaseError_eq_multiplier D G h time a T he]
  exact (T.le_opNorm _).trans (mul_le_mul hT (norm_native_l2_raw_target_le D a)
    (norm_nonneg _) (mul_nonneg (abs_nonneg _) hC))

theorem exists_bounded_nativeKdVPhaseError_bound (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (S : Set physicalRealDeletedSubmodule) (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, 0≤C ∧ ∀ a∈S, ∀ time : ℝ, ‖nativeKdVPhaseError D G h time a‖≤|time| * C := by
  obtain ⟨M,hM,hb⟩ := h S hS
  obtain ⟨R₀,hR₀⟩ := hS.exists_norm_le
  let R := max R₀ 0
  have hR : 0≤R := le_max_right _ _
  refine ⟨M*R,mul_nonneg hM hR,?_⟩
  intro a ha time
  calc
    _ ≤ |time| * M*‖a‖ := norm_nativeKdVPhaseError_le D G h S M hM hb a ha time
    _ ≤ |time| * M*R := mul_le_mul_of_nonneg_left ((hR₀ a ha).trans (le_max_left _ _))
      (mul_nonneg (abs_nonneg _) hM)
    _ = _ := by ring

theorem exists_bounded_originalKdVPhaseError_bound (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ) (h : ActualNativeKdVPhaseGain D G)
    (S : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))))
    (hS : Bornology.IsBounded S) :
    ∃ C : ℝ, 0≤C ∧ ∀ q∈S, ∀ time : ℝ,
      ‖nativeKdVPhaseError D G h time
        ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
          (Weight.sobolev_neg ((0:ℕ):ℝ))).symm q)‖≤|time| * C := by
  let e := (physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
    (Weight.sobolev_neg ((0:ℕ):ℝ))).symm
  have hS' : Bornology.IsBounded (e '' S) := e.isometry.lipschitz.isBounded_image hS
  obtain ⟨C,hC,hb⟩ := exists_bounded_nativeKdVPhaseError_bound D G h (e '' S) hS'
  exact ⟨C,hC,fun q hq time => hb (e q) ⟨q,hq,rfl⟩ time⟩

theorem GlobalRoughAbelianForwardData.corollary_1_7_actual_phase_error (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ (B : PhysicalMiuraFrequencyChart) (q : PeriodOneHminusOne),
        IsRealPeriodOneHminusOne q → q.val 0=0 → q∈B.domain → ∀ n : ℕ+,
          roughKdVFrequency D G n q=(2*(n:ℂ)*Real.pi)^3+B.correction n q) ∧
      ∃ h : ActualNativeKdVPhaseGain D G,
        (∀ S : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))),
          Bornology.IsBounded S → ∃ C : ℝ, 0≤C ∧ ∀ q∈S, ∀ time : ℝ,
            ‖nativeKdVPhaseError D G h time
              ((physicalRealMeanZeroWeightedIsometry (Weight.sobolev ((0:ℕ):ℝ))
                (Weight.sobolev_neg ((0:ℕ):ℝ))).symm q)‖≤|time| * C) ∧
        ∀ (time : ℝ) (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((0:ℕ):ℝ))),
          ‖originalKdVBirkhoffFlow D ((0:ℕ):ℝ) (by norm_num) G time q‖=‖q‖ := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  refine ⟨V,G,hV,hCV,hG,?_,exists_actual_native_kdv_phase_gain D G V hV hCV hG hrec,?_,?_⟩
  · intro B q hr hm hq n
    rw [roughKdVFrequency,roughKdVFrequencyCorrection_eq_physical D G hrec B q hr hm hq n]
  · exact fun S hS => exists_bounded_originalKdVPhaseError_bound D G _ S hS
  · exact fun time q => norm_originalKdVBirkhoffFlow_l2 D G time q

end NLS.Articles.KdVKdV2Frequencies
