import NLS.Articles.KdVKdV2Frequencies.IntermediateFrequencyRawTargets
import NLS.Articles.KdVKdV2Frequencies.NativeSobolevRawActions

/-! The entire intermediate target range of Theorem1.2(i), in the
original raw ell(2s+1,1) source AND target norms. One actual weak scalar
frequency calibrates all orders, all native sources and every closed gap. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem actual_weak_family_real_on_cone (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,
        G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) (n : ℕ+) : (G n a).im=0 := by
  obtain ⟨P,z,hz,hzr,hQ⟩ := exists_physical_pair_of_nonnegative_actions D a ha
  rw [←hQ,hrec P z hz hzr n]
  exact physicalMiuraFrequencyChart_real D P.source_chart (P.potential z)
    (P.real_potential z hz hzr) (P.mean_zero z hz) (P.source_mem z hz) n

/-- The COMPLETE -1<s<-1/2 weighted target clause of Theorem1.2(i).
The asymptotic and compactness clauses of Theorem1.2 remain separate. -/
theorem GlobalRoughAbelianForwardData.theorem_1_2_i_intermediate_regularities
    (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)), ∀ n : ℕ+,
        G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ s : ℝ, ∀ hs0 : -1<s, ∀ hs1 : s< -1/2,
        ∃ U : Set (WeightedCoeff (Weight.sobolev (2*s+1)) 1),
          ∃ F : WeightedCoeff (Weight.sobolev (2*s+1)) 1 → WeightedCoeff (Weight.sobolev (2*s+1)) 1,
            IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1⊆U ∧
            AnalyticOnNhd ℂ F U ∧
            (∀ a∈U, ∀ j : ℤ, j≤0 → (F a).val j=0) ∧
            (∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1, ∀ n : ℕ+,
              (F a).val (n : ℤ)=G n (weakActionEnumeration (weakActionNormalization
                (WeightedCoeff.sobolevInclusion (by linarith : -1≤2*s+1) a)))) ∧
            (∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1, ∀ j : ℤ,
              ((F a).val j).im=0) ∧
            ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
              D.nativeSobolevRawActions (2*s+1) (by linarith) q∈
                WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1 ∧
              ∀ n : ℕ+, (F (D.nativeSobolevRawActions (2*s+1) (by linarith) q)).val (n : ℤ)=
                (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3 := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  have hn := global_physical_family_native_recovery D G hrec
  refine ⟨V,G,hV,hCV,hG,hn,?_⟩
  intro s hs0 hs1
  have H := exists_intermediate_raw_frequency_target D
    (-(2*s+1)) (s+1) (by linarith) (by linarith) (by linarith) (by ring) (2*s+1) (by ring)
    V G hV hCV hG hrec
  obtain ⟨U,F,hU,hC,hF,hzero,hcal⟩ := H
  refine ⟨U,F,hU,hC,hF,hzero,hcal,?_,?_⟩
  · intro a ha j
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      rw [←hnj,hcal a ha n]
      apply actual_weak_family_real_on_cone D G hrec
      apply weakActionEnumeration_nonnegative
      apply weakActionNormalization_positive
      exact ⟨(fun k => by simpa only [WeightedCoeff.sobolevInclusion_apply] using ha.1 k),
        (fun k hk => by simpa only [WeightedCoeff.sobolevInclusion_apply] using ha.2 k hk)⟩
    · rw [hzero a (hC ha) j (by omega)]
      rfl
  · intro q
    have hq := D.nativeSobolevRawActions_positive (2*s+1) (by linarith) q
    refine ⟨hq,?_⟩
    intro n
    rw [hcal _ hq n,D.nativeSobolevRawActions_weak]
    exact hn q n

end NLS.Articles.KdVKdV2Frequencies
