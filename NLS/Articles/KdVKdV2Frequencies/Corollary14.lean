import NLS.Articles.KdVKdV2Frequencies.IntermediateRealFrequencyInverse
import NLS.SequenceSpaces.RealConeInverseCoordinates
import NLS.SequenceSpaces.WeightedPositiveActionCoordinates

/-! COMPLETE Corollary 1.4: for EVERY -1<s<-1/2 the ACTUAL frequency
has genuine REAL analytic two-sided local inverses on a relatively open
dense subset containing zero, in the ORIGINAL weighted action norm. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem GlobalRoughAbelianForwardData.corollary_1_4
    (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n, AnalyticOnNhd ℂ (G n) V) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)), ∀ n : ℕ+,
        G n (weakActionEnumeration (D.nativeWeakActionSequence 1 q))=
          (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ s : ℝ, ∀ hs0 : -1<s, ∀ _hs1 : s< -1/2,
        ∃ U : Set (WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1))),
          ∃ F : WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1)) →
            WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1)),
            IsOpen U ∧
            {a | a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1}⊆U ∧
            AnalyticOnNhd ℂ F U ∧
            (∀ a, a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1 → ∀ n : ℕ+,
              (F a).val.val (n : ℤ)=G n (weakActionEnumeration (weakActionNormalization
                (WeightedCoeff.sobolevInclusion (by linarith : -1≤2*s+1) a.val)))) ∧
            (∀ a, a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1 →
              ∀ j : ℤ, ((F a).val.val j).im=0) ∧
            ∃ O : Set (WeightedCoeff.PositiveSupportedActionCone (Weight.sobolev (2*s+1))),
              IsOpen O ∧ Dense O ∧ WeightedCoeff.positiveActionConeZero (Weight.sobolev (2*s+1))∈O ∧
              ∀ a∈O,
                AnalyticAt ℝ (Coeff.coordinateRestriction
                  (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev (2*s+1)) actionIndexEquiv).symm.toContinuousLinearEquiv F)
                  (Coeff.coordinateReCLM
                    (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev (2*s+1)) actionIndexEquiv).symm.toContinuousLinearEquiv a.val) ∧
                ComplexAnalysis.HasAnalyticInverse (𝕜 := ℝ) (Coeff.coordinateRestriction
                  (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev (2*s+1)) actionIndexEquiv).symm.toContinuousLinearEquiv F)
                  (Coeff.coordinateReCLM
                    (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev (2*s+1)) actionIndexEquiv).symm.toContinuousLinearEquiv a.val) := by
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  obtain ⟨E⟩ := nonempty_physicalHstarExtension
  refine ⟨V,G,hV,hCV,hG,global_physical_family_native_recovery D G hrec,?_⟩
  intro s hs0 hs1
  obtain ⟨U₀,F₀,hU₀,hC₀,hF₀,hr₀,hcal,O,hO,hdO,hz,hi⟩ :=
    exists_intermediate_real_frequency_inverse D E (2*s+1) (by linarith) (by linarith)
      V G hV hCV hG hrec
  let L := (WeightedCoeff.positiveActionModelEquiv (Weight.sobolev (2*s+1)) actionIndexEquiv).symm.toContinuousLinearEquiv
  obtain ⟨U,F,hU,hCU,hF,he,P,hP,hdP,hP0,hPi⟩ := Coeff.exists_original_real_inverse_locus
    L (WeightedCoeff.positiveActionConeHomeomorph (Weight.sobolev (2*s+1)) actionIndexEquiv)
    Subtype.val (fun _ => rfl) (WeightedCoeff.positiveActionConeZero (Weight.sobolev (2*s+1))) rfl
    U₀ F₀ hU₀ hC₀ hF₀ O hO hdO hz hi
  have hpos (a : WeightedCoeff.positiveSupportedSubmodule (Weight.sobolev (2*s+1)))
      (ha : a.val∈WeightedCoeff.nonnegativeLocus (Weight.sobolev (2*s+1)) 1) :
      L a∈Coeff.nonnegativeLocus 1 :=
    (WeightedCoeff.positiveActionModelEquiv_nonnegative _ _ a).mp ha
  refine ⟨U,F,hU,(fun a ha => hCU ⟨a,ha⟩),hF,?_,?_,P,hP,hdP,hP0,hPi⟩
  · intro a ha n
    rw [he]
    have hx := WeightedCoeff.positiveActionModelEquiv_raw_index (Weight.sobolev (2*s+1))
      actionIndexEquiv (F₀ (L a)) (actionIndexEquiv.symm n)
    change (L.symm (F₀ (L a))).val.val (n : ℤ)=_
    have hx' : (L.symm (F₀ (L a))).val.val (n : ℤ)=
        F₀ (L a) (actionIndexEquiv.symm n)/(Weight.sobolev (2*s+1) (n : ℤ) : ℂ) := by
      simpa only [L,LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
        LinearIsometryEquiv.symm_symm,Equiv.apply_symm_apply] using hx
    rw [hx',hcal _ (hpos a ha) n,mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    have hN : sobolevActionEnumeration (2*s+1) a.val=L a := rfl
    rw [←hN,normalizedSobolevWeakActionInclusion_enumeration]
  · intro a ha
    apply (WeightedCoeff.normalized_positive_action_real_iff _ _ (F a)).mp
    change L (F a)∈Coeff.realLocus 1
    rw [he,L.apply_symm_apply]
    exact hr₀ (L a) (hpos a ha)

end NLS.Articles.KdVKdV2Frequencies
