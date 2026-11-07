import NLS.Articles.KdVKdV2Frequencies.RawEllOneKdVFrequency
import NLS.SequenceSpaces.WeightedConeCalibrationUniqueness

/-! The strong target maps are restrictions of the ACTUAL weak scalar
frequency family. Exact raw weights and finite cone calibration prove
the identity on the ENTIRE strong cone, not only at native sources. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def rawEllOneWeakActionInclusion : Coeff 1 →L[ℂ] Coeff 1 :=
  baseActionNormalization.toContinuousLinearMap.comp
    (baseActionInclusion.comp rawActionHilbertInclusion)

@[simp] theorem rawEllOneWeakActionInclusion_apply (a : Coeff 1) (k : ℤ) :
    rawEllOneWeakActionInclusion a k=(baseActionWeight k : ℂ)*a k := by
  change (baseActionWeight k : ℂ)*(baseActionInclusion (rawActionHilbertInclusion a)).val k=_
  rw [baseActionInclusion_apply,rawActionHilbertInclusion_apply,Equiv.symm_apply_apply]

theorem rawEllOneWeakActionInclusion_nonnegative (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) :
    rawEllOneWeakActionInclusion a∈Coeff.nonnegativeLocus 1 := by
  apply (WeightedCoeff.mem_nonnegativeLocus_iff baseActionWeight 1 _).mp
  exact baseActionInclusion_mem_nonnegative _ (rawActionHilbertInclusion_nonnegative a ha)

theorem rawEllOneWeakActionInclusion_original (b : OriginalActionSpace) :
    rawEllOneWeakActionInclusion (originalActionToCoeffOne b)=
      baseActionNormalization (baseActionInclusion (originalActionInclusion b)) := by
  change baseActionNormalization (baseActionInclusion (rawActionHilbertInclusion (originalActionToCoeffOne b)))=_
  rw [rawActionHilbertInclusion_original]

theorem weak_scalar_original_physical_recovery (D : GlobalRoughAbelianForwardData)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n : ℕ+, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (b : WeightedCoeff.nonnegativeLocus originalActionWeight 1) (n : ℕ+) :
    G n (baseActionNormalization (baseActionInclusion (originalActionInclusion b.val)))=
      originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
  let q := nativeOriginalActionSource D b
  have ha := nativeOriginalActionSource_actions D b
  have he := global_physical_family_native_recovery D G hrec q n
  rw [weakActionEnumeration_native D q b ha,
    nativeSourceFrequency_eq_originalPhysicalFrequency D q b ha n] at he
  exact he

/-- EVERY strong analytic packet with the original physical calibration
agrees on the ENTIRE raw ell1 cone with EVERY genuine weak physical
frequency family, in the exact weak normalization. -/
theorem strong_packet_agrees_actual_weak_frequency
    (D : GlobalRoughAbelianForwardData) {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (U : Set (Coeff 1)) (F : Coeff 1 → Coeff r) (hU : IsOpen U)
    (hCU : Coeff.nonnegativeLocus 1⊆U) (hF : AnalyticOnNhd ℂ F U)
    (hphysical : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      F (originalActionToCoeffOne b.val) (n : ℤ)=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3)
    (V : Set (Coeff 1)) (G : ℕ+ → Coeff 1 → ℂ) (hV : IsOpen V)
    (hCV : Coeff.nonnegativeLocus 1⊆V) (hG : ∀ n : ℕ+, AnalyticOnNhd ℂ (G n) V)
    (hrec : ∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
      z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n : ℕ+, G n (quadraticActionsExponent (q := 1) z)=P.correction n z)
    (a : Coeff 1) (ha : a∈Coeff.nonnegativeLocus 1) (n : ℕ+) :
    F a (n : ℤ)=G n (rawEllOneWeakActionInclusion a) := by
  let W := rawEllOneWeakActionInclusion ⁻¹' V
  have hW : IsOpen W := hV.preimage rawEllOneWeakActionInclusion.continuous
  have hCW : Coeff.nonnegativeLocus 1⊆W := fun b hb => hCV (rawEllOneWeakActionInclusion_nonnegative b hb)
  have hf : ContinuousOn (fun b => F b (n : ℤ)) U := by
    intro b hb
    exact (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) r (n : ℤ)).analyticAt _).comp (hF b hb)).continuousAt.continuousWithinAt
  have hg : ContinuousOn (fun b => G n (rawEllOneWeakActionInclusion b)) W := by
    intro b hb
    exact ((hG n _ hb).comp (rawEllOneWeakActionInclusion.analyticAt b)).continuousAt.continuousWithinAt
  apply Coeff.eq_on_cone_of_weighted_calibration originalActionWeight originalActionToCoeffOne
    originalActionToCoeffOne_apply U W hU hW hCU hCW _ _ hf hg _ a ha
  intro b hb
  rw [hphysical ⟨b,hb⟩ n,rawEllOneWeakActionInclusion_original,
    weak_scalar_original_physical_recovery D G hrec ⟨b,hb⟩ n]

theorem exists_compatible_strong_weak_frequency_packets (D : GlobalRoughAbelianForwardData)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (hr : 1<r) :
    ∃ U : Set (Coeff 1), ∃ F : Coeff 1 → Coeff r,
      ∃ V : Set (Coeff 1), ∃ G : ℕ+ → Coeff 1 → ℂ,
        IsOpen U ∧ Coeff.nonnegativeLocus 1⊆U ∧ AnalyticOnNhd ℂ F U ∧
        IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n : ℕ+, AnalyticOnNhd ℂ (G n) V) ∧
        (∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
          z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n : ℕ+, G n (quadraticActionsExponent (q := 1) z)=P.correction n z) ∧
        ∀ a∈Coeff.nonnegativeLocus 1, ∀ n : ℕ+, F a (n : ℤ)=G n (rawEllOneWeakActionInclusion a) := by
  obtain ⟨ω,_hz,_hr,hphysical,hall⟩ := D.exists_actual_raw_ellOne_kdv_frequency
  obtain ⟨U,F,hU,hCU,hF,_hFz,hFr⟩ := hall r hr
  obtain ⟨V,G,hV,hCV,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  have hp : ∀ b : WeightedCoeff.nonnegativeLocus originalActionWeight 1, ∀ n : ℕ+,
      F (originalActionToCoeffOne b.val) (n : ℤ)=originalPhysicalFrequency b n-(2*(n : ℂ)*Real.pi)^3 := by
    intro b n
    have hb : originalActionToCoeffOne b.val∈Coeff.nonnegativeLocus 1 := by
      intro k
      simpa only [originalActionToCoeffOne_apply] using b.property k
    rw [hFr _ hb,hphysical b n]
  exact ⟨U,F,V,G,hU,hCU,hF,hV,hCV,hG,hrec,
    strong_packet_agrees_actual_weak_frequency D U F hU hCU hF hp V G hV hCV hG hrec⟩

end NLS.Articles.KdVKdV2Frequencies
