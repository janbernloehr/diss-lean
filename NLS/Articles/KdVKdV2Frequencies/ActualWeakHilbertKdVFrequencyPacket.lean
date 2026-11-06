import NLS.Articles.KdVKdV2Frequencies.LocalSequenceWeakSpectralActionDescent
import NLS.Articles.KdVKdV2Frequencies.NativeHilbertKdVFrequencyPacket
import NLS.KdV.HillRoughScalarReality

/-! # A genuine weighted ell2 analytic packet of ACTUAL KdV corrections

ONE full complex weak-action ball supports a Banach-analytic bounded packet
of the actual corrections divided by their own positive indices. The SAME
fixed inverse recovers every native H1 source with actions in that ball,
without a native-norm, phase, finite-support or open-gap premise. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_actual_weak_hilbert_kdv_frequency_packet (D : GlobalRoughAbelianForwardData) :
    ∃ ρ K : ℝ, ∃ g : Coeff 1 → Coeff 2,
      0<ρ ∧ 0<K ∧ AnalyticOnNhd ℂ g (ball (0 : Coeff 1) ρ) ∧
      (∀ a∈ball (0 : Coeff 1) ρ, ‖g a‖≤K ∧ ∀ j : ℤ, j≤0 → g a j=0) ∧
      (∀ a∈ball (0 : Coeff 1) ρ, a∈Coeff.nonnegativeLocus 1 → ∀ j : ℤ, (g a j).im=0) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeWeakActionSequence 1 q∈ball (0 : Coeff 1) ρ → ∀ n : ℕ+,
          g (D.nativeWeakActionSequence 1 q) (n : ℤ)=
            ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  obtain ⟨δ,K,F,hδ,hK,hF,hbound,hinv,hnative⟩ := D.exists_native_hilbert_kdv_frequency_packet_near_zero
  obtain ⟨Z,T,g,hZ,h0Z,hT,h0T,_,hg,hgbound,hsource,hrec⟩ :=
    D.exists_local_sequence_weak_spectral_action_factor δ K hδ hK.le F hF
      (fun q hq => (hbound q hq).1) (fun q hq => (hbound q hq).2) hinv
  obtain ⟨R,hR,hballZ⟩ := Metric.isOpen_iff.mp hZ 0 h0Z
  obtain ⟨ε,hε,hballT⟩ := Metric.isOpen_iff.mp hT 0 h0T
  let ρ := min ε (R^2/2)
  have hρ : 0<ρ := lt_min hε (by positivity)
  have hsub : ball (0 : Coeff 1) ρ⊆T := (ball_subset_ball (min_le_left _ _)).trans hballT
  have hFreal (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q)
      (hqm : q.val 0=0) (hq : q∈ball (0 : PeriodOneHminusOne) δ) (n : ℕ+) : (F q (n : ℤ)).im=0 := by
    apply hillRoughScalar_real_of_native_real δ (fun p => F p (n : ℤ))
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).continuous).comp_continuousOn hF.continuousOn) ?_ q hqr hqm hq
    intro u hu
    have hc : ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) u n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ)=
        (((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) u n-(2*(n : ℝ)*Real.pi)^3)/(n : ℝ) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hnative u hu n,hc]
    rfl
  refine ⟨ρ,K,g,hρ,hK,hg.mono hsub,(fun a ha => hgbound a (hsub ha)),?_,?_⟩
  · intro a ha hapos j
    obtain ⟨z,hzr,hQ,_⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1) (by simp) a hapos
    have hnorm := Coeff.norm_sq_le_two_norm_quadraticActions (p := 2) (q := 1) (by simp) z hzr
    rw [hQ] at hnorm
    have hasmall : ‖a‖<ρ := mem_ball_zero_iff.mp ha
    have hznorm : ‖z‖<R := (sq_lt_sq₀ (norm_nonneg z) hR.le).mp (by
      have hle : ρ≤R^2/2 := min_le_right _ _
      nlinarith)
    have hz : z∈Z := hballZ (mem_ball_zero_iff.mpr hznorm)
    have he := hrec z hz hzr
    rw [hQ] at he
    rw [he]
    by_cases hj : 0<j
    · let n := positiveIntegerIndex j hj
      have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
      rw [←hnj]
      exact hFreal _ (D.realWeakInverseSource_real _) (D.realWeakInverseSource_zero_mode _) (hsource z hz hzr) n
    · rw [(hbound _ (hsource z hz hzr)).2 j (by omega)]
      rfl
  · intro q hq n
    let a := D.nativeWeakSignedTarget 1 q
    let z := Coeff.signedToCartesian a.val
    have hzreal : z∈Coeff.realPairLocus 2 := Coeff.signedToCartesian_real a
    have hQ : quadraticActionsExponent (q := 1) z=D.nativeWeakActionSequence 1 q := rfl
    have hnorm := Coeff.norm_sq_le_two_norm_quadraticActions (p := 2) (q := 1) (by simp) z hzreal
    rw [hQ] at hnorm
    have hasmall : ‖D.nativeWeakActionSequence 1 q‖<ρ := mem_ball_zero_iff.mp hq
    have hznorm : ‖z‖<R := (sq_lt_sq₀ (norm_nonneg z) hR.le).mp (by
      have hle : ρ≤R^2/2 := min_le_right _ _
      nlinarith)
    have hz : z∈Z := hballZ (mem_ball_zero_iff.mpr hznorm)
    have hsrc := hsource z hz hzreal
    have he := hrec z hz hzreal
    have htarget : (⟨Coeff.cartesianToSigned z,Coeff.cartesianToSigned_real z hzreal⟩ : physicalRealDeletedSubmodule)=a :=
      Subtype.ext (Coeff.cartesianToSigned_signedToCartesian a.val)
    rw [htarget,D.nativeWeakSignedTarget_inverse] at hsrc he
    rw [hQ] at he
    exact (congrArg (fun b : Coeff 2 => b (n : ℤ)) he).trans (hnative q hsrc n)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
