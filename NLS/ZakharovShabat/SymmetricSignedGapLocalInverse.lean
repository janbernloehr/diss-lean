import NLS.ZakharovShabat.SymmetricSourceCoordinates
import NLS.ZakharovShabat.SourceSignedGapFreeDerivative
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! # Local analytic inversion of actual symmetric signed gaps at zero

In real Fourier coordinates the actual signed-gap map has derivative twice
the identity at the free source. The Banach inverse function theorem gives
a two-sided analytic local inverse. This is a local result at zero; it does
not assume or establish invertibility at every symmetric source.
-/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

@[simp] theorem symmetricSourceSignedGapMap_zero :
    symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num) 0 = 0 := by
  ext n
  simp [symmetricSourceSignedGapMap,sourceSignedGapSequence_apply,canonicalPeriodOneBoundaryRoots_zero]

/-- The derivative in actual symmetric source coordinates is exactly twice the identity. -/
theorem hasFDerivAt_symmetricSourceSignedGapMap_zero :
    HasFDerivAt (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num))
      ((2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2)) 0 := by
  let S := symmetricSourceCoefficients 2
  let F := sourceSignedGapSequence (p := 2) (by simp) (by norm_num)
  let D := (fderiv ℂ F 0).restrictScalars ℝ
  have hpre : HasFDerivAt (fun a : RealCoeff 2 => F (S a)) (D.comp S) 0 := by
    have hc : HasFDerivAt F D (S 0) := by
      simpa only [map_zero] using
        analyticAt_sourceSignedGapSequence_zero.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact hc.comp 0 S.hasFDerivAt
  have hpost := (Coeff.reCLM 2).hasFDerivAt.comp 0 hpre
  have hd : (Coeff.reCLM 2).comp (D.comp S) =
      (2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2) := by
    ext a n
    change ((fderiv ℂ F 0) (S a) n).re = 2*a n
    rw [fderiv_sourceSignedGapSequence_zero_apply]
    simp [S]
    ring
  rw [hd] at hpost
  exact hpost

/-- The actual real-coordinate signed-gap map has a two-sided analytic local inverse at zero. -/
theorem exists_symmetricSourceSignedGap_localInverse_zero :
    ∃ G : RealCoeff 2 → RealCoeff 2, AnalyticAt ℝ G 0 ∧ G 0 = 0 ∧
      (∀ᶠ a in 𝓝 (0 : RealCoeff 2),
        G (symmetricSourceSignedGapMap (by simp) (by norm_num) a) = a) ∧
      (∀ᶠ b in 𝓝 (0 : RealCoeff 2),
        symmetricSourceSignedGapMap (by simp) (by norm_num) (G b) = b) ∧
      fderiv ℝ G 0 = (1/2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2) := by
  let F := symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)
  let e : RealCoeff 2 ≃L[ℝ] RealCoeff 2 := {
    LinearEquiv.smulOfNeZero ℝ (RealCoeff 2) (2 : ℝ) (by norm_num) with
    continuous_toFun := continuous_const_smul (2 : ℝ)
    continuous_invFun := continuous_const_smul (2 : ℝ)⁻¹ }
  have he : e.toContinuousLinearMap = (2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2) := by
    ext a
    rfl
  have hei : e.symm.toContinuousLinearMap = (1/2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2) := by
    apply ContinuousLinearMap.ext
    intro a
    change (2 : ℝ)⁻¹ • a = (1/2 : ℝ) • a
    rw [one_div]
  have hF := analyticAt_symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num) 0
  have hzero : F 0 = 0 := symmetricSourceSignedGapMap_zero
  have hd : fderiv ℝ F 0 = e.toContinuousLinearMap :=
    hasFDerivAt_symmetricSourceSignedGapMap_zero.fderiv.trans he.symm
  have hs : HasStrictFDerivAt F e.toContinuousLinearMap 0 := by
    have h := hF.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
    rw [hd] at h
    exact h
  let P := hs.toOpenPartialHomeomorph F
  have hP : (P : RealCoeff 2 → RealCoeff 2) = F := hs.toOpenPartialHomeomorph_coe
  have hG : AnalyticAt ℝ P.symm (F 0) := by
    have h := P.analyticAt_symm' hs.mem_toOpenPartialHomeomorph_source
      (by rw [hP]; exact hF) (i := e) (by rw [hP]; exact hd)
    rw [hP] at h
    exact h
  refine ⟨hs.localInverse _ _ _,?_,?_,hs.eventually_left_inverse,?_,?_⟩
  · simpa only [hzero] using! hG
  · simpa only [hzero] using hs.localInverse_apply_image
  · simpa only [hzero] using hs.eventually_right_inverse
  · have h := hs.to_localInverse.hasFDerivAt.fderiv
    simpa only [hzero,hei] using h

/-- Every sufficiently small real signed-gap sequence is realized by an actual symmetric Hilbert source. -/
theorem exists_small_symmetric_signed_gap_realization :
    ∃ ε : ℝ, 0 < ε ∧ ∀ b : RealCoeff 2, ‖b‖ < ε →
      ∃ φ : realTypeSourceSubmodule 2, realSourceSpatialReflection φ = φ ∧ ∀ n,
        sourceSignedGapSequence (by simp) (by norm_num) φ.val n = (b n : ℂ) := by
  obtain ⟨G,_,_,_,hr,_⟩ := exists_symmetricSourceSignedGap_localInverse_zero
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hr
  refine ⟨ε,hε,fun b hb => ?_⟩
  let φ := symmetricRealSourceCoefficients 2 (G b)
  have hmap := hball (show b ∈ Metric.ball (0 : RealCoeff 2) ε by simpa [Metric.mem_ball,dist_eq_norm] using hb)
  refine ⟨φ,symmetricRealSourceCoefficients_reflection_fixed (G b),fun n => ?_⟩
  apply Complex.ext
  · exact congrArg (fun a : RealCoeff 2 => a n) hmap
  · simpa only [ofReal_im] using sourceSignedGapSequence_im_eq_zero (by simp) (by norm_num) φ n

/-- Every sufficiently small nonnegative Hilbert gap sequence occurs as the literal actual
periodic gap sequence of a reflection-symmetric real source. -/
theorem exists_small_symmetric_periodic_gap_realization :
    ∃ ε : ℝ, 0 < ε ∧ ∀ γ : RealCoeff 2, ‖γ‖ < ε → (∀ n, 0 ≤ γ n) →
      ∃ φ : realTypeSourceSubmodule 2, realSourceSpatialReflection φ = φ ∧ ∀ n,
        canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
          (periodOnePotential_mem _) n = (γ n : ℂ) := by
  obtain ⟨ε,hε,hrealize⟩ := exists_small_symmetric_signed_gap_realization
  refine ⟨ε,hε,fun γ hγ hnonneg => ?_⟩
  obtain ⟨φ,hφ,he⟩ := hrealize γ hγ
  refine ⟨φ,hφ,fun n => ?_⟩
  apply Complex.ext
  · have h := abs_sourceSignedGapSequence_re_of_reflection_fixed (by simp) (by norm_num) φ hφ n
    rw [he n,ofReal_re,abs_of_nonneg (hnonneg n)] at h
    exact h.symm
  · have h := canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) _
      (periodOnePotential_mem _) (isRealType_periodOnePotential φ.val φ.property) n
    simp only [canonicalPeriodicGap,sub_im,h.1,h.2,sub_self,ofReal_im]

end NLS.ZakharovShabat
