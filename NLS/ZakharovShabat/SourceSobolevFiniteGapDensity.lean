import NLS.ZakharovShabat.SourceSobolevNormalizedCoordinates
import NLS.ZakharovShabat.NormalizedWeightedClosingApproximation

/-! # Actual finite-gap density in H¹

The weighted spectral closing inverse gives nearby real finite-gap sources
in normalized coordinates. The continuous inverse coordinate map transfers
the approximation to the original H¹ norm, with the same physical operator
and canonical gaps. This is stronger than unweighted Fourier-Lebesgue density.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ZakharovShabat

/-- Real original H¹ sources, with their H¹ topology. -/
abbrev realTypeSobolevSourceLocus :=
  {a : ScalarDomain 2 × ScalarDomain 2 // IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a))}

/-- H¹ sources whose original canonical spectral gaps have finite support. -/
def sourceSobolevFiniteGapLocus : Set realTypeSobolevSourceLocus :=
  {a | (⟨sobolevSourceInclusion a.val, a.property⟩ : realTypeSourceLocus 2)
    ∈ sourceFiniteGapLocus (by simp) (by norm_num)}

/-- Every real H¹ source can be approximated by actual real finite-gap sources in H¹ norm. -/
theorem exists_sourceSobolevFiniteGap_norm_sub_lt
    (a : realTypeSobolevSourceLocus) (ε : ℝ) (hε : 0 < ε) :
    ∃ b ∈ sourceSobolevFiniteGapLocus, ‖b.val-a.val‖ < ε := by
  let E := sobolevNormalizedCoordinates
  let w := SpectralWeight.sobolev 1 (by norm_num)
  have hr : IsRealType (CoeffPair.toMax 2 (E a.val)) :=
    (sobolevNormalizedCoordinates_realType_iff a.val).mpr a.property
  have hn : E.symm ⁻¹' ball a.val ε ∈ 𝓝 (E a.val) := by
    apply E.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ball_mem_nhds a.val hε
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨N,_,ψ,hψ,hclose,_,hclosed⟩ :=
    exists_real_normalizedWeightedClosingApproximation (by simp) (by norm_num) w (E a.val) hr δ hδ
  let b := E.symm ψ
  have hcoord : sobolevNormalizedCoordinates b = ψ := E.apply_symm_apply ψ
  have hb : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion b)) :=
    (sobolevNormalizedCoordinates_realType_iff b).mp (by rw [hcoord]; exact hψ)
  refine ⟨⟨b,hb⟩,?_,?_⟩
  · have hf := normalizedWeightedSource_finiteGap_of_closed (by simp) (by norm_num) w ψ hψ N hclosed
    have he : normalizedWeightedSource w ψ = sobolevSourceInclusion b := by
      rw [← hcoord]
      exact normalizedWeightedSource_sobolevNormalizedCoordinates b
    change (⟨sobolevSourceInclusion b,hb⟩ : realTypeSourceLocus 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num)
    simpa only [he] using hf
  · have hψball : ψ ∈ ball (E a.val) δ := by
      simpa only [mem_ball,dist_eq_norm] using hclose
    have hbball := hδball hψball
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hbball

/-- Actual real spectral finite-gap sources are dense in the original H¹ topology. -/
theorem dense_sourceSobolevFiniteGapLocus : Dense sourceSobolevFiniteGapLocus := by
  apply Metric.dense_iff.mpr
  intro a ε hε
  obtain ⟨b,hb,hclose⟩ := exists_sourceSobolevFiniteGap_norm_sub_lt a ε hε
  exact ⟨b,by simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hclose,hb⟩

/-- H¹ finite-gap approximation can preserve any prescribed open condition. -/
theorem exists_sourceSobolevFiniteGap_mem_open
    (U : Set realTypeSobolevSourceLocus) (hU : IsOpen U)
    (a : realTypeSobolevSourceLocus) (ha : a ∈ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ b ∈ sourceSobolevFiniteGapLocus, b ∈ U ∧ ‖b.val-a.val‖ < ε := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  obtain ⟨b,hb,hclose⟩ := exists_sourceSobolevFiniteGap_norm_sub_lt a
    (min ε r) (lt_min hε hr)
  refine ⟨b,hb,hrU ?_,hclose.trans_le (min_le_left _ _)⟩
  simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hclose.trans_le (min_le_right _ _)

/-- Continuous physical identities pass from actual finite-gap sources to all real H¹ sources. -/
theorem eq_of_continuousOn_of_sourceSobolevFiniteGap
    {U : Set realTypeSobolevSourceLocus} (hU : IsOpen U)
    {H : realTypeSobolevSourceLocus → ℂ} (hH : ContinuousOn H U) (c : ℂ)
    (hf : ∀ b ∈ U, b ∈ sourceSobolevFiniteGapLocus → H b = c)
    (a : realTypeSobolevSourceLocus) (ha : a ∈ U) : H a = c := by
  have hclosure : a ∈ closure (sourceSobolevFiniteGapLocus ∩ U) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨b,hb,hbU,hclose⟩ := exists_sourceSobolevFiniteGap_mem_open U hU a ha ε hε
    refine ⟨b,⟨hb,hbU⟩,?_⟩
    rw [Subtype.dist_eq,dist_eq_norm,norm_sub_rev]
    exact hclose
  exact ((hH a ha).mono inter_subset_right).eq_const_of_mem_closure hclosure
    (fun b hb => hf b hb.2 hb.1)

end NLS.ZakharovShabat
