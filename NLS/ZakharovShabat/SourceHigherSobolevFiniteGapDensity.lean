import NLS.ZakharovShabat.SourceHigherSobolevEmbedding
import NLS.ZakharovShabat.NormalizedWeightedClosingApproximation

/-! # Actual finite-gap density in Hˢ

The weighted spectral closing inverse gives nearby real finite-gap sources
in normalized coordinates. The continuous inverse coordinate map transfers
the approximation to the original Hˢ norm, with the same physical operator
and canonical gaps. This is stronger than unweighted Fourier-Lebesgue density.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ZakharovShabat
variable (s : ℕ)

/-- Real original Hˢ sources, with their Hˢ topology. -/
abbrev realTypeHigherSobolevSourceLocus :=
  {a : SobolevSource s // IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s a))}

/-- Hˢ sources whose original canonical spectral gaps have finite support. -/
def sourceHigherSobolevFiniteGapLocus : Set (realTypeHigherSobolevSourceLocus s) :=
  {a | (⟨higherSobolevSourceInclusion s a.val, a.property⟩ : realTypeSourceLocus 2)
    ∈ sourceFiniteGapLocus (by simp) (by norm_num)}

/-- Every real Hˢ source can be approximated by actual real finite-gap sources in Hˢ norm. -/
theorem exists_sourceHigherSobolevFiniteGap_norm_sub_lt
    (a : realTypeHigherSobolevSourceLocus s) (ε : ℝ) (hε : 0 < ε) :
    ∃ b ∈ sourceHigherSobolevFiniteGapLocus s, ‖b.val-a.val‖ < ε := by
  let E := higherSobolevNormalizedCoordinates s
  let w := SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s)
  have hr : IsRealType (CoeffPair.toMax 2 (E a.val)) :=
    (higherSobolevNormalizedCoordinates_realType_iff s a.val).mpr a.property
  have hn : E.symm ⁻¹' ball a.val ε ∈ 𝓝 (E a.val) := by
    apply E.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using ball_mem_nhds a.val hε
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp hn
  obtain ⟨N,_,ψ,hψ,hclose,_,hclosed⟩ :=
    exists_real_normalizedWeightedClosingApproximation (by simp) (by norm_num) w (E a.val) hr δ hδ
  let b := E.symm ψ
  have hcoord : higherSobolevNormalizedCoordinates s b = ψ := E.apply_symm_apply ψ
  have hb : IsRealType (CoeffPair.toMax 2 (higherSobolevSourceInclusion s b)) :=
    (higherSobolevNormalizedCoordinates_realType_iff s b).mp (by rw [hcoord]; exact hψ)
  refine ⟨⟨b,hb⟩,?_,?_⟩
  · have hf := normalizedWeightedSource_finiteGap_of_closed (by simp) (by norm_num) w ψ hψ N hclosed
    have he : normalizedWeightedSource w ψ = higherSobolevSourceInclusion s b := by
      rw [← hcoord]
      rfl
    change (⟨higherSobolevSourceInclusion s b,hb⟩ : realTypeSourceLocus 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num)
    simpa only [he] using hf
  · have hψball : ψ ∈ ball (E a.val) δ := by
      simpa only [mem_ball,dist_eq_norm] using hclose
    have hbball := hδball hψball
    simpa only [mem_preimage,mem_ball,dist_eq_norm] using hbball

/-- Actual real spectral finite-gap sources are dense in the original Hˢ topology. -/
theorem dense_sourceHigherSobolevFiniteGapLocus : Dense (sourceHigherSobolevFiniteGapLocus s) := by
  apply Metric.dense_iff.mpr
  intro a ε hε
  obtain ⟨b,hb,hclose⟩ := exists_sourceHigherSobolevFiniteGap_norm_sub_lt s a ε hε
  exact ⟨b,by simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hclose,hb⟩

/-- Hˢ finite-gap approximation can preserve any prescribed open condition. -/
theorem exists_sourceHigherSobolevFiniteGap_mem_open
    (U : Set (realTypeHigherSobolevSourceLocus s)) (hU : IsOpen U)
    (a : realTypeHigherSobolevSourceLocus s) (ha : a ∈ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ b ∈ sourceHigherSobolevFiniteGapLocus s, b ∈ U ∧ ‖b.val-a.val‖ < ε := by
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ha)
  obtain ⟨b,hb,hclose⟩ := exists_sourceHigherSobolevFiniteGap_norm_sub_lt s a
    (min ε r) (lt_min hε hr)
  refine ⟨b,hb,hrU ?_,hclose.trans_le (min_le_left _ _)⟩
  simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hclose.trans_le (min_le_right _ _)

/-- Continuous physical identities pass from actual finite-gap sources to all real Hˢ sources. -/
theorem eq_of_continuousOn_of_sourceHigherSobolevFiniteGap
    {U : Set (realTypeHigherSobolevSourceLocus s)} (hU : IsOpen U)
    {H : realTypeHigherSobolevSourceLocus s → ℂ} (hH : ContinuousOn H U) (c : ℂ)
    (hf : ∀ b ∈ U, b ∈ sourceHigherSobolevFiniteGapLocus s → H b = c)
    (a : realTypeHigherSobolevSourceLocus s) (ha : a ∈ U) : H a = c := by
  have hclosure : a ∈ closure (sourceHigherSobolevFiniteGapLocus s ∩ U) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨b,hb,hbU,hclose⟩ := exists_sourceHigherSobolevFiniteGap_mem_open s U hU a ha ε hε
    refine ⟨b,⟨hb,hbU⟩,?_⟩
    rw [Subtype.dist_eq,dist_eq_norm,norm_sub_rev]
    exact hclose
  exact ((hH a ha).mono inter_subset_right).eq_const_of_mem_closure hclosure
    (fun b hb => hf b hb.2 hb.1)

/-- Real spectral finite-gap approximants can be chosen as an Hˢ-convergent sequence. -/
theorem exists_sourceHigherSobolevFiniteGap_sequence (a : realTypeHigherSobolevSourceLocus s) :
    ∃ b : ℕ → realTypeHigherSobolevSourceLocus s,
      (∀ j, b j ∈ sourceHigherSobolevFiniteGapLocus s) ∧ Tendsto b atTop (𝓝 a) :=
  mem_closure_iff_seq_limit.mp (dense_sourceHigherSobolevFiniteGapLocus s a)

end NLS.ZakharovShabat
