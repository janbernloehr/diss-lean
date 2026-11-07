import NLS.Articles.KdVKdV2Frequencies.OffDiagonalActionCharts
import NLS.Articles.KdVKdV2Frequencies.IntermediateFrequencyRawTargets
import NLS.SequenceSpaces.CompactWeightedPacketPullback

/-! The actual off-diagonal correction has compact ACTION derivatives
in the original weighted ell1 norm near every positive action point.
The diagonal term and the full corrected derivative remain separate. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem OffDiagonalFrequencyPairChart.exists_raw_compact_action_germ
    {D : GlobalRoughAbelianForwardData} {β t ε : ℝ}
    (P : OffDiagonalFrequencyPairChart D β t ε) (hε : 0<ε)
    (α : ℝ) (hα : -β=α) (z0 : Coeff 2 × Coeff 2)
    (hz0 : z0∈P.domain) (hzreal : z0∈Coeff.realPairLocus 2)
    (a0 : WeightedCoeff (Weight.sobolev α) 1)
    (ha0 : sobolevActionEnumeration α a0=quadraticActionsExponent (q := 1) z0) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1),
      ∃ G : WeightedCoeff (Weight.sobolev α) 1 → WeightedCoeff (Weight.sobolev α) 1,
        IsOpen U ∧ a0∈U ∧ AnalyticOnNhd ℂ G U ∧
        (∀ a∈U, ∀ j : ℤ, j≤0 → (G a).val j=0) ∧
        (∀ n : ℕ+, (G a0).val (n : ℤ)=P.correction n z0) ∧
        (∀ a∈U, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1 →
          ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
            quadraticActionsExponent (q := 1) z=sobolevActionEnumeration α a ∧
            ∀ n : ℕ+, (G a).val (n : ℤ)=P.correction n z) ∧
        ∀ a∈U, IsCompactOperator (fderiv ℂ G a) := by
  obtain ⟨δ,g,hδ,hg,_hgn,hgz,hgc,hlift⟩ := P.exists_action_ball z0 hz0 hzreal
  let N := sobolevActionEnumeration α
  have hc : N a0∈ball (quadraticActionsExponent (q := 1) z0) δ := by
    rw [ha0]
    exact mem_ball_self hδ
  obtain ⟨U,G,hU,haU,hUV,hG,hraw,hcompact⟩ := exists_compact_weighted_packet_pullback
    β ε hε α hα N (ball (quadraticActionsExponent (q := 1) z0) δ) g isOpen_ball hg a0 hc
  refine ⟨U,G,hU,haU,hG,?_,?_,?_,hcompact⟩
  · intro a ha j hj
    rw [hraw a ha j,hgz _ (hUV a ha) j hj,zero_div]
  · intro n
    rw [hraw a0 haU (n : ℤ),ha0,hgc,P.positive z0 hz0 n,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    rfl
  · intro a ha hapos
    obtain ⟨z,hz,hzr,hQ,hgp⟩ := hlift (N a) (hUV a ha)
      (sobolevActionEnumeration_nonnegative α a hapos.1)
    refine ⟨z,hz,hzr,hQ,?_⟩
    intro n
    rw [hraw a ha (n : ℤ),hgp,P.positive z hz n,
      mul_div_cancel_left₀ _ (Weight.complex_ne_zero _ _)]
    rfl

theorem GlobalRoughAbelianForwardData.exists_local_offDiagonal_compact_action_germ
    (D : GlobalRoughAbelianForwardData) (β t : ℝ)
    (hβ : 0<β) (hβ1 : β<1) (ht : 0<t) (hβt : 2*t=1-β)
    (α : ℝ) (hα : -β=α) (a0 : WeightedCoeff (Weight.sobolev α) 1)
    (ha0 : a0∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1) :
    ∃ ε : ℝ, 0<ε ∧ ε<β ∧ ∃ P : OffDiagonalFrequencyPairChart D β t ε,
      ∃ z0 : Coeff 2 × Coeff 2, z0∈P.domain ∧ z0∈Coeff.realPairLocus 2 ∧
        quadraticActionsExponent (q := 1) z0=sobolevActionEnumeration α a0 ∧
        ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1),
          ∃ G : WeightedCoeff (Weight.sobolev α) 1 → WeightedCoeff (Weight.sobolev α) 1,
            IsOpen U ∧ a0∈U ∧ AnalyticOnNhd ℂ G U ∧
            (∀ a∈U, ∀ j : ℤ, j≤0 → (G a).val j=0) ∧
            (∀ n : ℕ+, (G a0).val (n : ℤ)=P.correction n z0) ∧
            (∀ a∈U, a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1 →
              ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
                quadraticActionsExponent (q := 1) z=sobolevActionEnumeration α a ∧
                ∀ n : ℕ+, (G a).val (n : ℤ)=P.correction n z) ∧
            ∀ a∈U, IsCompactOperator (fderiv ℂ G a) := by
  obtain ⟨z0,hzr,hQ,_hz2⟩ := Coeff.exists_real_quadraticActions_lift (p := 2) (q := 1)
    (by norm_num) (sobolevActionEnumeration α a0) (sobolevActionEnumeration_nonnegative α a0 ha0.1)
  obtain ⟨ε,hε,hεβ,P,hzP⟩ := exists_offDiagonalFrequencyPairChart D β t hβ hβ1 ht hβt z0 hzr
  refine ⟨ε,hε,hεβ,P,z0,hzP,hzr,hQ,?_⟩
  exact P.exists_raw_compact_action_germ hε α hα z0 hzP hzr a0 hQ.symm

end NLS.Articles.KdVKdV2Frequencies
