import NLS.Articles.KdVKdV2Frequencies.OffDiagonalPairActionInvariance
import NLS.SequenceSpaces.RealSequenceActionDescent
import NLS.SequenceSpaces.RealActionLifting

/-! The genuine stronger off-diagonal packet descends near every real
pair, including zero actions. Surjectivity retains its full vector bound. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.OffDiagonalFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {β t ε : ℝ}

theorem exists_action_ball (P : OffDiagonalFrequencyPairChart D β t ε)
    (z0 : Coeff 2 × Coeff 2) (hz0 : z0∈P.domain) (hzreal : z0∈Coeff.realPairLocus 2) :
    ∃ ε : ℝ, ∃ g : Coeff 1 → Coeff 1, 0<ε ∧
      AnalyticOnNhd ℂ g (ball (quadraticActionsExponent (q := 1) z0) ε) ∧
      (∀ b∈ball (quadraticActionsExponent (q := 1) z0) ε, ‖g b‖≤P.bound) ∧
      (∀ b∈ball (quadraticActionsExponent (q := 1) z0) ε, ∀ j : ℤ, j≤0 → g b j=0) ∧
      g (quadraticActionsExponent (q := 1) z0)=P.packet z0 ∧
      ∀ b∈ball (quadraticActionsExponent (q := 1) z0) ε, b∈Coeff.nonnegativeLocus 1 →
        ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
          quadraticActionsExponent (q := 1) z=b ∧ g b=P.packet z := by
  obtain ⟨Z,T,g,hZ,hzZ,hZU,hT,himage,hg,hbound,hrec⟩ :=
    Coeff.exists_real_sequence_action_chart (p := 2) (q := 1) (r := 1) (by norm_num)
      P.packet P.domain P.domain_open P.analytic_packet
      (fun z hz w hw hzr hwr ha => P.packet_eq_of_real_actions z hz w hw hzr hwr ha)
      z0 hz0 hzreal P.bound P.norm_packet
  have haT : (quadraticActionsExponent (q := 1) z0)∈T := by rw [←himage];exact mem_image_of_mem _ hzZ
  obtain ⟨ε₀,hε₀,hballT⟩ := Metric.isOpen_iff.mp hT (quadraticActionsExponent (q := 1) z0) haT
  obtain ⟨ε₁,hε₁,hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (p := 2) (q := 1)
    (by norm_num) z0 hzreal Z hZ hzZ
  let ε := min ε₀ ε₁
  have hε : 0<ε := lt_min hε₀ hε₁
  have hsub : ball (quadraticActionsExponent (q := 1) z0) ε⊆T := (ball_subset_ball (min_le_left _ _)).trans hballT
  refine ⟨ε,g,hε,hg.mono hsub,(fun b hb => hbound b (hsub hb)),?_,hrec z0 hzZ,?_⟩
  · intro b hb j hj
    have hi : b∈quadraticActionsExponent (q := 1) '' Z := by rw [himage];exact hsub hb
    obtain ⟨z,hz,rfl⟩ := hi
    rw [hrec z hz]
    exact P.nonpositive z (hZU hz) j hj
  · intro b hb hbr
    obtain ⟨z,hz,hzb⟩ := hlift ⟨ball_subset_ball (min_le_right _ _) hb,hbr⟩
    exact ⟨z,hZU hz.1,hz.2,hzb,by rw [←hzb,hrec z hz.1]⟩


end NLS.Articles.KdVKdV2Frequencies.OffDiagonalFrequencyPairChart
