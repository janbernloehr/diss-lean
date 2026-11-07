import NLS.Articles.KdVKdV2Frequencies.DiagonalPairActionInvariance
import NLS.SequenceSpaces.RealSequenceActionDescent
import NLS.SequenceSpaces.RealActionLifting

/-! Actual diagonal Hilbert symbols descend to complex action balls
at every real pair, with the whole vector bound and real lifts retained. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.KdV NLS.ZakharovShabat
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairChart
variable {D : GlobalRoughAbelianForwardData} {I : PeriodOneHminusOne → BaseActionSpace} {t : ℝ}

theorem exists_action_ball (P : DiagonalFrequencyPairChart D I t)
    (Ω : Set PeriodOneHminusOne) (hΩ : {q | IsRealPeriodOneHminusOne q}⊆Ω)
    (hI : AnalyticOnNhd ℂ I Ω)
    (hrec : ∀ q (hr : IsRealPeriodOneHminusOne q) (n : ℕ+),
      (I q).val (actionIndexEquiv.symm n)=hillHminusRealGapContourMoment q hr n 0)
    (z0 : Coeff 2 × Coeff 2) (hz0 : z0∈P.domain) (hzreal : z0∈Coeff.realPairLocus 2) :
    ∃ δ : ℝ, ∃ g : Coeff 1 → Coeff 2, 0<δ ∧
      AnalyticOnNhd ℂ g (ball (quadraticActionsExponent (q := 1) z0) δ) ∧
      (∀ b∈ball (quadraticActionsExponent (q := 1) z0) δ, ‖g b‖≤P.bound) ∧
      (∀ b∈ball (quadraticActionsExponent (q := 1) z0) δ, ∀ j : ℤ, j≤0 → g b j=0) ∧
      g (quadraticActionsExponent (q := 1) z0)=P.packet z0 ∧
      ∀ b∈ball (quadraticActionsExponent (q := 1) z0) δ, b∈Coeff.nonnegativeLocus 1 →
        ∃ z : Coeff 2 × Coeff 2, z∈P.domain ∧ z∈Coeff.realPairLocus 2 ∧
          quadraticActionsExponent (q := 1) z=b ∧ g b=P.packet z := by
  obtain ⟨Z,T,g,hZ,hzZ,hZU,hT,himage,hg,hbound,hrecg⟩ :=
    Coeff.exists_real_sequence_action_chart (p := 2) (q := 1) (r := 2) (by norm_num)
      P.packet P.domain P.domain_open P.analytic_packet
      (fun z hz w hw hzr hwr ha => P.packet_eq_of_real_actions Ω hΩ hI hrec z hz w hw hzr hwr ha)
      z0 hz0 hzreal P.bound P.norm_packet
  have haT : quadraticActionsExponent (q := 1) z0∈T := by rw [←himage];exact mem_image_of_mem _ hzZ
  obtain ⟨δ0,hδ0,hballT⟩ := Metric.isOpen_iff.mp hT (quadraticActionsExponent (q := 1) z0) haT
  obtain ⟨δ1,hδ1,hlift⟩ := Coeff.exists_ball_real_quadraticActions_lifts (p := 2) (q := 1)
    (by norm_num) z0 hzreal Z hZ hzZ
  let δ := min δ0 δ1
  have hδ : 0<δ := lt_min hδ0 hδ1
  have hsub : ball (quadraticActionsExponent (q := 1) z0) δ⊆T :=
    (ball_subset_ball (min_le_left _ _)).trans hballT
  refine ⟨δ,g,hδ,hg.mono hsub,(fun b hb => hbound b (hsub hb)),?_,hrecg z0 hzZ,?_⟩
  · intro b hb j hj
    have hi : b∈quadraticActionsExponent (q := 1) '' Z := by rw [himage];exact hsub hb
    obtain ⟨z,hz,rfl⟩ := hi
    rw [hrecg z hz]
    exact P.nonpositive z (hZU hz) j hj
  · intro b hb hbr
    obtain ⟨z,hz,hzb⟩ := hlift ⟨ball_subset_ball (min_le_right _ _) hb,hbr⟩
    exact ⟨z,hZU hz.1,hz.2,hzb,by rw [←hzb,hrecg z hz.1]⟩

end NLS.Articles.KdVKdV2Frequencies.DiagonalFrequencyPairChart
