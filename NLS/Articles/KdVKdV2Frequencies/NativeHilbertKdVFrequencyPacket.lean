import NLS.KdV.HillHminusOnePhysicalHilbertFrequencyPacket
import NLS.KdV.HillRoughScalarAgreement
import NLS.Articles.KdVKdV2Frequencies.LocalWeakKdVActionFrequency

/-! The actual KdV correction divided by its own positive index is ONE
bounded Banach-analytic ell2 packet on a common complex rough ball.
It recovers the independent physical Hamiltonian frequencies and is
isospectral on the entire real mean-zero rough ball. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_native_hilbert_kdv_frequency_packet_near_zero (D : GlobalRoughAbelianForwardData) :
    ∃ δ K : ℝ, ∃ F : PeriodOneHminusOne → NLS.Coeff 2,
      0<δ ∧ 0<K ∧ AnalyticOnNhd ℂ F (ball (0 : PeriodOneHminusOne) δ) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) δ, ‖F q‖≤K ∧ ∀ j : ℤ, j≤0 → F q j=0) ∧
      (∀ q∈ball (0 : PeriodOneHminusOne) δ, ∀ p∈ball (0 : PeriodOneHminusOne) δ,
        IsRealPeriodOneHminusOne q → IsRealPeriodOneHminusOne p → q.val 0=0 → p.val 0=0 →
        hillHminusDiscriminant p=hillHminusDiscriminant q → F p=F q) ∧
      ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        nativeHillSource 1 q.val∈ball (0 : PeriodOneHminusOne) δ → ∀ n : ℕ+,
          F (nativeHillSource 1 q.val) (n : ℤ)=
            ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
  obtain ⟨δ₀,K,F,hδ₀,hK,hF,hbound,hphys⟩ := exists_hillOriginal_hilbert_analytic_frequency_packet
  obtain ⟨δ₁,G,hδ₁,hG,hinv,hnativeG⟩ := D.exists_native_kdv_isospectral_rough_extension_near_zero
  obtain ⟨δ₂,_,hδ₂,_,hnativeM⟩ := D.exists_native_kdv_original_moment_frequency_near_zero
  let δ := min δ₀ (min δ₁ δ₂)
  have hδ : 0<δ := lt_min hδ₀ (lt_min hδ₁ hδ₂)
  have hsub0 : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₀ := ball_subset_ball (min_le_left _ _)
  have hsub1 : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₁ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hsub2 : ball (0 : PeriodOneHminusOne) δ⊆ball 0 δ₂ :=
    ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hrec (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)))
      (hq : nativeHillSource 1 q.val∈ball (0 : PeriodOneHminusOne) δ) (n : ℕ+) :
      F (nativeHillSource 1 q.val) (n : ℤ)=
        ((D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3)/(n : ℂ) := by
    let p := nativeHillPhysicalSource 1 q.val q.property.1
    have hp : hillOriginalHminusSource p.val=nativeHillSource 1 q.val := by
      rw [hillOriginalHminusSource_eq_physical]
      exact (nativeHillSource_eq_physical 1 q.val q.property.1).symm
    have he := (hphys p (by rw [hp];exact hsub0 hq) n).2
    rw [hp] at he
    exact he.trans (congrArg (fun z : ℂ => z/(n : ℂ)) (hnativeM q (hsub2 hq) n).2.2.symm)
  have heq (n : ℕ+) (q : PeriodOneHminusOne) (hqr : IsRealPeriodOneHminusOne q)
      (hqm : q.val 0=0) (hq : q∈ball (0 : PeriodOneHminusOne) δ) : F q (n : ℤ)=G n q/(n : ℂ) := by
    apply hillRoughScalar_eq_of_native_agreement δ (fun q => F q (n : ℤ)) (fun q => G n q/(n : ℂ))
      (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).continuous).comp_continuousOn (hF.mono hsub0).continuousOn)
      (fun q hq => (((hG n).mono hsub1 q hq).div_const).continuousAt.continuousWithinAt) ?_ q hqr hqm hq
    intro u hu
    rw [hrec u hu n,hnativeG u (hsub1 hu) n]
  refine ⟨δ,K,F,hδ,hK,hF.mono hsub0,(fun q hq => hbound q (hsub0 hq)),?_,hrec⟩
  intro q hq p hp hqr hpr hqm hpm htrace
  ext j
  by_cases hj : 0<j
  · let n := positiveIntegerIndex j hj
    have hnj : (n : ℤ)=j := positiveIntegerIndex_int j hj
    rw [←hnj,heq n p hpr hpm hp,heq n q hqr hqm hq,hinv q (hsub1 hq) p (hsub1 hp) hqr hpr htrace n]
  · rw [(hbound p (hsub0 hp)).2 j (by omega),(hbound q (hsub0 hq)).2 j (by omega)]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
