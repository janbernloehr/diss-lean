import NLS.KdV.HillHminusActionAmplitudeDifferentials
import NLS.KdV.HillHminusActionGardner
import NLS.KdV.HillHminusEndpointPhaseGardner
import NLS.KdV.HillHminusPhysicalGermBrackets
import NLS.Poisson.HminusGardnerAmplitudeProducts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem exists_hillOriginal_full_phase_hminus_physical_germ
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    ∃ P : PeriodOneHminusOne → ℂ,
      AnalyticAt ℂ P (hillOriginalHminusSource q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        P (hillOriginalHminusSource p.val) = hillOriginalFullPhaseFactor n p := by
  obtain ⟨ε,hε,P,hP,hPM⟩ :=
    HillHminusPsiChart.exists_hillOriginal_fullPhaseFactor_hminus_analytic_open q n hgap
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 q) (𝓝 (hillOriginalHminusSource q.val)) :=
    (hillOriginalHminusSource.continuous.comp continuous_subtype_val).continuousAt
  exact ⟨P,hP _ (mem_ball_self hε),
    Filter.Eventually.mono (ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hε)))
      (fun p hp => hPM p hp)⟩

/-- At every all-periodic original source the original Cartesian
coordinates Poisson commute under the GENUINE H-minus-one Gardner bracket.
Only the two selected gaps must be open; every other gap may be collapsed. -/
theorem hillOriginalCartesians_hminus_Gardner_endpoint_zero
    (q : RealPeriodOneHillPotential) (n m : ℕ+)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1 ≤ k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk = 0)
    (Z W : PeriodOneHminusOne → ℂ)
    (hZ : AnalyticAt ℂ Z (hillOriginalHminusSource q.val))
    (hW : AnalyticAt ℂ W (hillOriginalHminusSource q.val))
    (hZM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      Z (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos)
    (hWM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      W (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 m m.pos) :
    NLS.Poisson.hminusGardnerBracket Z W (hillOriginalHminusSource q.val) = 0 := by
  by_cases hnm : (n:ℕ) = (m:ℕ)
  · have he : n=m := Subtype.ext hnm
    subst m
    have heq := hillHminusPhysicalGerm_fderiv_eq_of_eventuallyEq q Z W hZ hW (by
      filter_upwards [hZM,hWM] with p hp hw
      exact hp.trans hw.symm)
    unfold NLS.Poisson.hminusGardnerBracket NLS.Poisson.hminusScalarGradient
    rw [heq]
    exact NLS.Poisson.gardnerBivector_self _
  · obtain ⟨J,A,hJ,hA,hJM,hAM,hAn,hDA⟩ :=
      exists_hillOriginal_action_amplitude_hminus_differentials q n hgapn
    obtain ⟨K,B,hK,hB,hKM,hBM,hBn,hDB⟩ :=
      exists_hillOriginal_action_amplitude_hminus_differentials q m hgapm
    obtain ⟨P,hP,hPM⟩ := exists_hillOriginal_full_phase_hminus_physical_germ q n hgapn
    obtain ⟨Q,hQ,hQM⟩ := exists_hillOriginal_full_phase_hminus_physical_germ q m hgapm
    let F : PeriodOneHminusOne → ℂ := fun a => A a * P a
    let G : PeriodOneHminusOne → ℂ := fun a => B a * Q a
    have hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val) := hA.mul hP
    have hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val) := hB.mul hQ
    have hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        F (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 n n.pos := by
      filter_upwards [hAM,hPM] with p ha hp
      dsimp only [F]
      rw [ha,hp]
      simp only [hillSpectralCartesian,hillOriginalFullPhaseFactor,mul_assoc]
    have hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        G (hillOriginalHminusSource p.val) = hillSpectralCartesian p.val p.property.1 p.property.2 m m.pos := by
      filter_upwards [hBM,hQM] with p hb hq
      dsimp only [G]
      rw [hb,hq]
      simp only [hillSpectralCartesian,hillOriginalFullPhaseFactor,mul_assoc]
    have hFK : NLS.Poisson.hminusGardnerBracket F K (hillOriginalHminusSource q.val) = 0 := by
      simpa only [if_neg (Ne.symm hnm),mul_zero,zero_mul] using
        hillOriginalCartesian_action_hminus_Gardner_eq q n m F K hF hK hFM hKM
    have hGJ : NLS.Poisson.hminusGardnerBracket G J (hillOriginalHminusSource q.val) = 0 := by
      simpa only [if_neg hnm,mul_zero,zero_mul] using
        hillOriginalCartesian_action_hminus_Gardner_eq q m n G J hG hJ hGM hJM
    have hFG : NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) = 0 :=
      NLS.Poisson.hminusGardnerBracket_amplitude_products_zero A P B Q J K _ _ _
        hA.differentiableAt hP.differentiableAt hB.differentiableAt hQ.differentiableAt hDA hDB hAn hBn
        (hillOriginalActions_hminus_Gardner_commute q n m J K hJ hK hJM hKM)
        (hillOriginalFullPhases_hminus_Gardner_endpoint_zero q n m hgapn hgapm hterminal P Q hP hQ hPM hQM)
        hFK hGJ
    rw [hillHminusPhysicalGerm_Gardner_eq_of_eventuallyEq q Z W F G hZ hW hF hG
      (by filter_upwards [hZM,hFM] with p hp hf; exact hp.trans hf.symm)
      (by filter_upwards [hWM,hGM] with p hp hg; exact hp.trans hg.symm)]
    exact hFG

end NLS.KdV
