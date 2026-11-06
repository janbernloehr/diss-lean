import NLS.KdV.HillPhysicalRealGermIdentity
import NLS.KdV.HillHminusOriginalSourceAdapter
import NLS.SequenceSpaces.PeriodOneHminusAnalyticContinuation

/-! # Physical real L2 scalar germs determine complex rough scalar germs -/
noncomputable section
set_option autoImplicit false
open Set Metric Filter Topology
namespace NLS.KdV

theorem eventuallyEq_rough_of_physical_real_germ
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (f g : PeriodOneHminusOne → ℂ) (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      f (hillOriginalHminusSource p.val)=g (hillOriginalHminusSource p.val)) :
    f =ᶠ[𝓝 0] g := by
  let F : Coeff 2 → ℂ := fun a => f (periodOneL2Inclusion a)
  let G : Coeff 2 → ℂ := fun a => g (periodOneL2Inclusion a)
  have hFa : AnalyticAt ℂ F 0 :=
    hf.comp_of_eq (periodOneL2Inclusion.analyticAt 0) (map_zero _)
  have hGa : AnalyticAt ℂ G 0 :=
    hg.comp_of_eq (periodOneL2Inclusion.analyticAt 0) (map_zero _)
  have hnative : F =ᶠ[𝓝 0] G :=
    eventuallyEq_native_of_physical_real_germ h0q h0r F G hFa hGa he
  obtain ⟨r,hr,hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨s,hs,hgs⟩ := hg.exists_ball_analyticOnNhd
  let η := min r s
  have hη : 0 < η := lt_min hr hs
  have hall := eqOn_periodOneHminus_ball_of_L2_germ η hη f g
    (hfr.mono (ball_subset_ball (min_le_left _ _)))
    (hgs.mono (ball_subset_ball (min_le_right _ _))) hnative
  filter_upwards [ball_mem_nhds (0 : PeriodOneHminusOne) hη] with q hq
  exact hall hq

end NLS.KdV
