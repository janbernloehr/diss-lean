import NLS.KdV.HillUnitRealSourceUnembed

/-! # Original physical real germs determine native complex L2 germs -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem eventuallyEq_native_of_physical_real_germ
    (F G : Coeff 2 → ℂ) (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0)
    (he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩,
      F (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))=
        G (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))) :
    F =ᶠ[𝓝 (0 : Coeff 2)] G := by
  let S := {u : Coeff 2 // periodOneL2Conjugation u=u}
  let z : S := ⟨0,periodOneL2Conjugation_zero⟩
  let L : S → RealPeriodOneHillPotential := fun u =>
    hillRealWeightedEmbedding SpectralWeight.one (hillUnitRealSourceLift u.val u.property)
  have hL : Continuous L := by
    apply (continuous_hillRealWeightedEmbedding SpectralWeight.one).comp
    apply Continuous.subtype_mk
    exact hillUnitSourceLift.continuous.comp continuous_subtype_val
  have hL0 : L z = ⟨0,h0q,h0r⟩ := by
    apply Subtype.ext
    change hillPeriodOneUnitPotential SpectralWeight.one (hillUnitSourceLift 0)=0
    simp only [hillUnitSourceLift,map_zero,hillPeriodOneUnitPotential]
  have ht : Tendsto L (𝓝 z) (𝓝 (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)) := by
    rw [← hL0]
    exact hL.tendsto z
  have hreal : ∀ᶠ u : S in 𝓝 z, F u.val=G u.val := by
    filter_upwards [ht.eventually he] with u hu
    simpa only [L,hillRealWeightedEmbedding_toCoeff,hillUnitRealSourceLift_toCoeff,
      hillUnitSample_periodDouble] using hu
  obtain ⟨r,hr,hrealball⟩ := Metric.mem_nhds_iff.mp hreal
  obtain ⟨s,hs,hball⟩ := Metric.mem_nhds_iff.mp
    ((hF.eventually_analyticAt.and hG.eventually_analyticAt).and (ball_mem_nhds (0 : Coeff 2) hr))
  have hFa : AnalyticOnNhd ℂ F (ball 0 s) := fun u hu => (hball hu).1.1
  have hGa : AnalyticOnNhd ℂ G (ball 0 s) := fun u hu => (hball hu).1.2
  have hident := periodOneL2_real_form_identity isOpen_ball isPreconnected_ball (mem_ball_self hs)
    F G hFa hGa (by
      intro u hu hJu
      apply hrealball (show (⟨u,hJu⟩ : S) ∈ ball z r from ?_)
      simpa only [mem_ball,Subtype.dist_eq,z] using (hball hu).2)
  exact mem_of_superset (ball_mem_nhds 0 hs) hident

end NLS.KdV
