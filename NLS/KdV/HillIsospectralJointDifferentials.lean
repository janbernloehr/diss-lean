import NLS.KdV.HillIsospectralPhysicalDifferentials

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

/-- Joint energy/source analytic extensions of the actual selected
physical numerators with zero isospectral source variation at every energy. -/
theorem exists_hillAbelianSelectedGlobalPsi_joint_isospectral_extension
    (n : ℕ) (hn : 1≤n) :
    ∃ G : ℂ × Coeff 2 → ℂ,
      (∀ E : ℂ, AnalyticAt ℂ G (E,SpectralWeight.one.toCoeff q)) ∧
      (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E) ∧
      ∀ h : Coeff 2,
        (∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) →
        ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => G (E,b)) (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨N,B,D,δ,hN,_,_,hc,hδ,hsource,hcharts⟩ :=
    exists_hillMixedNormalizedComplexPsi_common_isospectral_germs q hq hr h0q h0r
  obtain ⟨U,hU,hpU,hLow⟩ := exists_hillAbelianComplexPeriods_common_finite_neighborhood q hq hr N
  have hpB : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B := hsource (mem_ball_self hδ)
  have hp : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hpB).le
  obtain ⟨a,ha,ha0,hzero,_,hflat⟩ := hcharts n hn
  have hOwnJoint : AnalyticAt ℂ (hillMixedOwnComplexPeriod q hq hr h0q h0r N n)
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillMixedOwnComplexPeriod q hq hr h0q h0r N n hn B D hc (U ∩ ball 0 B)
      (hU.inter isOpen_ball) inter_subset_right (by
        intro k hk hkN
        exact (hLow k k hk hkN).mono (prod_mono_right inter_subset_left)))
      _ ⟨mem_univ _,hpU,hpB⟩
  have haBase : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) := ha _ (mem_ball_self hδ)
  have hOwn : AnalyticAt ℂ (fun p : Coeff 2 => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p))
      (SpectralWeight.one.toCoeff q) :=
    hOwnJoint.comp (f := fun p : Coeff 2 => (a p,p)) (haBase.prod analyticAt_id)
  have hne : hillMixedOwnComplexPeriod q hq hr h0q h0r N n
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q)≠0 := by
    rw [ha0]
    exact hillMixedOwnComplexPeriod_selected_ne_zero q hq hr h0q h0r N n hN hn B D hc hp
  let G : ℂ × Coeff 2 → ℂ := fun t => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a t.2,t.2) t.1
  refine ⟨G,?_,?_,hflat⟩
  · intro E
    have haa : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => a t.2) (E,SpectralWeight.one.toCoeff q) := haBase.comp (x := (E,SpectralWeight.one.toCoeff q)) (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd
    have hnum := (analyticOnNhd_hillAbelianHilbertPsi n (E,a (SpectralWeight.one.toCoeff q)) (mem_univ _)).comp
      (f := fun t : ℂ × Coeff 2 => (t.1,a t.2)) (analyticAt_fst.prod haa)
    have hden : AnalyticAt ℂ (fun t : ℂ × Coeff 2 => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a t.2,t.2)) (E,SpectralWeight.one.toCoeff q) := hOwn.comp (x := (E,SpectralWeight.one.toCoeff q)) (f := fun t : ℂ × Coeff 2 => t.2) analyticAt_snd
    exact hnum.div hden hne
  · have hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
        hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with p hpδ
      exact hzero p hpδ
    have hm := hillMixedNormalizedComplexPsi_eventually_physical_of_zero_periods q hq hr h0q h0r N n hN hn B D hc hpB a hOwn hne hz
    filter_upwards [hm] with p hpReal
    exact congrFun hpReal

end NLS.KdV
