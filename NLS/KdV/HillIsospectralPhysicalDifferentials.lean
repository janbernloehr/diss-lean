import NLS.KdV.HillIsospectralNormalizedDifferentials
import NLS.KdV.HillMixedPeriodPhysicalMatching

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

/-- Actual mixed zero periods and a nonzero own normalization identify
the selected physical differential on nearby real sources. -/
theorem hillMixedNormalizedComplexPsi_eventually_physical_of_zero_periods
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D)
    (hpB : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B)
    (a : Coeff 2 → Coeff 2)
    (hOwn : AnalyticAt ℂ (fun p : Coeff 2 => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p))
      (SpectralWeight.one.toCoeff q))
    (hne : hillMixedOwnComplexPeriod q hq hr h0q h0r N n
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q)≠0)
    (hzero : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      hillMixedNormalizedComplexPsi q hq hr h0q h0r N n
        (a (SpectralWeight.one.toCoeff p.val),SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn := by
  obtain ⟨W,hW,hqW,hmatch⟩ := exists_hillMixedComplexPeriods_physical_neighborhood q hq hr h0q h0r N hN B D hc
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hown : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)≠0 :=
    hOwn.continuousAt.eventually_ne hne
  have ht : Tendsto P (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) (𝓝 (SpectralWeight.one.toCoeff q)) :=
    hP.continuousAt
  filter_upwards [hW.mem_nhds hqW,ht.eventually hown,ht.eventually hzero,
    ht.eventually (isOpen_ball.mem_nhds hpB)] with p hpW hpne hpzero hpball
  have hp : ‖P p‖≤B :=
    (show ‖P p‖<B by simpa only [mem_ball,dist_zero_right] using hpball).le
  have hoff := (hillMixedComplexPeriodSequence_eq_zero_iff_off_periods q hq hr h0q h0r N n hn (a (P p)) (P p)).mp hpzero
  apply hillMixedNormalizedComplexPsi_eq_selected_of_physical_periods q hq hr h0q h0r N n hn p (a (P p))
    (fun k hk => hmatch p hpW hp n k hk (a (P p))) hpne
  intro k hk
  rw [hillMixedNormalizedComplexPsi_period_eq_ratio q hq hr h0q h0r N n k (a (P p),P p)]
  by_cases hkn : k=n
  · subst k
    rw [if_pos rfl]
    change hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a (P p),P p)/
      hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a (P p),P p)=1
    exact div_self hpne
  · rw [if_neg hkn,hoff k hk hkn,zero_div]

/-- The stationary implicit normalized germs are genuine extensions of
the selected physical differentials on real-source neighborhoods, not
merely functions sharing a single base value. -/
theorem exists_hillMixedNormalizedComplexPsi_isospectral_physical_germs :
    ∃ N : ℕ, ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ a : Coeff 2 → Coeff 2,
        AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) ∧
        (∀ E : ℂ, AnalyticAt ℂ
          (fun p : Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p) E)
          (SpectralWeight.one.toCoeff q)) ∧
        (∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          hillMixedNormalizedComplexPsi q hq hr h0q h0r N n
            (a (SpectralWeight.one.toCoeff p.val),SpectralWeight.one.toCoeff p.val)=
              hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn) ∧
        ∀ h : Coeff 2,
          (∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) →
          ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p) E)
            (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨N,B,D,δ,hN,_,_,hc,hδ,hsource,hcharts⟩ :=
    exists_hillMixedNormalizedComplexPsi_common_isospectral_germs q hq hr h0q h0r
  obtain ⟨U,hU,hpU,hLow⟩ := exists_hillAbelianComplexPeriods_common_finite_neighborhood q hq hr N
  have hpB : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B := hsource (mem_ball_self hδ)
  have hp : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hpB).le
  refine ⟨N,δ,hδ,?_⟩
  intro n hn
  obtain ⟨a,ha,ha0,hzero,hbase,hflat⟩ := hcharts n hn
  have hOwnJoint : AnalyticAt ℂ (hillMixedOwnComplexPeriod q hq hr h0q h0r N n)
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillMixedOwnComplexPeriod q hq hr h0q h0r N n hn B D hc (U ∩ ball 0 B)
      (hU.inter isOpen_ball) inter_subset_right (by
        intro k hk hkN
        exact (hLow k k hk hkN).mono (prod_mono_right inter_subset_left)))
      _ ⟨mem_univ _,hpU,hpB⟩
  have hOwn : AnalyticAt ℂ (fun p : Coeff 2 => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p))
      (SpectralWeight.one.toCoeff q) :=
    hOwnJoint.comp (f := fun p : Coeff 2 => (a p,p)) ((ha _ (mem_ball_self hδ)).prod analyticAt_id)
  have hne : hillMixedOwnComplexPeriod q hq hr h0q h0r N n
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q)≠0 := by
    rw [ha0]
    exact hillMixedOwnComplexPeriod_selected_ne_zero q hq hr h0q h0r N n hN hn B D hc hp
  refine ⟨a,ha,fun E => (hbase E).1,?_,hflat⟩
  apply hillMixedNormalizedComplexPsi_eventually_physical_of_zero_periods q hq hr h0q h0r N n hN hn B D hc hpB a hOwn hne
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with p hpδ
  exact hzero p hpδ

end NLS.KdV
