import NLS.KdV.HillIsospectralImplicitRoots
import NLS.KdV.HillCommonMixedNormalizedPsi

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

theorem hillMixedOwnComplexPeriod_isospectral_potential_fderiv
    (N n : ℕ) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (a h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ (fun p : Coeff 2 => hillMixedOwnComplexPeriod q hq hr h0q h0r N n
      (a,p)) (SpectralWeight.one.toCoeff q)) h=0 := by
  unfold hillMixedOwnComplexPeriod
  by_cases hnN : n<N
  · simp only [if_pos hnN]
    exact (hillAbelianComplexPeriod_isospectral_potential_fderiv q hq hr n n hn a _ h hiso (by
      intro E hE
      exact mem_hillAbelianComplexRootDomain_base q hq hr E
        ((hillRealGapContour_sphere_subset q hq hr n hn) hE))).2
  · simp only [if_neg hnN]
    exact (hillAbelianComplexPeriod_isospectral_potential_fderiv 0 h0q h0r n n hn a _ h hiso
      ((hc _ hp).1 n (by omega))).2

/-- The actual mixed normalization contributes no source variation once
the root coordinates and discriminant are stationary. -/
theorem hillMixedNormalizedComplexPsi_isospectral_fderiv
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (a : Coeff 2 → Coeff 2) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q))
    (ha0 : a (SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn)
    (hOwn : AnalyticAt ℂ (hillMixedOwnComplexPeriod q hq hr h0q h0r N n)
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q))
    (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0)
    (hflat : (fderiv ℂ a (SpectralWeight.one.toCoeff q)) h=0) (E : ℂ) :
    AnalyticAt ℂ (fun p : Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p) E)
      (SpectralWeight.one.toCoeff q) ∧
    (fderiv ℂ (fun p : Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p) E)
      (SpectralWeight.one.toCoeff q)) h=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let num : Coeff 2 → ℂ := fun b => hillAbelianHilbertPsi n (E,b)
  have hnum : AnalyticAt ℂ num (a p0) :=
    (analyticOnNhd_hillAbelianHilbertPsi n (E,a p0) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
  have hnc : AnalyticAt ℂ (fun p => num (a p)) p0 := hnum.comp ha
  have hnc0 : (fderiv ℂ (fun p => num (a p)) p0) h=0 := by
    change (fderiv ℂ (num ∘ a) p0) h=0
    rw [fderiv_comp p0 hnum.differentiableAt ha.differentiableAt,ContinuousLinearMap.comp_apply,hflat,map_zero]
  have hdc : AnalyticAt ℂ (fun p => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) p0 :=
    hOwn.comp (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
  have hdc0 : (fderiv ℂ (fun p => hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) p0) h=0 := by
    rw [joint_fderiv_eq_parameter_of_state_kernel _ a p0 h hOwn ha hflat]
    exact hillMixedOwnComplexPeriod_isospectral_potential_fderiv q hq hr h0q h0r N n hn B D hc hp (a p0) h hiso
  have hne : hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p0,p0)≠0 := by
    rw [ha0]
    exact hillMixedOwnComplexPeriod_selected_ne_zero q hq hr h0q h0r N n hN hn B D hc hp
  refine ⟨hnc.div hdc hne,?_⟩
  change (fderiv ℂ (fun p => num (a p)/hillMixedOwnComplexPeriod q hq hr h0q h0r N n (a p,p)) p0) h=0
  rw [fderiv_div_apply _ _ p0 hnc.differentiableAt hdc.differentiableAt hne h,hnc0,hdc0]
  simp only [zero_mul,mul_zero,sub_zero,zero_div]

/-- Genuine selected implicit differential germs at every real source:
one common root-chart radius, actual mixed zero periods, exact physical
base values, and zero variation in every isospectral direction. -/
theorem exists_hillMixedNormalizedComplexPsi_common_isospectral_germs :
    ∃ N : ℕ, ∃ B D δ : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<δ ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ a : Coeff 2 → Coeff 2, AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) ∧
        a (SpectralWeight.one.toCoeff q)=hillAbelianSelectedGlobalRootCoordinates q hq hr n hn ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0) ∧
        (∀ E : ℂ,
          AnalyticAt ℂ (fun p : Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p) E)
            (SpectralWeight.one.toCoeff q) ∧
          hillMixedNormalizedComplexPsi q hq hr h0q h0r N n
            (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) E=hillAbelianSelectedGlobalPsi q hq hr n hn E) ∧
        ∀ h : Coeff 2,
          (∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) →
          ∀ E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillMixedNormalizedComplexPsi q hq hr h0q h0r N n (a p,p) E)
            (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨N,B,D,ρ,δ,hN,hB,hD,hc,_,hδ,hsource,hcharts⟩ :=
    exists_hillMixedSupportedPeriods_common_isospectral_root q hq hr h0q h0r
  obtain ⟨U,hU,hpU,hLow⟩ := exists_hillAbelianComplexPeriods_common_finite_neighborhood q hq hr N
  have hpB : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B := hsource (mem_ball_self hδ)
  have hp : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hpB).le
  refine ⟨N,B,D,δ,hN,hB,hD,hc,hδ,hsource,?_⟩
  intro n hn
  obtain ⟨s,hs,hs0,hinfo,hflat⟩ := hcharts n hn
  let a0 := hillAbelianSelectedGlobalRootCoordinates q hq hr n hn
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let a : Coeff 2 → Coeff 2 := fun p => a0+inc (s p)
  have ha : AnalyticOnNhd ℂ a (ball (SpectralWeight.one.toCoeff q) δ) := by
    intro p hpδ
    exact analyticAt_const.add ((inc.analyticAt _).comp (hs p hpδ))
  have ha0 : a (SpectralWeight.one.toCoeff q)=a0 := by
    simp only [a,hs0,map_zero,add_zero]
  have hOwn : AnalyticAt ℂ (hillMixedOwnComplexPeriod q hq hr h0q h0r N n)
      (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) :=
    (analyticOnNhd_hillMixedOwnComplexPeriod q hq hr h0q h0r N n hn B D hc (U ∩ ball 0 B)
      (hU.inter isOpen_ball) inter_subset_right (by
        intro k hk hkN
        exact (hLow k k hk hkN).mono (prod_mono_right inter_subset_left)))
      _ ⟨mem_univ _,hpU,hpB⟩
  have haFlat (h : Coeff 2)
      (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) :
      (fderiv ℂ a (SpectralWeight.one.toCoeff q)) h=0 := by
    have hd := (hasFDerivAt_const a0 (SpectralWeight.one.toCoeff q)).add
      ((inc.hasFDerivAt).comp (f := s) (SpectralWeight.one.toCoeff q)
        (hs _ (mem_ball_self hδ)).differentiableAt.hasFDerivAt)
    change HasFDerivAt a _ (SpectralWeight.one.toCoeff q) at hd
    rw [hd.fderiv]
    simp only [add_apply,zero_apply,ContinuousLinearMap.comp_apply,hflat h hiso,map_zero,add_zero]
  refine ⟨a,ha,ha0,?_,?_,?_⟩
  · intro p hpδ
    have hh := congrArg (fun v : PositiveDeletedCoeff 2 (n : ℤ) => (v : Coeff 2)) (hinfo p hpδ).2
    change Coeff.positiveDeletedProjection 2 (n : ℤ)
      (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p))=0 at hh
    rw [hillMixedComplexPeriodSequence_positiveDeleted_fixed q hq hr h0q h0r N n hn] at hh
    exact hh
  · intro E
    refine ⟨(hillMixedNormalizedComplexPsi_isospectral_fderiv q hq hr h0q h0r N n hN hn B D hc hp
      a (ha _ (mem_ball_self hδ)) ha0 hOwn 0 (by intro E; exact map_zero _) (map_zero _) E).1,?_⟩
    rw [ha0]
    exact hillMixedNormalizedComplexPsi_selected_at_base q hq hr h0q h0r N n hN hn B D hc hp E
  · intro h hiso E
    exact (hillMixedNormalizedComplexPsi_isospectral_fderiv q hq hr h0q h0r N n hN hn B D hc hp
      a (ha _ (mem_ball_self hδ)) ha0 hOwn h hiso (haFlat h hiso) E).2

end NLS.KdV
