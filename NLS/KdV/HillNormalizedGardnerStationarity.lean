import NLS.KdV.HillMixedGardnerVariation
import NLS.KdV.HillAnalyticNormalizedCandidateBranch
import NLS.ComplexAnalysis.ImplicitRootStationarity

/-! # An actual stationary analytic normalized differential germ

The branch is constructed from the genuine normalized global roots and the
verified bijective derivative of their period equation. Its stationarity is
proved by differentiating that equation, then the own-period normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Differentiating the actual own-period quotient preserves stationarity
of the numerator coefficients. -/
theorem fderiv_hillBaseNormalizedComplexPsi_gardnerDirection_eq_zero
    (n : ℕ) (hn : 1≤n) (a : Coeff 2 → Coeff 2)
    (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q))
    (hown : hillAbelianHilbertPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q))≠0)
    (b E : ℂ)
    (hz : (fderiv ℂ a (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) :
    (fderiv ℂ (fun p : Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a p,p) E)
      (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  let p0 := SpectralWeight.one.toCoeff q
  let X := hillL2DiscriminantGardnerDirection p0 b
  have hN : AnalyticAt ℂ (fun c : Coeff 2 => hillAbelianHilbertPsi n (E,c)) (a p0) :=
    (analyticOnNhd_hillAbelianHilbertPsi n (E,a p0) (mem_univ _)).comp
      (f := fun c : Coeff 2 => (E,c)) (analyticAt_const.prod analyticAt_id)
  have hNA := hN.comp ha
  have hdN := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L X)
    (hN.differentiableAt.hasFDerivAt.comp p0 ha.differentiableAt.hasFDerivAt).fderiv
  change (fderiv ℂ (fun p : Coeff 2 => hillAbelianHilbertPsi n (E,a p)) p0) X=
    (fderiv ℂ (fun c : Coeff 2 => hillAbelianHilbertPsi n (E,c)) (a p0)) ((fderiv ℂ a p0) X) at hdN
  rw [hz,map_zero] at hdN
  obtain ⟨U,_,hpU,hP⟩ := exists_hillAbelianComplexPeriod_analytic_neighborhood q hq hr n n hn
  have hPA := hP (a p0,p0) ⟨mem_univ _,hpU⟩
  have hdP := fderiv_pair_comp_apply_of_left_eq_zero
    (hillAbelianComplexPeriod q hq hr n n) a p0 X hPA.differentiableAt ha.differentiableAt hz
  rw [fderiv_hillAbelianComplexPeriod_gardnerDirection_eq_zero q hq hr n n hn (a p0) b] at hdP
  have hPT := analyticAt_hillAbelianComplexPeriod_general_root_germ q hq hr n n hn a ha
  have hne : hillAbelianComplexPeriod q hq hr n n (a p0,p0)≠0 := by
    rw [hillAbelianComplexPeriod_at_base q hq hr n n hn]
    exact hown
  change (fderiv ℂ (fun p : Coeff 2 => hillAbelianHilbertPsi n (E,a p)/
    hillAbelianComplexPeriod q hq hr n n (a p,p)) p0) X=0
  rw [fderiv_div_apply (fun p : Coeff 2 => hillAbelianHilbertPsi n (E,a p))
    (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n n (a p,p))
    p0 hNA.differentiableAt hPT.differentiableAt hne X,hdN,hdP]
  simp

variable
  (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
  (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- A genuine normalized global differential has an actual jointly analytic
local extension stationary along every constructed complex Gardner direction. -/
theorem exists_hillBaseNormalizedComplexPsi_stationary_analytic_branch_with_tail_control (n : ℕ) (hn : 1≤n) :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ a : Coeff 2 → Coeff 2,
      1≤N ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      ‖SpectralWeight.one.toCoeff q‖<B ∧
      AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) ∧
      a (SpectralWeight.one.toCoeff q)=hillGapRootHilbertCoordinates q hq hr
        (hillAbelianSelectedGlobalRoots q hq hr n hn).val (hillAbelianSelectedGlobalRoots q hq hr n hn).property ∧
      (∀ b : ℂ, (fderiv ℂ a (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      (∀ E : ℂ, AnalyticAt ℂ
        (fun t : ℂ × Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a t.2,t.2) t.1)
          (E,SpectralWeight.one.toCoeff q)) ∧
      (∀ E : ℂ, hillBaseNormalizedComplexPsi q hq hr n
        (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) E=
          hillAbelianSelectedGlobalPsi q hq hr n hn E) ∧
      (∀ b E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a p,p) E)
        (SpectralWeight.one.toCoeff q))
          (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
        hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0 := by
  obtain ⟨N,B,D,U,hN,hD,hc,_hU,hqU,hsub,hcharts⟩ :=
    exists_hillMixedSupportedPeriodMap_analytic_with_bijective_root_derivative q hq hr h0q h0r
  have hp : ‖SpectralWeight.one.toCoeff q‖<B := by
    simpa only [mem_ball,dist_zero_right] using hsub hqU
  let roots := (hillAbelianSelectedGlobalRoots q hq hr n hn).val
  have hroots : roots∈hillGapRootBox q hq hr := (hillAbelianSelectedGlobalRoots q hq hr n hn).property
  have hperiods (k : ℕ) (hk : 1≤k) (hkn : k≠n) : hillAbelianCandidatePeriod q hq hr roots n k=0 := by
    have h := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
    rw [if_neg hkn,div_eq_zero_iff] at h
    exact h.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  let a0 := hillGapRootHilbertCoordinates q hq hr roots hroots
  let F := hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0
  obtain ⟨hF,hzero,hbij⟩ := hcharts n hn roots hroots hperiods
  obtain ⟨s,hs,hs0,hzeros⟩ := exists_analytic_implicitBanachRoot F 0 (SpectralWeight.one.toCoeff q) hF hzero hbij
  have hsX (b : ℂ) : (fderiv ℂ s (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
    apply fderiv_implicitRoot_apply_eq_zero F s _ _
      (by simpa only [hs0] using hF.differentiableAt) hs.differentiableAt hzeros
      (by simpa only [hs0] using hbij.1)
    simpa only [hs0] using
      fderiv_hillMixedSupportedPeriodMap_source_gardnerDirection_eq_zero q hq hr h0q h0r N n hN hn B D hD.le hc hp a0 b
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let a : Coeff 2 → Coeff 2 := fun p => a0+(s p : Coeff 2)
  have ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) := analyticAt_const.add ((inc.analyticAt _).comp hs)
  have ha0 : a (SpectralWeight.one.toCoeff q)=a0 := by
    dsimp only [a]
    rw [hs0,ZeroMemClass.coe_zero,add_zero]
  have haX (b : ℂ) : (fderiv ℂ a (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
    have hd := congrArg (fun L : Coeff 2 →L[ℂ] Coeff 2 =>
      L (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b))
      ((inc.hasFDerivAt.comp _ hs.differentiableAt.hasFDerivAt).const_add a0).fderiv
    change (fderiv ℂ a (SpectralWeight.one.toCoeff q)) _=inc ((fderiv ℂ s (SpectralWeight.one.toCoeff q)) _) at hd
    rw [hsX,map_zero] at hd
    exact hd
  have hown : hillAbelianHilbertPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q))≠0 := by
    rw [ha0,hillAbelianHilbertPeriod_eq_genuine_period]
    exact hillAbelianCandidatePeriod_own_ne_zero q hq hr roots hroots n hn
  refine ⟨N,B,D,a,hN,hD,hc,hp,ha,ha0,haX,?_,?_,?_,?_⟩
  · intro E
    exact analyticAt_hillBaseNormalizedComplexPsi_root_germ q hq hr n hn a ha hown E
  · intro E
    rw [ha0,hillBaseNormalizedComplexPsi_at_physical_roots q hq hr n hn roots hroots E]
    rfl
  · intro b E
    exact fderiv_hillBaseNormalizedComplexPsi_gardnerDirection_eq_zero q hq hr n hn a ha hown b E (haX b)
  · filter_upwards [hzeros] with p hp0
    have hprojection : Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p))=0 :=
      congrArg (fun v : PositiveDeletedCoeff 2 (n : ℤ) => (v : Coeff 2)) hp0
    have hfixed : Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p))=
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p) :=
      (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) _).mpr
        (fun m hm => hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn _ m hm)
    rw [hfixed] at hprojection
    exact hprojection

/-- The stationary normalized germ, with the auxiliary tail-control data hidden. -/
theorem exists_hillBaseNormalizedComplexPsi_stationary_analytic_branch (n : ℕ) (hn : 1≤n) :
    ∃ N : ℕ, ∃ a : Coeff 2 → Coeff 2,
      AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) ∧
      a (SpectralWeight.one.toCoeff q)=hillGapRootHilbertCoordinates q hq hr
        (hillAbelianSelectedGlobalRoots q hq hr n hn).val (hillAbelianSelectedGlobalRoots q hq hr n hn).property ∧
      (∀ b : ℂ, (fderiv ℂ a (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      (∀ E : ℂ, AnalyticAt ℂ
        (fun t : ℂ × Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a t.2,t.2) t.1)
          (E,SpectralWeight.one.toCoeff q)) ∧
      (∀ E : ℂ, hillBaseNormalizedComplexPsi q hq hr n
        (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) E=
          hillAbelianSelectedGlobalPsi q hq hr n hn E) ∧
      (∀ b E : ℂ, (fderiv ℂ (fun p : Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a p,p) E)
        (SpectralWeight.one.toCoeff q))
          (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
        hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)=0 := by
  obtain ⟨N,B,D,a,_hN,_hD,_hc,_hp,ha,ha0,haX,hjoint,hbase,hstat,hzeros⟩ :=
    exists_hillBaseNormalizedComplexPsi_stationary_analytic_branch_with_tail_control q hq hr h0q h0r n hn
  exact ⟨N,a,ha,ha0,haX,hjoint,hbase,hstat,hzeros⟩

end NLS.KdV
