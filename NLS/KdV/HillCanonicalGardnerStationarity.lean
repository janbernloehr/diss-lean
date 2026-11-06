import NLS.KdV.HillNormalizedGardnerStationarity
import NLS.KdV.HillGlobalDifferentialAnalyticExtension
import NLS.KdV.HillRealSourceJetUniqueness

/-! # Stationarity of an actual canonical normalized family

The stationary implicit branch is matched to the genuine normalized global
differential at every nearby real potential, using its actual off-diagonal
period equations and nonzero own period. The same branch supplies both the
physical agreement and the source derivative.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
  (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
  (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
  (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
  (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

/-- A jointly analytic stationary extension agrees with the actual canonical
normalized differential at all nearby real period-one L2 potentials. -/
theorem exists_hillAbelianSelectedGlobalPsi_stationary_joint_analytic_extension
    (n : ℕ) (hn : 1≤n) :
    ∃ G : ℂ × Coeff 2 → ℂ,
      (∀ E : ℂ, AnalyticAt ℂ G (E,SpectralWeight.one.toCoeff q)) ∧
      (∀ b E : ℂ, (fderiv ℂ (fun p : Coeff 2 => G (E,p)) (SpectralWeight.one.toCoeff q))
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        ∀ E : ℂ, G (E,SpectralWeight.one.toCoeff p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E := by
  obtain ⟨N,B,D,a,hN,_hD,hc,hp,ha,ha0,_haX,hjoint,_hbase,hstat,hzeros⟩ :=
    exists_hillBaseNormalizedComplexPsi_stationary_analytic_branch_with_tail_control q hq hr h0q h0r n hn
  have hown : hillAbelianHilbertPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q))≠0 := by
    rw [ha0,hillAbelianHilbertPeriod_eq_genuine_period]
    exact hillAbelianCandidatePeriod_own_ne_zero q hq hr
      (hillAbelianSelectedGlobalRoots q hq hr n hn).val (hillAbelianSelectedGlobalRoots q hq hr n hn).property n hn
  have hden := analyticAt_hillAbelianComplexPeriod_general_root_germ q hq hr n n hn a ha
  have hden0 : hillAbelianComplexPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q)≠0 := by
    rw [hillAbelianComplexPeriod_at_base q hq hr n n hn]
    exact hown
  have hden_ne : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), hillAbelianComplexPeriod q hq hr n n (a p,p)≠0 :=
    hden.continuousAt.eventually_ne hden0
  obtain ⟨V,hV,hqV,hphysical⟩ := exists_hillMixedComplexPeriodSequence_physical_zero_neighborhood q hq hr h0q h0r N hN B D hc
  obtain ⟨W,hW,hqW,hownphysical⟩ := exists_hillAbelianComplexPeriod_physical_neighborhood q hq hr n hn
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hT : Tendsto P (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) (𝓝 (SpectralWeight.one.toCoeff q)) :=
    hP.tendsto (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
  have hball : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B := by
    simpa only [mem_ball,dist_zero_right] using hp
  refine ⟨fun t => hillBaseNormalizedComplexPsi q hq hr n (a t.2,t.2) t.1,hjoint,hstat,?_⟩
  filter_upwards [hT.eventually hzeros,hT.eventually hden_ne,
    hT.eventually (isOpen_ball.mem_nhds hball),hV.mem_nhds hqV,hW.mem_nhds hqW] with p hpzero hpden hpB hpV hpW
  have hpnorm : ‖P p‖≤B :=
    (show ‖P p‖<B by simpa only [mem_ball,dist_zero_right] using hpB).le
  have hmatch := hownphysical p hpW n (a (P p))
  have hownp : hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n n (a (P p))≠0 := by
    rw [← hmatch]
    exact hpden
  have hperiodp := hphysical p hpV hpnorm n hn (a (P p)) hpzero
  have he := hillAbelian_complex_normalized_hilbertPsi_eq_selected p.val p.property.1 p.property.2 h0q h0r n hn (a (P p)) hownp hperiodp
  intro E
  change hillAbelianHilbertPsi n (E,a (P p))/hillAbelianComplexPeriod q hq hr n n (a (P p),P p)=_
  rw [hmatch]
  exact congrFun he E

/-- Every differentiable extension of the genuine normalized differential
has zero Gardner variation; the extension need only agree on nearby actual
real potentials. Thus existing analytic angle charts can use the result
without identifying their chosen extension off the physical real slice. -/
theorem fderiv_hillAbelianSelectedGlobalPsi_extension_gardnerDirection_eq_zero
    (n : ℕ) (hn : 1≤n) (F : Coeff 2 → ℂ) (E b : ℂ)
    (hF : DifferentiableAt ℂ F (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F (SpectralWeight.one.toCoeff p.val)=hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E) :
    (fderiv ℂ F (SpectralWeight.one.toCoeff q))
      (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q) b)=0 := by
  obtain ⟨G,hG,hstat,hreal⟩ :=
    exists_hillAbelianSelectedGlobalPsi_stationary_joint_analytic_extension q hq hr h0q h0r n hn
  have hsec : AnalyticAt ℂ (fun p : Coeff 2 => G (E,p)) (SpectralWeight.one.toCoeff q) :=
    (hG E).comp (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)
  have he : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      F (SpectralWeight.one.toCoeff p.val)=G (E,SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch,hreal] with p hp hpG
    exact hp.trans (hpG E).symm
  rw [fderiv_eq_on_parity_of_eventuallyEq_realPotentials q hq hr F (fun p => G (E,p)) hF hsec.differentiableAt he
    _ (hillL2DiscriminantGardnerDirection_mem_parity _ b)]
  exact hstat b E

end NLS.KdV
