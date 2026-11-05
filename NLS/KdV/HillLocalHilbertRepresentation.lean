import NLS.KdV.HillAnalyticNormalizedCandidateBranch
import NLS.KdV.HillMixedNearbyPhysicalPeriods
import NLS.KdV.HillComplexHilbertNormalizedUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r

theorem exists_hillSelectedPsi_analytic_hilbert_representation (n : ℕ) (hn : 1 ≤ n) :
    ∃ a : Coeff 2 → Coeff 2, ∃ P : Coeff 2 → ℂ,
      AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) ∧
      AnalyticAt ℂ P (SpectralWeight.one.toCoeff q) ∧
      P (SpectralWeight.one.toCoeff q) ≠ 0 ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        ∀ E : ℂ, hillAbelianHilbertPsi n (E,a (SpectralWeight.one.toCoeff p.val)) /
          P (SpectralWeight.one.toCoeff p.val) =
            hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n hn E := by
  obtain ⟨N,B,D,U,hN,hD,hc,hU,hqU,hsub,hbranches⟩ :=
    exists_hillMixedSupportedPeriodMap_analytic_implicit_root q hq hr h0q h0r
  let roots := (hillAbelianSelectedGlobalRoots q hq hr n hn).val
  have hroots : roots ∈ hillGapRootBox q hq hr := (hillAbelianSelectedGlobalRoots q hq hr n hn).property
  have hperiods (k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n) : hillAbelianCandidatePeriod q hq hr roots n k = 0 := by
    have h := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
    rw [if_neg hkn,div_eq_zero_iff] at h
    exact h.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  obtain ⟨s,hs,hs0,hzeros⟩ := hbranches n hn roots hroots hperiods
  let a0 := hillGapRootHilbertCoordinates q hq hr roots hroots
  let inc : PositiveDeletedCoeff 2 (n : ℤ) →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.id ℂ (Coeff 2)-Coeff.positiveDeletedProjection 2 (n : ℤ)).ker.subtypeL
  let a : Coeff 2 → Coeff 2 := fun p => a0+(s p : Coeff 2)
  have ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) := analyticAt_const.add ((inc.analyticAt _).comp hs)
  have ha0 : a (SpectralWeight.one.toCoeff q) = a0 := by
    dsimp only [a]
    rw [hs0,ZeroMemClass.coe_zero,add_zero]
  have hown : hillAbelianHilbertPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q)) ≠ 0 := by
    rw [ha0,hillAbelianHilbertPeriod_eq_genuine_period]
    exact hillAbelianCandidatePeriod_own_ne_zero q hq hr roots hroots n hn
  have hzero_full : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p) = 0 := by
    filter_upwards [hzeros] with p hp
    have hprojection : Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)) = 0 :=
      congrArg (fun v : PositiveDeletedCoeff 2 (n : ℤ) => (v : Coeff 2)) hp
    have hfixed : Coeff.positiveDeletedProjection 2 (n : ℤ)
        (hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p)) =
          hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p) :=
      (Coeff.positiveDeletedProjection_eq_self_iff 2 (n : ℤ) _).mpr
        (fun m hm => hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn _ m hm)
    rw [hfixed] at hprojection
    exact hprojection
  have hden : AnalyticAt ℂ (fun p : Coeff 2 => hillAbelianComplexPeriod q hq hr n n (a p,p))
      (SpectralWeight.one.toCoeff q) := analyticAt_hillAbelianComplexPeriod_general_root_germ q hq hr n n hn a ha
  have hden0 : hillAbelianComplexPeriod q hq hr n n (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) ≠ 0 := by
    rw [hillAbelianComplexPeriod_at_base q hq hr n n hn]
    exact hown
  have hden_ne : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q), hillAbelianComplexPeriod q hq hr n n (a p,p) ≠ 0 :=
    hden.continuousAt.eventually_ne hden0
  obtain ⟨V,hV,hqV,hphysical⟩ := exists_hillMixedComplexPeriodSequence_physical_zero_neighborhood q hq hr h0q h0r N hN B D hc
  obtain ⟨W,hW,hqW,hownphysical⟩ := exists_hillAbelianComplexPeriod_physical_neighborhood q hq hr n hn
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hT : Tendsto P (𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)) (𝓝 (SpectralWeight.one.toCoeff q)) :=
    hP.tendsto (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)
  refine ⟨a,fun p => hillAbelianComplexPeriod q hq hr n n (a p,p),ha,hden,hden0,?_⟩
  filter_upwards [hT.eventually hzero_full,hT.eventually hden_ne,hT.eventually (hU.mem_nhds hqU),
      hV.mem_nhds hqV,hW.mem_nhds hqW] with p hpzero hpden hpU hpV hpW
  have hpnorm : ‖P p‖ ≤ B :=
    (show ‖P p‖ < B by simpa only [mem_ball,dist_zero_right] using hsub hpU).le
  have hmatch := hownphysical p hpW n (a (P p))
  have hownp : hillAbelianHilbertPeriod p.val p.property.1 p.property.2 n n (a (P p)) ≠ 0 := by
    rw [← hmatch]
    exact hpden
  have hperiodp := hphysical p hpV hpnorm n hn (a (P p)) hpzero
  have he := hillAbelian_complex_normalized_hilbertPsi_eq_selected p.val p.property.1 p.property.2 h0q h0r
    n hn (a (P p)) hownp hperiodp
  intro E
  change hillAbelianHilbertPsi n (E,a (P p))/hillAbelianComplexPeriod q hq hr n n (a (P p),P p) = _
  rw [hmatch]
  exact congrFun he E

end NLS.KdV
