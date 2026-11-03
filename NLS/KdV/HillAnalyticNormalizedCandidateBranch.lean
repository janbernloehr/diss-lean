import NLS.KdV.HillBijectivePeriodChart
import NLS.KdV.HillBaseNormalizedComplexPsi

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

theorem exists_hillBaseNormalizedComplexPsi_analytic_candidate_branch (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, ∃ a : Coeff 2 → Coeff 2,
      AnalyticAt ℂ a (SpectralWeight.one.toCoeff q) ∧
      a (SpectralWeight.one.toCoeff q) = hillGapRootHilbertCoordinates q hq hr
        (hillAbelianSelectedGlobalRoots q hq hr n hn).val (hillAbelianSelectedGlobalRoots q hq hr n hn).property ∧
      (∀ E : ℂ, AnalyticAt ℂ
        (fun t : ℂ × Coeff 2 => hillBaseNormalizedComplexPsi q hq hr n (a t.2,t.2) t.1)
          (E,SpectralWeight.one.toCoeff q)) ∧
      (∀ E : ℂ, hillBaseNormalizedComplexPsi q hq hr n
        (a (SpectralWeight.one.toCoeff q),SpectralWeight.one.toCoeff q) E =
          hillAbelianSelectedGlobalPsi q hq hr n hn E) ∧
      ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
        hillMixedComplexPeriodSequence q hq hr h0q h0r N n (a p,p) = 0 := by
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
  refine ⟨N,a,ha,ha0,?_,?_,?_⟩
  · intro E
    exact analyticAt_hillBaseNormalizedComplexPsi_root_germ q hq hr n hn a ha hown E
  · intro E
    rw [ha0,hillBaseNormalizedComplexPsi_at_physical_roots q hq hr n hn roots hroots E]
    rfl
  · filter_upwards [hzeros] with p hp
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

end NLS.KdV
