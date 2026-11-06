import NLS.KdV.HillIsospectralMixedPeriods
import NLS.KdV.HillCommonMixedPeriodRoots
import NLS.KdV.HillMixedPeriodRootDerivativeInjectivity
import NLS.ComplexAnalysis.ImplicitRootIsospectralDerivative

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

theorem hillMixedImplicitRoot_isospectral_fderiv
    (N n : ℕ) (hN : 1≤N) (hn : 1≤n) (B D : ℝ)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (hF : AnalyticAt ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N n)
      (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn,SpectralWeight.one.toCoeff q))
    (hG : AnalyticAt ℂ (hillMixedSupportedPeriodMap q hq hr h0q h0r N n
      (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn)) (0,SpectralWeight.one.toCoeff q))
    (s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ))
    (hs : AnalyticAt ℂ s (SpectralWeight.one.toCoeff q)) (hs0 : s (SpectralWeight.one.toCoeff q)=0)
    (heq : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q),
      hillMixedSupportedPeriodMap q hq hr h0q h0r N n
        (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (s p,p)=0)
    (h : Coeff 2)
    (hiso : ∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) :
    (fderiv ℂ s (SpectralWeight.one.toCoeff q)) h=0 := by
  let roots := hillAbelianSelectedGlobalRoots q hq hr n hn
  have hperiods (k : ℕ) (hk : 1≤k) (hkn : k≠n) : hillAbelianCandidatePeriod q hq hr roots.val n k=0 := by
    have hh := (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).2 k hk
    rw [if_neg hkn,div_eq_zero_iff] at hh
    exact hh.resolve_right (hillAbelianSelectedGlobalRoots_periods q hq hr n hn).1
  have hinj := hillMixedSupportedPeriodMap_partial_derivative_injective q hq hr h0q h0r
    N n hN hn B D hc hp roots.val roots.property hperiods hG
  apply implicitRoot_fderiv_eq_zero_of_parameter_kernel _ s (SpectralWeight.one.toCoeff q) h hG hs hs0 heq hinj
  exact hillMixedSupportedPeriodMap_isospectral_parameter_kernel q hq hr h0q h0r N n hn B D hc hp
    (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) h hiso hF hG

/-- The genuine common implicit roots are stationary in every actual
isospectral coefficient direction, at every original real source and
every differential index, with one common source radius. -/
theorem exists_hillMixedSupportedPeriods_common_isospectral_root :
    ∃ N : ℕ, ∃ B D ρ δ : ℝ, 1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
      0<ρ ∧ 0<δ ∧ ball (SpectralWeight.one.toCoeff q) δ⊆ball 0 B ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ s : Coeff 2 → PositiveDeletedCoeff 2 (n : ℤ),
        AnalyticOnNhd ℂ s (ball (SpectralWeight.one.toCoeff q) δ) ∧ s (SpectralWeight.one.toCoeff q)=0 ∧
        (∀ p∈ball (SpectralWeight.one.toCoeff q) δ,
          (s p,p)∈ball (0,SpectralWeight.one.toCoeff q) ρ ∧
          hillMixedSupportedPeriodMap q hq hr h0q h0r N n
            (hillAbelianSelectedGlobalRootCoordinates q hq hr n hn) (s p,p)=0) ∧
        ∀ h : Coeff 2,
          (∀ E : ℂ, (fderiv ℂ (fun b : Coeff 2 => hillL2Discriminant b E) (SpectralWeight.one.toCoeff q)) h=0) →
          (fderiv ℂ s (SpectralWeight.one.toCoeff q)) h=0 := by
  obtain ⟨N,B,D,ρ,δ,hN,hB,hD,hc,hρ,hδ,hsource,hcharts⟩ :=
    exists_hillMixedSupportedPeriods_common_analytic_root q hq hr h0q h0r
  obtain ⟨U,hU,hpU,hLow⟩ := exists_hillAbelianComplexPeriods_common_finite_neighborhood q hq hr N
  have hpB : SpectralWeight.one.toCoeff q∈ball (0 : Coeff 2) B := hsource (mem_ball_self hδ)
  have hp : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hpB).le
  refine ⟨N,B,D,ρ,δ,hN,hB,hD,hc,hρ,hδ,hsource,?_⟩
  intro n hn
  obtain ⟨s,hs,hs0,hinfo⟩ := hcharts n hn
  let a0 := hillAbelianSelectedGlobalRootCoordinates q hq hr n hn
  have hMixed := analyticOnNhd_hillMixedComplexPeriodSequence q hq hr h0q h0r N n hN hn B D hD.le hc U (hLow n)
  have hF := hMixed (a0,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hpU,hpB⟩
  have hG := (analyticOnNhd_hillMixedSupportedPeriodMap q hq hr h0q h0r N n a0 (U ∩ ball 0 B) hMixed)
    (0,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hpU,hpB⟩
  refine ⟨s,hs,hs0,?_,?_⟩
  · intro p hpδ
    exact ⟨(hinfo p hpδ).1,(hinfo p hpδ).2.1⟩
  · intro h hiso
    apply hillMixedImplicitRoot_isospectral_fderiv q hq hr h0q h0r N n hN hn B D hc hp hF hG s
      (hs _ (mem_ball_self hδ)) hs0 ?_ h hiso
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hδ)] with p hpδ
    exact (hinfo p hpδ).2.1

end NLS.KdV
