import NLS.KdV.HillExtendedPositiveJacobian
import NLS.FunctionalAnalysis.CompactFamilyLowerBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The actual full positive extensions of the original scaled mixed
Jacobians have one large-index lower bound over the entire real gap box. -/
theorem exists_hillExtendedPositivePeriodJacobian_uniform_lower_bound
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (hF : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N j (b,SpectralWeight.one.toCoeff q)) univ)
    (hFull : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ) :
    ∃ J : ℕ, ∃ C : ℝ, 1≤J ∧ 1≤C ∧ ∀ n : ℕ, J≤n →
      ∀ roots : ℕ → ℝ, ∀ hroots : roots∈hillGapRootBox q hq hr,
      ∀ h : PositiveDeletedCoeff 2 (0 : ℤ),
        ‖h‖≤C*‖hillExtendedPositivePeriodJacobian q hq hr h0q h0r N n
          (hillGapRootHilbertCoordinates q hq hr roots hroots) (SpectralWeight.one.toCoeff q) h‖ := by
  let K := range (fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property)
  have hK : IsCompact K := isCompact_range_hillGapRootHilbertCoordinates q hq hr
  let T : ℕ → Coeff 2 → PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (0 : ℤ) :=
    fun n a => hillExtendedPositivePeriodJacobian q hq hr h0q h0r N n a (SpectralWeight.one.toCoeff q)
  let S : Coeff 2 → PositiveDeletedCoeff 2 (0 : ℤ) →L[ℂ] PositiveDeletedCoeff 2 (0 : ℤ) :=
    fun a => fderiv ℂ (fun b : PositiveDeletedCoeff 2 (0 : ℤ) =>
      hillFullMixedSupportedPeriodMap q hq hr h0q h0r N a (b,SpectralWeight.one.toCoeff q)) 0
  have hS : ∀ a∈K, Function.Bijective (S a) := by
    intro a ha
    obtain ⟨roots,rfl⟩ := ha
    exact hillFullMixedSupportedPeriodMap_root_derivative_bijective q hq hr h0q h0r
      N hN B D hD hc hp roots.val roots.property hFull
  have hlim : ∀ n : ℕ → ℕ, (∀ i, 1≤n i) → Tendsto n atTop atTop →
      ∀ a : ℕ → Coeff 2, (∀ i, a i∈K) → ∀ a0∈K, Tendsto a atTop (𝓝 a0) →
        Tendsto (fun i => T (n i) (a i)) atTop (𝓝 (S a0)) := by
    intro n hn hni a haK a0 _ ha
    have hnorm := tendsto_hillExtendedMixedPeriodJacobian q hq hr h0q h0r n hn hni
      N hN B D hD hc hp K hK a haK a0 ha hF hFull
    exact tendsto_hillExtendedPositivePeriodJacobian_of_ambient q hq hr h0q h0r N n a a0 _
      (hFull a0 (mem_univ _)).differentiableAt hnorm
  obtain ⟨J,C,hJ,hC,hbound⟩ := exists_uniform_eventual_lower_bound_of_compact_norm_limits K hK T S hS hlim
  refine ⟨J,C,hJ,hC,?_⟩
  intro n hn roots hroots h
  exact hbound n hn _ ⟨⟨roots,hroots⟩,rfl⟩ h

/-- At every original real potential, all source and analytic hypotheses
of the large-index uniform positive lower bound hold on one common
complex source neighborhood. -/
theorem exists_hillExtendedPositivePeriodJacobian_common_lower_bound :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2), ∃ J : ℕ, ∃ C : ℝ,
      1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ U⊆ball 0 B ∧
        AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ U) ∧
        (∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N j) (univ ×ˢ U)) ∧
        1≤J ∧ 1≤C ∧ ∀ n : ℕ, J≤n → ∀ roots : ℕ → ℝ, ∀ hroots : roots∈hillGapRootBox q hq hr,
          ∀ h : PositiveDeletedCoeff 2 (0 : ℤ),
          ‖h‖≤C*‖hillExtendedPositivePeriodJacobian q hq hr h0q h0r N n
            (hillGapRootHilbertCoordinates q hq hr roots hroots) (SpectralWeight.one.toCoeff q) h‖ := by
  let K := range (fun roots : hillGapRootBox q hq hr => hillGapRootHilbertCoordinates q hq hr roots.val roots.property)
  obtain ⟨N,B,D,U,hN,hB,hD,hc,hU,hqU,hsub,hFull,hFinite,_⟩ :=
    exists_hillExtendedMixedPeriodJacobian_norm_limit q hq hr h0q h0r K (isCompact_range_hillGapRootHilbertCoordinates q hq hr)
  have hp : ‖SpectralWeight.one.toCoeff q‖≤B :=
    (show ‖SpectralWeight.one.toCoeff q‖<B by simpa only [mem_ball,dist_zero_right] using hsub hqU).le
  have hfullsec : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ := by
    intro b _
    exact (hFull (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hfinitesec : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N j (b,SpectralWeight.one.toCoeff q)) univ := by
    intro j hj b _
    exact (hFinite j hj (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqU⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  obtain ⟨J,C,hJ,hC,hbound⟩ := exists_hillExtendedPositivePeriodJacobian_uniform_lower_bound q hq hr h0q h0r
    N hN B D hD.le hc hp hfinitesec hfullsec
  exact ⟨N,B,D,U,J,C,hN,hB,hD,hc,hU,hqU,hsub,hFull,hFinite,hJ,hC,hbound⟩

end NLS.KdV
