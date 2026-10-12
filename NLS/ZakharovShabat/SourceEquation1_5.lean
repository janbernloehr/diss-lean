import NLS.ZakharovShabat.SourceParityRestriction
import NLS.ZakharovShabat.SourceEquation1_4

/-! # Equation (1.5) in the original period-one potential topology

One open convex neighborhood in period-one coordinates carries both parity
restrictions of every sufficiently large central projector and every distant
circle projector. The restrictions are analytic endomorphisms of the parity
subspaces, agree with the actual integrals, and are finite-rank projections.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (1.5), simultaneously for both parities and all larger cutoffs.
The potential coordinates are period one; `periodOnePair` inserts them into
the period-two operator. Thus openness and analyticity use the source's
period-one topology, including at p=1. -/
theorem sourceEquation1_5 (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ U : Set (CoeffPair p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ IsConnected U ∧
      φ ∈ U ∧ 0 ∈ U ∧ ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
      (AnalyticOnNhd ℂ (fun ψ => sourceParityCentralProjection hp (periodOnePair ψ) N r) U ∧
        ∀ ψ ∈ U,
          (∀ x : sourceParitySubspace (p := p) r,
            (sourceParityCentralProjection hp (periodOnePair ψ) N r x).val =
              sourceCentralRectangleIntegral hp (periodOnePair ψ) N x.val) ∧
          IsIdempotentElem (sourceParityCentralProjection hp (periodOnePair ψ) N r) ∧
          FiniteDimensional ℂ (sourceParityCentralProjection hp (periodOnePair ψ) N r).range) ∧
      ∀ n : ℤ, N < n.natAbs →
        AnalyticOnNhd ℂ (fun ψ => sourceParityCircleProjection hp (periodOnePair ψ)
          ((Real.pi : ℂ)*n) (Real.pi/4) r) U ∧
        ∀ ψ ∈ U,
          (∀ x : sourceParitySubspace (p := p) r,
            (sourceParityCircleProjection hp (periodOnePair ψ) ((Real.pi : ℂ)*n) (Real.pi/4) r x).val =
              sourceResolventCircleIntegral hp (periodOnePair ψ) ((Real.pi : ℂ)*n) (Real.pi/4) x.val) ∧
          IsIdempotentElem (sourceParityCircleProjection hp (periodOnePair ψ) ((Real.pi : ℂ)*n) (Real.pi/4) r) ∧
          FiniteDimensional ℂ (sourceParityCircleProjection hp (periodOnePair ψ) ((Real.pi : ℂ)*n) (Real.pi/4) r).range := by
  obtain ⟨N₀,V,hN₀,hVo,hVc,_,hφ,h0,h⟩ := sourceEquation1_4 hp (periodOnePair φ)
  let U : Set (CoeffPair p) := periodOnePair ⁻¹' V
  have ho : IsOpen U := hVo.preimage (periodOnePair (p := p)).continuous
  have hc : Convex ℝ U := hVc.linear_preimage
    ((periodOnePair (p := p)).toContinuousLinearMap.restrictScalars ℝ).toLinearMap
  have h0U : (0 : CoeffPair p) ∈ U := by simpa only [U,Set.mem_preimage,map_zero] using h0
  refine ⟨N₀,U,hN₀,ho,hc,⟨⟨0,h0U⟩,hc.isPreconnected⟩,hφ,h0U,?_⟩
  intro N hN r
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro ψ hψ
    exact (analyticAt_sourceParityCompression r _).comp
      (((h N hN).1.1 _ hψ).comp ((periodOnePair (p := p)).toContinuousLinearMap.analyticAt ψ))
  · intro ψ hψ
    have hb := ((h N hN).1.2 _ hψ).1
    exact ⟨sourceParityCentralProjection_apply hp _ (periodOnePotential_mem ψ) N r hb,
      sourceParityCentralProjection_idempotent hp _ (periodOnePotential_mem ψ) N r hb,
      finiteDimensional_range_sourceParityCentralProjection hp _ (periodOnePotential_mem ψ) N r hb⟩
  · intro n hn
    refine ⟨?_,?_⟩
    · intro ψ hψ
      exact analyticAt_sourceParityCircleProjection hp ψ _ _ r (by positivity)
        ((((h N hN).2 n hn).2 _ hψ).1)
    · intro ψ hψ
      have hb := (((h N hN).2 n hn).2 _ hψ).1
      exact ⟨sourceParityCircleProjection_apply hp _ (periodOnePotential_mem ψ) _ _ r (by positivity) hb,
        sourceParityCircleProjection_idempotent hp _ (periodOnePotential_mem ψ) _ _ r (by positivity) hb,
        finiteDimensional_range_sourceParityCircleProjection hp _ (periodOnePotential_mem ψ) _ _ r (by positivity) hb⟩

end NLS.ZakharovShabat
