import NLS.ZakharovShabat.WeightedResonantCenterRemainder
import NLS.ZakharovShabat.UniformPowerTail

/-!
# Locally uniform smallness of the actual sequence remainder

The joint source-pair budget gives an arbitrarily small `ℓᵖ` norm on
one open convex neighborhood for every sufficiently large cutoff.
The neighborhood may depend on the tolerance. This does not assert
uniform convergence on a fixed source ball, or a derivative bound.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both actual remainder components are constructed and their
combined sequence norm is arbitrarily small locally uniformly. -/
theorem exists_uniform_weightedResonantCenterRemainder_small
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      (∀ ψ ∈ U, ‖ψ‖ < ‖φ‖+1) ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ N positive) p) ∧
        ‖weightedResonantCenterRemainder hp w ψ N‖ < ε := by
  have hP : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let M := ‖φ‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ := exists_uniform_weightedResonantCenterRemainder_bound hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,hnorm,hbudget⟩ :=
    exists_uniform_powerTail_budget hp w φ (by positivity : 0 < 2*p.toReal)
      (by positivity : 0 < min 1 (p.toReal-1))
      (mul_nonneg (offDiagonalSummationConstant_nonneg p) (Real.rpow_nonneg hM.le p.toReal))
      (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,fun ψ hψ => hnorm ψ hψ.2,?_⟩
  intro ψ hψ N hN
  have hdata := h₁ ψ hψ.1 N (by omega)
  have hψM : ‖ψ‖ ≤ M := (hnorm ψ hψ.2).le
  have hpower : ‖weightedResonantCenterRemainder hp w ψ N‖^p.toReal < ε^p.toReal := by
    apply hdata.2.trans_lt
    apply lt_of_le_of_lt _ (hbudget ψ hψ.2 N (by omega))
    have hC := offDiagonalSummationConstant_nonneg p
    gcongr
  exact ⟨hdata.1,(Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by linarith)).mp hpower⟩

end NLS.ZakharovShabat
