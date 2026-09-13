import NLS.ZakharovShabat.ParityLiteralCutoffs
import NLS.ZakharovShabat.ActualParityProductExistence

/-!
# Independence of actual parity products from spectral choices

Sufficiently large finite even cutoffs are the same intrinsic central
polynomial. The odd cutoffs retain the same additional counted boundary pair.
Their equality holds at every spectral parameter, including all roots.
Uniqueness of limits gives equality of the entire parity functions for any
admissible central cutoffs and pair labels.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A counted pair determines its normalized factor independently of the order of its two labels. -/
theorem PeriodicResonantPair.factor_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {n : ℤ} {ξ η α β : ℤ → ℂ}
    (h : PeriodicResonantPair hp w φ n (ξ n) (η n))
    (k : PeriodicResonantPair hp w φ n (α n) (β n)) (z : ℂ) :
    spectralPairFactor ξ η z n = spectralPairFactor α β z n := by
  rcases h.eq_or_swap k with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · simp only [spectralPairFactor_eq_div, hx, hy]
  · simp only [spectralPairFactor_eq_div, hx, hy, mul_comm]

/-- Both literal cutoff polynomials agree once they contain both admissible central clusters. -/
theorem CompletePeriodicParityPairs.cutoffs_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N K : ℕ} {ξ η α β : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (k : CompletePeriodicParityPairs hp w φ K α β)
    (M : ℕ) (hNM : N ≤ 2*M) (hKM : K ≤ 2*M) :
    (fun z => evenSpectralPairCutoff ξ η z M) = (fun z => evenSpectralPairCutoff α β z M) ∧
    (fun z => oddSpectralPairCutoff ξ η z M) = (fun z => oddSpectralPairCutoff α β z M) := by
  constructor
  · funext z
    rw [h.evenCutoff_eq_central M hNM z, k.evenCutoff_eq_central M hKM z]
  · funext z
    rw [h.oddCutoff_eq_central M hNM z, k.oddCutoff_eq_central M hKM z]
    have hn : N < (2*(M : ℤ)+1).natAbs := by omega
    have hk : K < (2*(M : ℤ)+1).natAbs := by omega
    rw [(h.distant _ hn).factor_eq (k.distant _ hk) z]

/-- Both entire parity products are independent of admissible central cutoffs and labels. -/
theorem CompletePeriodicParityPairs.products_eq {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N K : ℕ} {ξ η α β : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (k : CompletePeriodicParityPairs hp w φ K α β) :
    evenSpectralPairProduct ξ η = evenSpectralPairProduct α β ∧
    oddSpectralPairProduct ξ η = oddSpectralPairProduct α β := by
  have he : ∀ᶠ M : ℕ in atTop,
      (fun z => evenSpectralPairCutoff ξ η z M) = (fun z => evenSpectralPairCutoff α β z M) ∧
      (fun z => oddSpectralPairCutoff ξ η z M) = (fun z => oddSpectralPairCutoff α β z M) := by
    filter_upwards [eventually_ge_atTop (max N K)] with M hM
    exact h.cutoffs_eq k M (by omega) (by omega)
  constructor
  · funext z
    exact tendsto_nhds_unique
      (((tendstoLocallyUniformlyOn_evenSpectralPairProduct hp ξ η h.left_displacement h.right_displacement).tendsto_at
        (Set.mem_univ z)).congr' (he.mono (fun _ hM => congrFun hM.1 z)))
      ((tendstoLocallyUniformlyOn_evenSpectralPairProduct hp α β k.left_displacement k.right_displacement).tendsto_at
        (Set.mem_univ z))
  · funext z
    exact tendsto_nhds_unique
      (((tendstoLocallyUniformlyOn_oddSpectralPairProduct hp ξ η h.left_displacement h.right_displacement).tendsto_at
        (Set.mem_univ z)).congr' (he.mono (fun _ hM => congrFun hM.2 z)))
      ((tendstoLocallyUniformlyOn_oddSpectralPairProduct hp α β k.left_displacement k.right_displacement).tendsto_at
        (Set.mem_univ z))

/-- Every actual potential has one pair of entire functions for all admissible central cutoffs and labels. -/
theorem exists_uniform_choiceIndependent_actualParityProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U,
        weightedBaseToPair w ψ ∈ pairParitySubspace 0 → ∃ f g : ℂ → ℂ,
          AnalyticOnNhd ℂ f Set.univ ∧ AnalyticOnNhd ℂ g Set.univ ∧
          (∀ z : ℂ,
            (f z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 0 z) ∧
            (g z = 0 ↔ 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w ψ) 1 z)) ∧
          ∀ N : ℕ, ∀ ξ η : ℤ → ℂ, CompletePeriodicParityPairs hp w ψ N ξ η →
            evenSpectralPairProduct ξ η = f ∧ oddSpectralPairProduct ξ η = g := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ heven
  obtain ⟨ξ,η,hd⟩ := h ψ hψ heven N₀ le_rfl
  exact ⟨evenSpectralPairProduct ξ η, oddSpectralPairProduct ξ η,
    analyticOnNhd_evenSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    analyticOnNhd_oddSpectralPairProduct hp ξ η hd.left_displacement hd.right_displacement,
    fun z => ⟨hd.evenProduct_eq_zero_iff z, hd.oddProduct_eq_zero_iff z⟩,
    fun _ _ _ hk => hk.products_eq hd⟩

end NLS.ZakharovShabat
