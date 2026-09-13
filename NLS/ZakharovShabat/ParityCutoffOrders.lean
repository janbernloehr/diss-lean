import NLS.ZakharovShabat.ActualParityProductIndependence

/-!
# Exact orders of sufficiently large parity cutoffs

The intrinsic central polynomials retain the original parity root-space
multiplicities. The extra odd boundary pair eventually lies outside any
fixed spectral parameter's central box.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every fixed point eventually belongs to all doubled central boxes. -/
theorem eventually_mem_doubledCentralSpectralBox (z : ℂ) :
    ∀ᶠ M : ℕ in atTop, z ∈ centralSpectralBox (2*M) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (|z.re|/Real.pi) |z.im|)
  have hre : |z.re| < (K : ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (lt_of_le_of_lt (le_max_left _ _) hK)
  have him : |z.im| ≤ (K : ℝ) := (lt_of_le_of_lt (le_max_right _ _) hK).le
  have hz : z ∈ centralSpectralBox K := ⟨by linarith [Real.pi_pos], him⟩
  filter_upwards [eventually_ge_atTop K] with M hM
  exact centralSpectralBox_mono (by omega) hz

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A resolvent parameter has zero parity multiplicity, for any potential. -/
theorem parityAlgebraicMultiplicity_eq_zero_of_not_mem (hp : p ≠ ⊤) (φ : PairSpace p)
    (r : ℤ) (z : ℂ) (hz : z ∉ periodicSpectrum hp φ) :
    parityAlgebraicMultiplicity hp φ r z = 0 := by
  have hres : z ∈ resolventSet hp φ := by
    simpa only [periodicSpectrum, Set.mem_compl_iff, not_not] using hz
  unfold parityAlgebraicMultiplicity
  rw [periodicRootSpaceTop_eq_bot_of_mem_resolventSet hp φ z hres, bot_inf_eq, finrank_bot]

/-- Inside the central box, the parity polynomial has exactly the original parity order. -/
theorem analyticOrderAt_centralParityPolynomial_of_mem_box (hp : p ≠ ⊤) (φ : PairSpace p)
    (K : ℕ) (r : ℤ) (z : ℂ) (hz : z ∈ centralSpectralBox K) :
    analyticOrderAt (centralParityPolynomial hp φ K r) z =
      (parityAlgebraicMultiplicity hp φ r z : ℕ∞) := by
  classical
  rw [analyticOrderAt_centralParityPolynomial]
  split_ifs with hc
  · rfl
  · have hn : z ∉ periodicSpectrum hp φ := fun hs =>
      hc ((mem_centralPeriodicSpectrum hp φ K z).mpr ⟨hs,hz⟩)
    rw [parityAlgebraicMultiplicity_eq_zero_of_not_mem hp φ r z hn, Nat.cast_zero]

private theorem normalized_parity_order (hp : p ≠ ⊤) (φ : PairSpace p)
    (K : ℕ) (r : ℤ) (z c : ℂ) (hc : c ≠ 0) (hz : z ∈ centralSpectralBox K) :
    analyticOrderAt (fun t => c * centralParityPolynomial hp φ K r t / centralParityNormalization K r) z =
      (parityAlgebraicMultiplicity hp φ r z : ℕ∞) := by
  have ha := (analyticOnNhd_centralParityPolynomial hp φ K r) z (Set.mem_univ z)
  rw [NLS.ComplexAnalysis.analyticOrderAt_div_const (fun t => c * centralParityPolynomial hp φ K r t) z _ (centralParityNormalization_ne_zero K r)
    ((analyticAt_const (v := c)).mul ha)]
  change analyticOrderAt ((fun _ => c) * centralParityPolynomial hp φ K r) z = _
  rw [analyticOrderAt_mul analyticAt_const ha,
    analyticOrderAt_eq_zero.mpr (Or.inr hc), zero_add,
    analyticOrderAt_centralParityPolynomial_of_mem_box hp φ K r z hz]

/-- Once the central box contains the parameter, both literal cutoffs have its exact parity orders. -/
theorem CompletePeriodicParityPairs.cutoff_orders {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (M : ℕ) (hM : N ≤ 2*M)
    (z : ℂ) (hz : z ∈ centralSpectralBox (2*M)) :
    analyticOrderAt (fun t => evenSpectralPairCutoff ξ η t M) z =
      (parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 0 z : ℕ∞) ∧
    analyticOrderAt (fun t => oddSpectralPairCutoff ξ η t M) z =
      (parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 1 z : ℕ∞) := by
  have he : (fun t => evenSpectralPairCutoff ξ η t M) =
      (fun t => (-1 : ℂ)*centralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 0 t /
        centralParityNormalization (2*M) 0) := by
    funext t
    rw [h.evenCutoff_eq_central M hM t, neg_one_mul]
  have ho : (fun t => oddSpectralPairCutoff ξ η t M) =
      (fun t => 4*centralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 1 t /
        centralParityNormalization (2*M) 1) * (fun t => spectralPairFactor ξ η t (2*(M : ℤ)+1)) :=
    funext (h.oddCutoff_eq_central M hM)
  have hpos : 0 < 2*M := lt_of_lt_of_le h.counting.cutoff_pos hM
  have hn : 2*M < (2*(M : ℤ)+1).natAbs := by omega
  have hfactor : analyticOrderAt (fun t => spectralPairFactor ξ η t (2*(M : ℤ)+1)) z = 0 := by
    apply (h.distant _ (lt_of_le_of_lt hM hn)).factor_order_zero ξ η z
    intro hmem
    exact (centralBox_disjoint_periodicDisk (2*M) hpos _ hn).le_bot
      ⟨hz, ((mem_enclosedPeriodicSpectrum hp _ _ z _).mp hmem).2⟩
  constructor
  · rw [he]
    exact normalized_parity_order hp _ _ 0 z (-1) (by norm_num) hz
  · have ha : AnalyticAt ℂ (fun t => 4*centralParityPolynomial hp (weightedBaseToPair w φ) (2*M) 1 t /
        centralParityNormalization (2*M) 1) z :=
      ((analyticAt_const (v := (4 : ℂ))).mul
        ((analyticOnNhd_centralParityPolynomial hp _ (2*M) 1) z (Set.mem_univ z))).div
          analyticAt_const (centralParityNormalization_ne_zero _ _)
    rw [ho, analyticOrderAt_mul ha
      ((analyticOnNhd_spectralPairFactor ξ η (2*(M : ℤ)+1) Set.univ) z (Set.mem_univ z)), hfactor, add_zero]
    exact normalized_parity_order hp _ _ 1 z 4 (by norm_num) hz

/-- Exact original parity orders stabilize at every point, including nonspectral and lattice points. -/
theorem CompletePeriodicParityPairs.eventually_cutoff_orders {hp : p ≠ ⊤} {w : SpectralWeight}
    {φ : WeightedCoeffPair w.toWeight p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (z : ℂ) :
    ∀ᶠ M : ℕ in atTop,
      analyticOrderAt (fun t => evenSpectralPairCutoff ξ η t M) z =
        (parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 0 z : ℕ∞) ∧
      analyticOrderAt (fun t => oddSpectralPairCutoff ξ η t M) z =
        (parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) 1 z : ℕ∞) := by
  filter_upwards [eventually_mem_doubledCentralSpectralBox z, eventually_ge_atTop N] with M hz hM
  exact h.cutoff_orders M (by omega) z hz

end NLS.ZakharovShabat
