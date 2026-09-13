import NLS.ZakharovShabat.CanonicalPeriodicProduct

/-!
# Uniform bounds for the central spectral correction

The central spectral box bounds each root, while the counting theorem fixes
the total degree. These bounds do not require continuous choices of roots.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The central polynomials are uniformly bounded on compact spectral sets for every counted potential. -/
theorem exists_bound_centralPeriodicPolynomial (hp : p ≠ ⊤) (N : ℕ)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : PairSpace p, PeriodicCountingData hp φ N →
      ∀ z ∈ K, ‖centralPeriodicPolynomial hp φ N z‖ ≤ B := by
  obtain ⟨A,hA,hroot⟩ := (isBounded_centralSpectralBox N).exists_pos_norm_le
  obtain ⟨R,hR,hz⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨(A+R)^(4*N+2),by positivity,fun φ hc z hzk => ?_⟩
  unfold centralPeriodicPolynomial
  calc
    _ ≤ ∏ a ∈ centralPeriodicSpectrum hp φ N, ‖(a-z)^periodicAlgebraicMultiplicity hp φ a‖ :=
      Finset.norm_prod_le _ _
    _ ≤ ∏ a ∈ centralPeriodicSpectrum hp φ N, (A+R)^periodicAlgebraicMultiplicity hp φ a := by
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro a ha
      rw [norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le a z).trans
        (add_le_add (hroot a ((mem_centralPeriodicSpectrum hp φ N a).mp ha).2) (hz z hzk))
    _ = (A+R)^(4*N+2) := by rw [Finset.prod_pow_eq_pow_sum, hc.central_multiplicity]

/-- The central quotient has one bound over all counted potentials on each off-lattice compact set. -/
theorem exists_bound_centralPeriodicQuotient (hp : p ≠ ⊤) (N : ℕ)
    (K : Set ℂ) (hK : IsCompact K) (hKl : K ⊆ freeLatticeᶜ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ φ : PairSpace p, PeriodicCountingData hp φ N →
      ∀ z ∈ K, ‖centralPeriodicPolynomial hp φ N z / centralFreePolynomial N z‖ ≤ B := by
  obtain ⟨A,hA,hb⟩ := exists_bound_centralPeriodicPolynomial hp N K hK
  have hc : ContinuousOn (fun z => (centralFreePolynomial N z)⁻¹) K := by
    apply ContinuousOn.inv₀
    · unfold centralFreePolynomial
      fun_prop
    · exact fun z hz => centralFreePolynomial_ne_zero N z (hKl hz)
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨A*max R 0,mul_nonneg hA (le_max_right _ _),fun φ hφ z hz => ?_⟩
  rw [div_eq_mul_inv, norm_mul]
  exact mul_le_mul (hb φ hφ z hz) ((hR z hz).trans (le_max_left _ _)) (norm_nonneg _) hA

/-- Completing an already free central block changes nothing. -/
theorem centralFreeCompletion_eq_self (N : ℕ) (ξ : ℤ → ℂ)
    (h : ∀ n : ℤ, n.natAbs ≤ N → ξ n = (Real.pi : ℂ)*n) :
    centralFreeCompletion N ξ = ξ := by
  funext n
  unfold centralFreeCompletion
  split_ifs with hn
  · rfl
  · exact (h n (by omega)).symm

/-- Exact restoration of the central, free, and relative factors in every large intrinsic polynomial. -/
theorem normalizedCentralPeriodicPolynomial_eq_relative (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N M : ℕ) (hNM : N ≤ M) (ξ η : ℤ → ℂ)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (hfree : ∀ n : ℤ, n.natAbs ≤ N → ξ n = (Real.pi : ℂ)*n ∧ η n = (Real.pi : ℂ)*n)
    (z : ℂ) (hz : z ∉ freeLattice) :
    normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w φ) M z =
      (centralPeriodicPolynomial hp (weightedBaseToPair w φ) N z / centralFreePolynomial N z) *
        ((-4*freeSpectralPartialProduct Real.pi z M) *
          ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), spectralRelativeFactor ξ z n*spectralRelativeFactor η z n) := by
  rw [← periodicSpectralPolynomialCutoff_eq_normalizedCentral hp w φ N M hNM ξ η hc hr]
  rw [periodicSpectralPolynomialCutoff_eq hp _ N ξ η M hNM ⟨z,hz⟩]
  unfold periodicSpectralProductCutoff
  rw [centralFreeCompletion_eq_self N ξ (fun n hn => (hfree n hn).1),
    centralFreeCompletion_eq_self N η (fun n hn => (hfree n hn).2),
    spectralPairPartialProduct_eq ξ η z hz M]

end NLS.ZakharovShabat
