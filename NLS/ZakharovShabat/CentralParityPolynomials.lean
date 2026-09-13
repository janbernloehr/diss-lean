import NLS.ZakharovShabat.ParityClusterMultiplicity
import NLS.ZakharovShabat.PeriodicSpectralProducts
import NLS.ComplexAnalysis.FiniteProductOrders

/-!
# Central polynomials for the actual parity spectra

The central factors use original parity root-space multiplicities. They split
the full central polynomial exactly, preserve analytic orders, and have finite
root multisets with the counted parity cardinalities. No global root labeling
or discriminant compatibility is assumed.
-/

noncomputable section
open scoped ENNReal ENat
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The finite central polynomial in one parity, with the original Jordan multiplicities. -/
def centralParityPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) (z : ℂ) : ℂ :=
  ∏ ζ ∈ centralPeriodicSpectrum hp φ N, (ζ-z)^(parityAlgebraicMultiplicity hp φ r ζ)

/-- The full central polynomial factors exactly into its two parity polynomials. -/
theorem centralPeriodicPolynomial_eq_parity_mul (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (z : ℂ) :
    centralPeriodicPolynomial hp φ N z =
      centralParityPolynomial hp φ N 0 z * centralParityPolynomial hp φ N 1 z := by
  simp only [centralPeriodicPolynomial, centralParityPolynomial,
    periodicAlgebraicMultiplicity_eq_parity_sum hp φ hφ, pow_add, Finset.prod_mul_distrib]

/-- Every central parity polynomial is entire in the spectral parameter. -/
theorem analyticOnNhd_centralParityPolynomial (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) :
    AnalyticOnNhd ℂ (centralParityPolynomial hp φ N r) Set.univ := by
  intro z _
  exact Finset.analyticAt_fun_prod _ (fun _ _ => by fun_prop)

/-- The zero set retains the central cutoff and the actual parity-domain eigenvector condition. -/
theorem centralParityPolynomial_eq_zero_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (r : ℤ) (z : ℂ) :
    centralParityPolynomial hp φ N r z = 0 ↔ z ∈ centralPeriodicSpectrum hp φ N ∧
      ∃ f : Domain p, f ≠ 0 ∧ f ∈ domainParitySubspace r ∧ spectralPencil hp φ z f = 0 := by
  classical
  rw [← parityAlgebraicMultiplicity_pos_iff hp φ hφ]
  constructor
  · intro h
    obtain ⟨ζ, hζ, hz⟩ := Finset.prod_eq_zero_iff.mp h
    have he : ζ = z := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
    subst ζ
    refine ⟨hζ, Nat.pos_iff_ne_zero.mpr ?_⟩
    intro hm
    simp [hm] at hz
  · rintro ⟨hz, hm⟩
    exact Finset.prod_eq_zero hz (by rw [sub_self, zero_pow (Nat.ne_of_gt hm)])

/-- Extended analytic orders equal the original parity multiplicities, with no infinite-order ambiguity. -/
theorem analyticOrderAt_centralParityPolynomial (hp : p ≠ ⊤) (φ : PairSpace p)
    (N : ℕ) (r : ℤ) (z : ℂ) :
    analyticOrderAt (centralParityPolynomial hp φ N r) z =
      if z ∈ centralPeriodicSpectrum hp φ N then (parityAlgebraicMultiplicity hp φ r z : ℕ∞) else 0 :=
  NLS.ComplexAnalysis.analyticOrderAt_rootPolynomial _ _ z

/-- The central root multiset repeats each original spectral value with its parity multiplicity. -/
def centralParityRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) : Multiset ℂ :=
  ∑ z ∈ centralPeriodicSpectrum hp φ N, Multiset.replicate (parityAlgebraicMultiplicity hp φ r z) z

/-- Root counts in the central multiset are exactly the cutoff parity multiplicities. -/
theorem count_centralParityRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) (z : ℂ) :
    (centralParityRoots hp φ N r).count z =
      if z ∈ centralPeriodicSpectrum hp φ N then parityAlgebraicMultiplicity hp φ r z else 0 := by
  classical
  simp [centralParityRoots, Multiset.count_sum', Multiset.count_replicate]

/-- The central multiset has the total algebraic multiplicity of its parity cluster. -/
theorem card_centralParityRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) :
    (centralParityRoots hp φ N r).card =
      ∑ z ∈ centralPeriodicSpectrum hp φ N, parityAlgebraicMultiplicity hp φ r z := by
  simp [centralParityRoots]

/-- Actual central parity root multisets have the counted cardinalities on one potential neighborhood. -/
theorem exists_uniform_centralParityRoots_card (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 → ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
        (centralParityRoots hp ψ N r).card = if (N : ℤ) % 2 = r % 2 then 2*N+2 else 2*N := by
  simpa only [card_centralParityRoots] using exists_uniform_central_parity_multiplicity_sums hp φ

/-- Membership records precisely the central spectral values with positive parity multiplicity. -/
theorem mem_centralParityRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) (z : ℂ) :
    z ∈ centralParityRoots hp φ N r ↔
      z ∈ centralPeriodicSpectrum hp φ N ∧ 0 < parityAlgebraicMultiplicity hp φ r z := by
  classical
  rw [← Multiset.count_pos, count_centralParityRoots]
  by_cases hz : z ∈ centralPeriodicSpectrum hp φ N <;> simp [hz]

/-- The finite root multiset produces the same central polynomial, including repeated roots. -/
theorem prod_centralParityRoots (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (r : ℤ) (z : ℂ) :
    ((centralParityRoots hp φ N r).map (fun ζ => ζ-z)).prod = centralParityPolynomial hp φ N r z := by
  classical
  rw [Finset.prod_multiset_map_count]
  have hs : (centralParityRoots hp φ N r).toFinset ⊆ centralPeriodicSpectrum hp φ N := by
    intro ζ hζ
    exact ((mem_centralParityRoots hp φ N r ζ).mp (Multiset.mem_toFinset.mp hζ)).1
  calc
    _ = ∏ ζ ∈ centralPeriodicSpectrum hp φ N, (ζ-z)^(centralParityRoots hp φ N r).count ζ := by
      apply Finset.prod_subset hs
      intro ζ _ hζ
      rw [Multiset.count_eq_zero_of_notMem (fun h => hζ (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro ζ hζ
      rw [count_centralParityRoots, if_pos hζ]

/-- The central free polynomial retains precisely the requested signed parity indices. -/
theorem centralParityPolynomial_zero (hp : p ≠ ⊤) (N : ℕ) (r : ℤ) (z : ℂ) :
    centralParityPolynomial hp (0 : PairSpace p) N r z =
      ∏ n ∈ centralParityIndices N r, ((Real.pi : ℂ)*n-z)^2 := by
  classical
  unfold centralParityPolynomial
  rw [centralPeriodicSpectrum_zero, Finset.prod_image]
  · simp only [parityAlgebraicMultiplicity_zero, centralParityIndices, Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro n _
    split_ifs <;> simp
  · intro a _ b _ hab
    exact Int.cast_injective (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) hab)

/-- Free central parity cardinalities hold at every cutoff, including zero. -/
theorem card_centralParityRoots_zero (hp : p ≠ ⊤) (N : ℕ) (r : ℤ) :
    (centralParityRoots hp (0 : PairSpace p) N r).card =
      if (N : ℤ) % 2 = r % 2 then 2*N+2 else 2*N := by
  rw [card_centralParityRoots, ← finrank_centralParityProjection_eq_sum hp 0 (Submodule.zero_mem _) N r]
  exact finrank_range_centralParityProjection_zero hp N r

end NLS.ZakharovShabat
