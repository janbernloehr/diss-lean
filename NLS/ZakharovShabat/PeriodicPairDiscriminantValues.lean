import NLS.ZakharovShabat.DiscriminantRolle

/-!
# Discriminant levels at completed periodic pairs

Both endpoints at an index belong to its parity spectrum, so they have
the same discriminant value, either 2 or -2. These are actual original
periodic eigenvalues and are real at real-type potentials, including
central labels and repeated endpoints.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {w : SpectralWeight} {φ : WeightedCoeffPair w.toWeight p}
variable {N : ℕ} {ξ η : ℤ → ℂ}

/-- Completed endpoints at each index have the discriminant level prescribed by that index's parity. -/
theorem CompletePeriodicParityPairs.discriminant_at_roots
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p) (n : ℤ) :
    canonicalDiscriminant hp (weightedBaseToPair w φ) (ξ n) = (if n % 2 = 0 then 2 else -2) ∧
      canonicalDiscriminant hp (weightedBaseToPair w φ) (η n) = (if n % 2 = 0 then 2 else -2) := by
  have hm (r : ℤ) (hr : r = 0 ∨ r = 1) (hn : n % 2 = r % 2) (z : ℂ)
      (hz : ξ n = z ∨ η n = z) : 0 < parityAlgebraicMultiplicity hp (weightedBaseToPair w φ) r z :=
    (h.root_iff r hr z).mp ⟨n,hn,hz⟩
  by_cases hn : n % 2 = 0
  · rw [if_pos hn]
    exact ⟨(canonicalDiscriminant_parity_levels_finite hp hp1 _ h.even_potential (ξ n)).1.mpr
      (hm 0 (Or.inl rfl) (by omega) _ (Or.inl rfl)),
      (canonicalDiscriminant_parity_levels_finite hp hp1 _ h.even_potential (η n)).1.mpr
      (hm 0 (Or.inl rfl) (by omega) _ (Or.inr rfl))⟩
  · rw [if_neg hn]
    exact ⟨(canonicalDiscriminant_parity_levels_finite hp hp1 _ h.even_potential (ξ n)).2.mpr
      (hm 1 (Or.inr rfl) (by omega) _ (Or.inl rfl)),
      (canonicalDiscriminant_parity_levels_finite hp hp1 _ h.even_potential (η n)).2.mpr
      (hm 1 (Or.inr rfl) (by omega) _ (Or.inr rfl))⟩

/-- Every completed endpoint is an original periodic eigenvalue, including central indices. -/
theorem CompletePeriodicParityPairs.roots_mem_periodicSpectrum
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p) (n : ℤ) :
    ξ n ∈ periodicSpectrum hp (weightedBaseToPair w φ) ∧
      η n ∈ periodicSpectrum hp (weightedBaseToPair w φ) := by
  obtain ⟨hx,hy⟩ := h.discriminant_at_roots hp1 n
  constructor
  · apply (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ h.even_potential _).mp
    rw [hx]
    split_ifs <;> norm_num
  · apply (canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ h.even_potential _).mp
    rw [hy]
    split_ifs <;> norm_num

/-- Completed endpoints are real at a real-type potential, independently of their enumeration. -/
theorem CompletePeriodicParityPairs.roots_im_eq_zero_of_realType
    (h : CompletePeriodicParityPairs hp w φ N ξ η) (hp1 : 1 < p)
    (hreal : IsRealType (weightedBaseToPair w φ)) (n : ℤ) : (ξ n).im = 0 ∧ (η n).im = 0 :=
  ⟨periodicSpectrum_im_eq_zero_of_realType hp _ hreal _ (h.roots_mem_periodicSpectrum hp1 n).1,
    periodicSpectrum_im_eq_zero_of_realType hp _ hreal _ (h.roots_mem_periodicSpectrum hp1 n).2⟩

end NLS.ZakharovShabat
