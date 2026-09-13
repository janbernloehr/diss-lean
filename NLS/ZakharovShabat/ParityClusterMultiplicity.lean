import NLS.ZakharovShabat.ParityRootMultiplicity

/-!
# Parity multiplicity sums in finite spectral clusters

Parity projection distributes over the original direct sum of root spaces.
Thus central contour parity ranks count the actual algebraic multiplicities
of the respective sectors, without assigning a shared eigenvalue exclusively
to either parity.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every individual spectral projection commutes with Fourier parity for even potentials. -/
theorem pairParityProjection_commute_spectralProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) :
    Commute (pairParityProjection r) (periodicSpectralProjection hp φ z) := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  exact commute_periodicSpectralProjection_of_resolvent hp φ w z hw _
    (pairParityProjection_commute_resolvent hp φ hφ r w hw)

/-- Finite spectral cluster projections also commute with parity. -/
theorem pairParityProjection_commute_clusterProjection (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (s : Finset ℂ) :
    Commute (pairParityProjection r) (periodicClusterProjection hp φ s) := by
  classical
  exact Commute.sum_right s _ _ fun z _ => pairParityProjection_commute_spectralProjection hp φ hφ r z

/-- The image of any invariant space under a parity mask equals its parity intersection. -/
theorem map_pairParityProjection_eq_inf (r : ℤ) (M : Submodule ℂ (PairSpace p))
    (hM : ∀ x ∈ M, pairParityProjection r x ∈ M) :
    M.map (pairParityProjection r).toLinearMap = M ⊓ pairParitySubspace r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hM y hy, pairParityProjection_mem r y⟩
  · rintro ⟨hx, hr⟩
    exact ⟨x, hx, (pairParityProjection_eq_self_iff r x).mpr hr⟩

/-- The parity mask preserves every finite periodic spectral cluster. -/
theorem pairParityProjection_mem_clusterSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (s : Finset ℂ) (x : PairSpace p)
    (hx : x ∈ periodicClusterSpace hp φ s) :
    pairParityProjection r x ∈ periodicClusterSpace hp φ s := by
  rw [← range_periodicClusterProjection] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨pairParityProjection r y, (DFunLike.congr_fun
    (pairParityProjection_commute_clusterProjection hp φ hφ r s).eq y).symm⟩

/-- Taking a parity part commutes with the finite direct sum of original root spaces. -/
theorem periodicClusterSpace_inf_parity_eq (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (s : Finset ℂ) :
    periodicClusterSpace hp φ s ⊓ pairParitySubspace r =
      ⨆ z ∈ s, periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r := by
  rw [← map_pairParityProjection_eq_inf r _ (pairParityProjection_mem_clusterSpace hp φ hφ r s)]
  simp only [periodicClusterSpace, Submodule.map_iSup,
    map_pairParityProjection_eq_inf r _ (pairParityProjection_mem_rootSpace hp φ hφ r _)]

/-- A parity part of a finite cluster is finite dimensional. -/
theorem finiteDimensional_parityClusterSpace (hp : p ≠ ⊤) (φ : PairSpace p) (r : ℤ) (s : Finset ℂ) :
    FiniteDimensional ℂ ↥(periodicClusterSpace hp φ s ⊓ pairParitySubspace r) := by
  let : FiniteDimensional ℂ (periodicClusterSpace hp φ s) := finiteDimensional_periodicClusterSpace hp φ s
  exact FiniteDimensional.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

/-- Finite parity cluster dimensions are sums of the actual parity algebraic multiplicities. -/
theorem finrank_periodicClusterSpace_inf_parity (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (s : Finset ℂ) :
    Module.finrank ℂ ↥(periodicClusterSpace hp φ s ⊓ pairParitySubspace r) =
      ∑ z ∈ s, parityAlgebraicMultiplicity hp φ r z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [periodicClusterSpace_empty, bot_inf_eq, finrank_bot, Finset.sum_empty]
  | @insert z s hz ih =>
    let : FiniteDimensional ℂ ↥(periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r) :=
      finiteDimensional_parityRootSpace hp φ r z
    let : FiniteDimensional ℂ ↥(periodicClusterSpace hp φ s ⊓ pairParitySubspace r) :=
      finiteDimensional_parityClusterSpace hp φ r s
    have he : periodicClusterSpace hp φ (insert z s) ⊓ pairParitySubspace r =
        (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r) ⊔
          (periodicClusterSpace hp φ s ⊓ pairParitySubspace r) := by
      simp only [periodicClusterSpace_inf_parity_eq hp φ hφ, Finset.iSup_insert]
    have hd := (disjoint_periodicRootSpaceTop_clusterSpace hp φ s z hz).mono
      (show periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r ≤ periodicRootSpaceTop hp φ z from inf_le_left)
      (show periodicClusterSpace hp φ s ⊓ pairParitySubspace r ≤ periodicClusterSpace hp φ s from inf_le_left)
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r) (periodicClusterSpace hp φ s ⊓ pairParitySubspace r)
    rw [hd.eq_bot, finrank_bot, add_zero, ih] at h
    rw [he, Finset.sum_insert hz]
    exact h

/-- The central parity projector counts precisely the corresponding central root multiplicities. -/
theorem finrank_centralParityProjection_eq_sum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (N : ℕ) (r : ℤ) :
    Module.finrank ℂ (centralParityProjection hp φ N r).range =
      ∑ z ∈ centralPeriodicSpectrum hp φ N, parityAlgebraicMultiplicity hp φ r z := by
  rw [range_centralParityProjection hp φ N r
    (pairParityProjection_commute_clusterProjection hp φ hφ r _),
    centralSpectralProjection, range_periodicClusterProjection, finrank_periodicClusterSpace_inf_parity hp φ hφ]

/-- On one open convex neighborhood, every large central cutoff has the exact parity multiplicity counts. -/
theorem exists_uniform_central_parity_multiplicity_sums (hp : p ≠ ⊤) (φ : PairSpace p) :
    ∃ N₀ : ℕ, ∃ U : Set (PairSpace p), 0 < N₀ ∧ IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 → ∀ N : ℕ, N₀ ≤ N → ∀ r : ℤ,
        (∑ z ∈ centralPeriodicSpectrum hp ψ N, parityAlgebraicMultiplicity hp ψ r z) =
          if (N : ℤ) % 2 = r % 2 then 2*N+2 else 2*N := by
  obtain ⟨N₀, U, hN₀, ho, hc, hφ, h0, h⟩ := exists_uniform_central_parity_ranks hp φ
  refine ⟨N₀, U, hN₀, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ heven N hN r
  rw [← finrank_centralParityProjection_eq_sum hp ψ heven N r]
  exact (h ψ hψ heven N hN r).1

end NLS.ZakharovShabat
