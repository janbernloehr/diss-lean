import NLS.ZakharovShabat.CentralParity

/-!
# Algebraic multiplicities in the actual parity sectors

For even-supported potentials, the periodic root space splits into its even
and odd Fourier parts. Their dimensions count Jordan chains of the respective
parity, and positivity is equivalent to an actual domain eigenvector of that
parity. A spectral value may contribute to both sectors.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Algebraic multiplicity in one Fourier parity sector, including all root chains. -/
def parityAlgebraicMultiplicity (hp : p ≠ ⊤) (φ : PairSpace p) (r : ℤ) (z : ℂ) : ℕ :=
  Module.finrank ℂ ↥(periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r)

/-- Each parity part of a root space is finite dimensional. -/
theorem finiteDimensional_parityRootSpace (hp : p ≠ ⊤) (φ : PairSpace p) (r : ℤ) (z : ℂ) :
    FiniteDimensional ℂ ↥(periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r) := by
  let : FiniteDimensional ℂ (periodicRootSpaceTop hp φ z) := finiteDimensional_periodicRootSpaceTop hp φ z
  exact FiniteDimensional.of_injective (Submodule.inclusion inf_le_left) (Submodule.inclusion_injective _)

/-- The parity mask preserves every full root space of an even potential. -/
theorem pairParityProjection_mem_rootSpace (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (x : PairSpace p)
    (hx : x ∈ periodicRootSpaceTop hp φ z) :
    pairParityProjection r x ∈ periodicRootSpaceTop hp φ z := by
  obtain ⟨w, hw⟩ := resolventSet_nonempty hp φ
  exact mapsTo_periodicRootSpaceTop_of_commute hp φ w z hw _
    (pairParityProjection_commute_resolvent hp φ hφ r w hw) hx

/-- The full original root space is the sum of its two disjoint parity parts. -/
theorem periodicRootSpaceTop_parity_split (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 0) ⊔
      (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 1) = periodicRootSpaceTop hp φ z := by
  apply le_antisymm (sup_le inf_le_left inf_le_left)
  intro x hx
  rw [← pairParityProjection_zero_add_one x]
  exact Submodule.add_mem_sup
    ⟨pairParityProjection_mem_rootSpace hp φ hφ 0 z x hx, pairParityProjection_mem 0 x⟩
    ⟨pairParityProjection_mem_rootSpace hp φ hφ 1 z x hx, pairParityProjection_mem 1 x⟩

/-- The original algebraic multiplicity is the sum of the two parity multiplicities. -/
theorem periodicAlgebraicMultiplicity_eq_parity_sum (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    periodicAlgebraicMultiplicity hp φ z =
      parityAlgebraicMultiplicity hp φ 0 z + parityAlgebraicMultiplicity hp φ 1 z := by
  let : FiniteDimensional ℂ ↥(periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 0) :=
    finiteDimensional_parityRootSpace hp φ 0 z
  let : FiniteDimensional ℂ ↥(periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 1) :=
    finiteDimensional_parityRootSpace hp φ 1 z
  have hd := isCompl_pairParitySubspaces (p := p) |>.disjoint.mono
    (show periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 0 ≤ pairParitySubspace 0 from inf_le_right)
    (show periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 1 ≤ pairParitySubspace 1 from inf_le_right)
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 0) (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace 1)
  rw [periodicRootSpaceTop_parity_split hp φ hφ z, hd.eq_bot, finrank_bot, add_zero] at h
  exact h

/-- A nonzero finite root chain in one parity contains a domain eigenvector of that parity. -/
theorem exists_parity_eigenvector_of_root (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) (n : ℕ) (x : PairSpace p)
    (hx : x ∈ periodicRootSpace hp φ z n) (hr : x ∈ pairParitySubspace r) (hne : x ≠ 0) :
    ∃ f : Domain p, f ≠ 0 ∧ f ∈ domainParitySubspace r ∧ spectralPencil hp φ z f = 0 := by
  induction n generalizing x with
  | zero => exact (hne (show x = 0 from hx)).elim
  | succ n ih =>
    obtain ⟨f, hf, hn⟩ := (mem_periodicRootSpace_succ hp φ z n x).mp hx
    have hfr : f ∈ domainParitySubspace r := (mem_domainParitySubspace r f).mpr (hf ▸ hr)
    by_cases hz : spectralPencil hp φ z f = 0
    · exact ⟨f, fun he => hne (hf.symm.trans (by rw [he, map_zero])), hfr, hz⟩
    · apply ih _ hn _ hz
      rw [← pairParityProjection_eq_self_iff, ← spectralPencil_domainParityProjection hp φ hφ,
        (domainParityProjection_eq_self_iff r f).mpr hfr]

/-- Positive parity multiplicity detects actual eigenvectors in the original weighted domain. -/
theorem parityAlgebraicMultiplicity_pos_iff (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (z : ℂ) :
    0 < parityAlgebraicMultiplicity hp φ r z ↔
      ∃ f : Domain p, f ≠ 0 ∧ f ∈ domainParitySubspace r ∧ spectralPencil hp φ z f = 0 := by
  let : FiniteDimensional ℂ ↥(periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r) :=
    finiteDimensional_parityRootSpace hp φ r z
  rw [parityAlgebraicMultiplicity, Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
  change (periodicRootSpaceTop hp φ z ⊓ pairParitySubspace r ≠ ⊥) ↔ _
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, ⟨hx, hr⟩, hne⟩
    obtain ⟨n, hn⟩ := (mem_periodicRootSpaceTop hp φ z x).mp hx
    exact exists_parity_eigenvector_of_root hp φ hφ r z n x hn hr hne
  · rintro ⟨f, hne, hr, hf⟩
    refine ⟨domainInclusion f, ⟨?_, (mem_domainParitySubspace r f).mp hr⟩, ?_⟩
    · exact (mem_periodicRootSpaceTop hp φ z _).mpr ⟨1,
        (mem_periodicRootSpace_succ hp φ z 0 _).mpr ⟨f, rfl, by simp [hf]⟩⟩
    · exact fun h => hne (domainInclusion_injective (h.trans (map_zero _).symm))

/-- If the full root space has one parity, that sector retains its full multiplicity. -/
theorem parityAlgebraicMultiplicity_eq_of_root_le (hp : p ≠ ⊤) (φ : PairSpace p) (r : ℤ) (z : ℂ)
    (hr : periodicRootSpaceTop hp φ z ≤ pairParitySubspace r) :
    parityAlgebraicMultiplicity hp φ r z = periodicAlgebraicMultiplicity hp φ z := by
  rw [parityAlgebraicMultiplicity, inf_eq_left.mpr hr]
  rfl

/-- A root space of the opposite parity contributes no multiplicity. -/
theorem parityAlgebraicMultiplicity_eq_zero_of_root_le (hp : p ≠ ⊤) (φ : PairSpace p)
    (r s : ℤ) (z : ℂ) (hrs : r % 2 ≠ s % 2)
    (hr : periodicRootSpaceTop hp φ z ≤ pairParitySubspace s) :
    parityAlgebraicMultiplicity hp φ r z = 0 := by
  rw [parityAlgebraicMultiplicity, ((disjoint_pairParitySubspaces s r hrs.symm).mono_left hr).eq_bot,
    finrank_bot]

/-- Both signed free eigenmodes contribute two precisely in their index parity. -/
theorem parityAlgebraicMultiplicity_zero (hp : p ≠ ⊤) (r n : ℤ) :
    parityAlgebraicMultiplicity hp (0 : PairSpace p) r ((Real.pi : ℂ)*n) =
      if n % 2 = r % 2 then 2 else 0 := by
  have hr : periodicRootSpaceTop hp (0 : PairSpace p) ((Real.pi : ℂ)*n) ≤ pairParitySubspace n := by
    rw [periodicRootSpaceTop_zero_eq_range]
    rintro x ⟨a, rfl⟩
    exact freeModeEmbedding_mem_pairParitySubspace n a
  by_cases hn : n % 2 = r % 2
  · rw [if_pos hn]
    have hr' : periodicRootSpaceTop hp (0 : PairSpace p) ((Real.pi : ℂ)*n) ≤ pairParitySubspace r := by
      rw [periodicRootSpaceTop_zero_eq_range]
      rintro x ⟨a, rfl⟩
      rw [← pairParityProjection_eq_self_iff]
      change pairParityProjection r (freeModeEmbedding n a) = freeModeEmbedding n a
      rw [pairParityProjection_freeModeEmbedding, if_pos hn]
    rw [parityAlgebraicMultiplicity_eq_of_root_le hp 0 r _ hr', periodicAlgebraicMultiplicity_zero]
  · rw [if_neg hn]
    exact parityAlgebraicMultiplicity_eq_zero_of_root_le hp 0 r n _ (Ne.symm hn) hr

end NLS.ZakharovShabat
