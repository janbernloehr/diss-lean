import NLS.ZakharovShabat.ClassicalSignedMultiplicity
import NLS.ZakharovShabat.OrderedPeriodicParityPairs
import NLS.ZakharovShabat.PeriodicPairDiscriminantValues

/-! # Actual signed physical multiplicities in complete complex parity lists -/
noncomputable section
set_option autoImplicit false
open scoped Classical
namespace NLS.ZakharovShabat

/-- Reindexing one integer parity retains exactly its contribution to a finite sum. -/
theorem finsum_affine_parity {M : Type*} [AddCommMonoid M] (f : ℤ → M) (r : ℤ) :
    (∑ᶠ n : ℤ, f (2*n+r)) = ∑ᶠ k : ℤ, if k % 2 = r % 2 then f k else 0 := by
  have hi : Function.Injective (fun n : ℤ => 2*n+r) := by intro a b hab; dsimp at hab; omega
  have hr : Set.range (fun n : ℤ => 2*n+r) = {k : ℤ | k % 2 = r % 2} := by
    ext k
    constructor
    · rintro ⟨n,rfl⟩
      change (2*n+r) % 2 = r % 2
      omega
    · intro hk
      exact ⟨(k-r)/2,by
        change k % 2 = r % 2 at hk
        change 2*((k-r)/2)+r = k
        omega⟩
  rw [← finsum_mem_range hi,hr]
  simp only [Set.mem_ofPred_eq,finsum_eq_if]

private theorem pair_count_eq (u : IntervalPairL2) (ξ η : ℤ → ℂ) (r : ℤ) (z : ℂ)
    (htotal : (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z)
    (hmem : ∀ n : ℤ, (ξ n ∈ classicalSignedSpectrum u r ↔ n % 2 = r % 2) ∧
      (η n ∈ classicalSignedSpectrum u r ↔ n % 2 = r % 2))
    (hfull : z ∈ classicalSignedSpectrum u r → classicalSignedAlgebraicMultiplicity u r z =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z) :
    (∑ᶠ n : ℤ, ({ξ (2*n+r),η (2*n+r)} : Multiset ℂ).count z) =
      classicalSignedAlgebraicMultiplicity u r z := by
  rw [finsum_affine_parity (fun k => ({ξ k,η k} : Multiset ℂ).count z) r]
  by_cases hz : z ∈ classicalSignedSpectrum u r
  · rw [hfull hz,← htotal]
    apply finsum_congr
    intro n
    by_cases hn : n % 2 = r % 2
    · simp [hn]
    · have hL : ξ n ≠ z := fun he => hn ((hmem n).1.mp (he.symm ▸ hz))
      have hR : η n ≠ z := fun he => hn ((hmem n).2.mp (he.symm ▸ hz))
      simp [hn,Ne.symm hL,Ne.symm hR]
  · have hzero : classicalSignedAlgebraicMultiplicity u r z = 0 := by
      apply Nat.eq_zero_of_not_pos
      exact fun h => hz ((classicalSignedAlgebraicMultiplicity_pos_iff u r z).mp h)
    rw [hzero]
    have hterms : ∀ n : ℤ, (if n % 2 = r % 2 then ({ξ n,η n} : Multiset ℂ).count z else 0) = 0 := by
      intro n
      by_cases hn : n % 2 = r % 2
      · have hL : ξ n ≠ z := fun he => hz (he ▸ (hmem n).1.mpr hn)
        have hR : η n ≠ z := fun he => hz (he ▸ (hmem n).2.mpr hn)
        simp [hn,Ne.symm hL,Ne.symm hR]
      · simp [hn]
    simp only [hterms,finsum_zero]

private theorem physical_base (u : IntervalPairL2) :
    weightedBaseToPair SpectralWeight.one
      (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) =
      periodOnePotential (sourcePhysicalL2Equiv.symm u) := by
  rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]

variable (u : IntervalPairL2) {N : ℕ} {ξ η : ℤ → ℂ}
variable (h : CompletePeriodicParityPairs (by simp) SpectralWeight.one
  (unitBaseEquiv.symm (periodOnePotential (sourcePhysicalL2Equiv.symm u))) N ξ η)
include h

/-- Complete complex parity labels have their exact physical trace level at every index. -/
theorem CompletePeriodicParityPairs.physical_discriminant_at_roots (n : ℤ) :
    l2Discriminant u (ξ n) = (if n % 2 = 0 then 2 else -2) ∧
      l2Discriminant u (η n) = (if n % 2 = 0 then 2 else -2) := by
  have hd := h.discriminant_at_roots (by norm_num) n
  rwa [physical_base,canonicalDiscriminant_eq_l2_source,canonicalDiscriminant_eq_l2_source,
    sourcePhysicalL2_equiv_symm] at hd

/-- The correctly assigned complex parity pairs lie in exactly their actual signed spectrum. -/
theorem CompletePeriodicParityPairs.mem_classicalSignedSpectrum_iff (r : ℤ) (hr : r = 0 ∨ r = 1) (n : ℤ) :
    (ξ n ∈ classicalSignedSpectrum u r ↔ n % 2 = r % 2) ∧
      (η n ∈ classicalSignedSpectrum u r ↔ n % 2 = r % 2) := by
  obtain ⟨hξ,hη⟩ := h.physical_discriminant_at_roots u n
  rcases hr with rfl | rfl
  · rw [mem_classicalPeriodicSpectrum_iff_discriminant,mem_classicalPeriodicSpectrum_iff_discriminant,
      hξ,hη]
    by_cases hn : n % 2 = 0 <;> norm_num [hn]
  · rw [mem_classicalAntiperiodicSpectrum_iff_discriminant,mem_classicalAntiperiodicSpectrum_iff_discriminant,
      hξ,hη]
    by_cases hn : n % 2 = 0
    · have ho : n % 2 ≠ 1 := by omega
      norm_num [hn,ho]
    · have ho : n % 2 = 1 := by omega
      norm_num [hn,ho]

/-- The separately indexed complex parity pairs count the actual classical signed root-space dimension. -/
theorem CompletePeriodicParityPairs.classicalSigned_multiplicity (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    (∑ᶠ n : ℤ, ({ξ (2*n+r),η (2*n+r)} : Multiset ℂ).count z) =
      classicalSignedAlgebraicMultiplicity u r z := by
  apply pair_count_eq u ξ η r z _ (h.mem_classicalSignedSpectrum_iff u r hr)
  · intro hz
    rcases hr with rfl | rfl
    · exact classicalPeriodicMultiplicity_eq_full_of_mem u z hz
    · exact classicalAntiperiodicMultiplicity_eq_full_of_mem u z hz
  · rw [physicalPeriodicAlgebraicMultiplicity_eq]
    change (∑ᶠ n : ℤ, ({ξ n,η n} : Multiset ℂ).count z) =
      periodicAlgebraicMultiplicity (by simp) (periodOnePotential (sourcePhysicalL2Equiv.symm u)) z
    simpa only [physical_base] using h.toEndpoints.global_multiplicity z

/-- Each actual signed spectrum is exhausted by its separately indexed complex parity pairs. -/
theorem CompletePeriodicParityPairs.classicalSigned_exhaustive (r : ℤ) (hr : r = 0 ∨ r = 1) (z : ℂ) :
    z ∈ classicalSignedSpectrum u r ↔ ∃ n : ℤ, ξ (2*n+r) = z ∨ η (2*n+r) = z := by
  rw [← classicalSignedAlgebraicMultiplicity_pos_iff,classicalSignedAlgebraicMultiplicity_eq]
  have hx := h.affine_root_iff r hr z
  simpa only [physical_base] using hx.symm

end NLS.ZakharovShabat
