import NLS.ZakharovShabat.ClassicalSignedMultiplicity

/-! # Exact endpoint counts for actual classical signed algebraic multiplicities -/
noncomputable section
set_option autoImplicit false
namespace NLS.ZakharovShabat

private theorem signedEndpointCount_eq (u : IntervalPairL2) (r : ℤ) (z : ℂ)
    (hmem : ∀ n : ℤ,
      (physicalPeriodicLeft u n ∈ classicalSignedSpectrum u r ↔ n % 2 = r) ∧
      (physicalPeriodicRight u n ∈ classicalSignedSpectrum u r ↔ n % 2 = r))
    (hfull : z ∈ classicalSignedSpectrum u r → classicalSignedAlgebraicMultiplicity u r z =
      physicalPeriodicAlgebraicMultiplicity (periodOnePair (sourcePhysicalL2Equiv.symm u)) z) :
    (∑ᶠ n : ℤ, if n % 2 = r then
      ({physicalPeriodicLeft u n,physicalPeriodicRight u n} : Multiset ℂ).count z else 0) =
      classicalSignedAlgebraicMultiplicity u r z := by
  classical
  by_cases hz : z ∈ classicalSignedSpectrum u r
  · rw [hfull hz, ← physicalPeriodicEndpoints_count_multiplicity]
    apply finsum_congr
    intro n
    by_cases hn : n % 2 = r
    · simp only [hn,if_pos]
    · have hL : physicalPeriodicLeft u n ≠ z := by
        intro he
        exact hn ((hmem n).1.mp (he.symm ▸ hz))
      have hR : physicalPeriodicRight u n ≠ z := by
        intro he
        exact hn ((hmem n).2.mp (he.symm ▸ hz))
      simp [hn,Ne.symm hL,Ne.symm hR]
  · have hzero : classicalSignedAlgebraicMultiplicity u r z = 0 := by
      apply Nat.eq_zero_of_not_pos
      exact fun h => hz ((classicalSignedAlgebraicMultiplicity_pos_iff u r z).mp h)
    rw [hzero]
    have hterms : ∀ n : ℤ, (if n % 2 = r then
        ({physicalPeriodicLeft u n,physicalPeriodicRight u n} : Multiset ℂ).count z else 0) = 0 := by
      intro n
      by_cases hn : n % 2 = r
      · have hL : physicalPeriodicLeft u n ≠ z := by
          intro he
          exact hz (he ▸ (hmem n).1.mpr hn)
        have hR : physicalPeriodicRight u n ≠ z := by
          intro he
          exact hz (he ▸ (hmem n).2.mpr hn)
        simp [hn,Ne.symm hL,Ne.symm hR]
      · simp [hn]
    simp only [hterms,finsum_zero]

/-- The even-index physical endpoint pairs count the full generalized eigenspace
of the actual classical periodic operator, including collapsed pairs. -/
theorem physicalEvenEndpoints_count_classicalPeriodicMultiplicity (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) :
    (∑ᶠ n : ℤ, if n % 2 = 0 then
      ({physicalPeriodicLeft u n,physicalPeriodicRight u n} : Multiset ℂ).count z else 0) =
      classicalSignedAlgebraicMultiplicity u 0 z :=
  signedEndpointCount_eq u 0 z (physicalPeriodicEndpoints_mem_periodic_iff u hu)
    (classicalPeriodicMultiplicity_eq_full_of_mem u z)

/-- The odd-index physical endpoint pairs count the full generalized eigenspace
of the actual classical antiperiodic operator, including collapsed pairs. -/
theorem physicalOddEndpoints_count_classicalAntiperiodicMultiplicity (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) :
    (∑ᶠ n : ℤ, if n % 2 = 1 then
      ({physicalPeriodicLeft u n,physicalPeriodicRight u n} : Multiset ℂ).count z else 0) =
      classicalSignedAlgebraicMultiplicity u 1 z :=
  signedEndpointCount_eq u 1 z (physicalPeriodicEndpoints_mem_antiperiodic_iff u hu)
    (classicalAntiperiodicMultiplicity_eq_full_of_mem u z)

end NLS.ZakharovShabat
