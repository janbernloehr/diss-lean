import NLS.ZakharovShabat.ClassicalSignedDiscriminant
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder
import NLS.ZakharovShabat.SourcePhysicalRealL2

/-! # Exact parity enumeration of the actual classical signed spectra -/
noncomputable section
set_option autoImplicit false
open Set NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

private theorem physicalSource_realType (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    IsRealType (CoeffPair.toMax 2 (sourcePhysicalL2Equiv.symm u)) :=
  (mem_realTypeSourceSubmodule _).mp ((mem_physicalRealSubmodule u).mpr hu)

/-- Every physical endpoint has its exact signed discriminant level, including central and collapsed pairs. -/
theorem physicalPeriodicEndpoints_discriminant_of_realType (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (n : ℤ) :
    l2Discriminant u (physicalPeriodicLeft u n) = (if n % 2 = 0 then 2 else -2) ∧
    l2Discriminant u (physicalPeriodicRight u n) = (if n % 2 = 0 then 2 else -2) := by
  have h := canonicalPeriodicEndpoints_discriminant_of_realType (by simp) (by norm_num)
    (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _)
    (isRealType_periodOnePotential _ (physicalSource_realType u hu)) n
  rw [canonicalDiscriminant_eq_l2_source,canonicalDiscriminant_eq_l2_source,
    sourcePhysicalL2_equiv_symm] at h
  simpa only [(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2] using h

/-- Both physical endpoint sequences are real at real-type potentials. -/
theorem physicalPeriodicEndpoints_im_eq_zero_of_realType (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (n : ℤ) :
    (physicalPeriodicLeft u n).im = 0 ∧ (physicalPeriodicRight u n).im = 0 := by
  rw [(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]
  exact canonicalPeriodicEndpoints_im_eq_zero_of_realType (by simp) (by norm_num) _
    (periodOnePotential_mem _) (isRealType_periodOnePotential _ (physicalSource_realType u hu)) n

/-- The physical endpoints are ordered within each pair, with strict separation of consecutive pairs. -/
theorem physicalPeriodicEndpoints_real_order (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (n : ℤ) :
    (physicalPeriodicLeft u n).re ≤ (physicalPeriodicRight u n).re ∧
    (physicalPeriodicRight u n).re < (physicalPeriodicLeft u (n+1)).re := by
  refine ⟨re_le_of_complexLexLE ((physicalPeriodicEndpoints_spec u).within n),?_⟩
  rw [(physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]
  exact canonicalPeriodicRight_re_lt_next_left (by simp) (by norm_num) _
    (periodOnePotential_mem _) (isRealType_periodOnePotential _ (physicalSource_realType u hu)) n

/-- The actual periodic spectrum selects exactly the even physical endpoint indices. -/
theorem physicalPeriodicEndpoints_mem_periodic_iff (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (n : ℤ) :
    (physicalPeriodicLeft u n ∈ classicalSignedSpectrum u 0 ↔ n % 2 = 0) ∧
    (physicalPeriodicRight u n ∈ classicalSignedSpectrum u 0 ↔ n % 2 = 0) := by
  rw [mem_classicalPeriodicSpectrum_iff_discriminant,mem_classicalPeriodicSpectrum_iff_discriminant,
    (physicalPeriodicEndpoints_discriminant_of_realType u hu n).1,
    (physicalPeriodicEndpoints_discriminant_of_realType u hu n).2]
  by_cases hn : n % 2 = 0 <;> norm_num [hn]

/-- The actual antiperiodic spectrum selects exactly the odd physical endpoint indices. -/
theorem physicalPeriodicEndpoints_mem_antiperiodic_iff (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (n : ℤ) :
    (physicalPeriodicLeft u n ∈ classicalSignedSpectrum u 1 ↔ n % 2 = 1) ∧
    (physicalPeriodicRight u n ∈ classicalSignedSpectrum u 1 ↔ n % 2 = 1) := by
  rw [mem_classicalAntiperiodicSpectrum_iff_discriminant,mem_classicalAntiperiodicSpectrum_iff_discriminant,
    (physicalPeriodicEndpoints_discriminant_of_realType u hu n).1,
    (physicalPeriodicEndpoints_discriminant_of_realType u hu n).2]
  by_cases hn : n % 2 = 0
  · have hodd : n % 2 ≠ 1 := by omega
    norm_num [hn,hodd]
  · have hodd : n % 2 = 1 := by omega
    norm_num [hn,hodd]

/-- The actual periodic spectrum is exhausted by the even-index physical endpoint pairs. -/
theorem classicalPeriodicSpectrum_iff_even_endpoint (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) :
    z ∈ classicalSignedSpectrum u 0 ↔ ∃ n : ℤ, n % 2 = 0 ∧
      (physicalPeriodicLeft u n = z ∨ physicalPeriodicRight u n = z) := by
  constructor
  · intro hz
    have hfull : z ∈ physicalPeriodicSpectrum (periodOnePair (sourcePhysicalL2Equiv.symm u)) := by
      rw [physicalPeriodicSpectrum_eq_classicalSigned_union]
      exact Or.inl hz
    obtain ⟨n,hn⟩ := (physicalPeriodicSpectrum_iff_endpoint u z).mp hfull
    refine ⟨n,?_,hn⟩
    rcases hn with h | h
    · exact (physicalPeriodicEndpoints_mem_periodic_iff u hu n).1.mp (h.symm ▸ hz)
    · exact (physicalPeriodicEndpoints_mem_periodic_iff u hu n).2.mp (h.symm ▸ hz)
  · rintro ⟨n,hn,h | h⟩
    · exact h ▸ (physicalPeriodicEndpoints_mem_periodic_iff u hu n).1.mpr hn
    · exact h ▸ (physicalPeriodicEndpoints_mem_periodic_iff u hu n).2.mpr hn

/-- The actual antiperiodic spectrum is exhausted by the odd-index physical endpoint pairs. -/
theorem classicalAntiperiodicSpectrum_iff_odd_endpoint (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) :
    z ∈ classicalSignedSpectrum u 1 ↔ ∃ n : ℤ, n % 2 = 1 ∧
      (physicalPeriodicLeft u n = z ∨ physicalPeriodicRight u n = z) := by
  constructor
  · intro hz
    have hfull : z ∈ physicalPeriodicSpectrum (periodOnePair (sourcePhysicalL2Equiv.symm u)) := by
      rw [physicalPeriodicSpectrum_eq_classicalSigned_union]
      exact Or.inr hz
    obtain ⟨n,hn⟩ := (physicalPeriodicSpectrum_iff_endpoint u z).mp hfull
    refine ⟨n,?_,hn⟩
    rcases hn with h | h
    · exact (physicalPeriodicEndpoints_mem_antiperiodic_iff u hu n).1.mp (h.symm ▸ hz)
    · exact (physicalPeriodicEndpoints_mem_antiperiodic_iff u hu n).2.mp (h.symm ▸ hz)
  · rintro ⟨n,hn,h | h⟩
    · exact h ▸ (physicalPeriodicEndpoints_mem_antiperiodic_iff u hu n).1.mpr hn
    · exact h ▸ (physicalPeriodicEndpoints_mem_antiperiodic_iff u hu n).2.mpr hn

end NLS.ZakharovShabat
