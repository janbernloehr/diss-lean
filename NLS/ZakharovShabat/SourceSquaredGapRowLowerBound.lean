import NLS.ZakharovShabat.SourceSquaredGapReciprocalRows

/-!
# A lower bound for the reciprocal-square gap row

The neighboring term shows that improved summability of the absolute
gap row forces the same improvement for the squared gaps. This isolates
the sequence-space obstruction in Remark 10.9; it does not construct
a source whose gaps fail a stronger exponent.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The row centered one index to the right contains the full squared gap. -/
theorem squared_sourceGap_le_neighbor_row (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) :
    ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 ≤
      ∑' j : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ (m+1) j := by
  have hs := ((exists_sourceSquaredGapPhysicalRows hp hp1 ψ).choose_spec.1 (m+1)).1
  have ht := hs.le_tsum m (fun j _ => by
    unfold sourceSquaredGapReciprocalTerm
    split_ifs <;> positivity)
  simpa [sourceSquaredGapReciprocalTerm,show m ≠ m+1 by omega,
    show m-(m+1) = -1 by ring] using ht

/-- A stronger exponent for the absolute row requires that exponent for the squared gaps. -/
theorem memℓp_squared_sourceGap_of_physicalRows {r : ℝ≥0∞}
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hr : 0 < r.toReal) (ψ : CoeffPair p)
    (hrow : Memℓp (fun n : ℤ =>
      ((∑' j : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n j : ℝ):ℂ)) r) :
    Memℓp (fun m : ℤ => (sourcePeriodicGapDisplacement hp hp1 ψ m)^2) r := by
  have hs : Memℓp (fun m : ℤ =>
      ((∑' j : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ (m+1) j : ℝ):ℂ)) r := by
    rw [memℓp_gen_iff hr]
    exact (Equiv.addRight (1:ℤ)).summable_iff.mpr (hrow.summable hr)
  apply hs.mono'
  intro m
  have hnonneg : 0 ≤ ∑' j : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ (m+1) j := by
    apply tsum_nonneg
    intro j
    unfold sourceSquaredGapReciprocalTerm
    split_ifs <;> positivity
  rw [norm_pow,Complex.norm_real,Real.norm_of_nonneg hnonneg]
  exact squared_sourceGap_le_neighbor_row hp hp1 ψ m

end NLS.ZakharovShabat
