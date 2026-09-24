import NLS.ZakharovShabat.SourceStandardRootNormalizedFactorSign

/-!
# Signs of symmetric omitted-root factors

The literal symmetric omitted product groups the factors at `k` and
`-k`. On a real gap each retained factor is real. We determine the
sign of each paired block from the relative order of its indices.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real part of an omitted symmetric pair is the product of its
two real normalized factors, replacing an omitted member by one. -/
theorem sourceStandardRootOmittedPairedFactor_re_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (j : ℕ) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let k : ℤ := (j:ℤ)+1
    let f (m : ℤ) := sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m
    (sourceStandardRootOmittedPairedFactor hp hp1 ψ (x:ℂ) n j).re =
      (if k=n then 1 else (f k).re) *
        (if -k=n then 1 else (f (-k)).re) := by
  let k : ℤ := (j:ℤ)+1
  let f (m : ℤ) := sourceStandardRoot hp hp1 ψ m (x:ℂ) /
    singleSpectralDenominator m
  have hpos : (if k=n then (1:ℂ) else f k) =
      (((if k=n then 1 else (f k).re):ℝ):ℂ) := by
    by_cases h : k=n
    · simp [h]
    · simpa [h] using
        sourceStandardRoot_normalized_eq_ofReal_off_selected_realGap
          hp hp1 ψ hreal h hx
  have hneg : (if -k=n then (1:ℂ) else f (-k)) =
      (((if -k=n then 1 else (f (-k)).re):ℝ):ℂ) := by
    by_cases h : -k=n
    · simp [h]
    · simpa [h] using
        sourceStandardRoot_normalized_eq_ofReal_off_selected_realGap
          hp hp1 ψ hreal h hx
  change ((if k=n then (1:ℂ) else f k) *
    (if -k=n then (1:ℂ) else f (-k))).re =
      (if k=n then 1 else (f k).re) *
        (if -k=n then 1 else (f (-k)).re)
  rw [hpos,hneg]
  simp

/-- Every paired block strictly below the selected absolute index
contributes one negative sign to the omitted product. -/
theorem sourceStandardRootOmittedPairedFactor_re_neg_of_lt_natAbs
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (j : ℕ) (hj : j+1 < n.natAbs) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceStandardRootOmittedPairedFactor hp hp1 ψ (x:ℂ) n j).re < 0 := by
  let k : ℤ := (j:ℤ)+1
  let f (m : ℤ) := sourceStandardRoot hp hp1 ψ m (x:ℂ) /
    singleSpectralDenominator m
  have hk : 0 < k := by dsimp [k]; omega
  have hpair := sourceStandardRootOmittedPairedFactor_re_eq
    hp hp1 ψ hreal n j hx
  change (sourceStandardRootOmittedPairedFactor hp hp1 ψ (x:ℂ) n j).re =
    (if k=n then 1 else (f k).re) *
      (if -k=n then 1 else (f (-k)).re) at hpair
  rw [hpair]
  by_cases hn : 0 < n
  · have hkn : k < n := by dsimp [k] at *; omega
    have hnegk : -k < n := by omega
    have hknNe : k ≠ n := ne_of_lt hkn
    have hnegNe : -k ≠ n := ne_of_lt hnegk
    simp only [if_neg hknNe, if_neg hnegNe]
    have hfk : (f k).re < 0 :=
      sourceStandardRoot_normalized_re_neg_of_nonneg_before
        hp hp1 ψ hreal hk.le hkn hx
    have hfn : 0 < (f (-k)).re :=
      sourceStandardRoot_normalized_re_pos_of_neg_before
        hp hp1 ψ hreal (by omega) hnegk hx
    exact mul_neg_of_neg_of_pos hfk hfn
  · have hnneg : n < 0 := by dsimp [k] at *; omega
    have hnk : n < -k := by dsimp [k] at *; omega
    have hnkp : n < k := by omega
    have hknNe : k ≠ n := Ne.symm (ne_of_lt hnkp)
    have hnegNe : -k ≠ n := Ne.symm (ne_of_lt hnk)
    simp only [if_neg hknNe, if_neg hnegNe]
    have hfk : 0 < (f k).re :=
      sourceStandardRoot_normalized_re_pos_of_nonneg_after
        hp hp1 ψ hreal hk.le hnkp hx
    have hfn : (f (-k)).re < 0 :=
      sourceStandardRoot_normalized_re_neg_of_neg_after
        hp hp1 ψ hreal (by omega) hnk hx
    exact mul_neg_of_pos_of_neg hfk hfn

/-- Every paired block at or above the selected absolute index is
positive; the block containing the omitted index has one positive
retained factor. -/
theorem sourceStandardRootOmittedPairedFactor_re_pos_of_natAbs_le
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (j : ℕ) (hj : n.natAbs ≤ j+1) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (sourceStandardRootOmittedPairedFactor hp hp1 ψ (x:ℂ) n j).re := by
  let k : ℤ := (j:ℤ)+1
  let f (m : ℤ) := sourceStandardRoot hp hp1 ψ m (x:ℂ) /
    singleSpectralDenominator m
  have hk : 0 < k := by dsimp [k]; omega
  have hpair := sourceStandardRootOmittedPairedFactor_re_eq
    hp hp1 ψ hreal n j hx
  change (sourceStandardRootOmittedPairedFactor hp hp1 ψ (x:ℂ) n j).re =
    (if k=n then 1 else (f k).re) *
      (if -k=n then 1 else (f (-k)).re) at hpair
  rw [hpair]
  by_cases hnpos : 0 < n
  · have hnegk : -k < n := by omega
    have hnegNe : -k ≠ n := ne_of_lt hnegk
    have hfn : 0 < (f (-k)).re :=
      sourceStandardRoot_normalized_re_pos_of_neg_before
        hp hp1 ψ hreal (by omega) hnegk hx
    by_cases hkn : k = n
    · simp only [if_pos hkn, if_neg hnegNe, one_mul]
      exact hfn
    · have hnk : n < k := by dsimp [k] at *; omega
      have hfk : 0 < (f k).re :=
        sourceStandardRoot_normalized_re_pos_of_nonneg_after
          hp hp1 ψ hreal hk.le hnk hx
      simp only [if_neg hkn, if_neg hnegNe]
      exact mul_pos hfk hfn
  · by_cases hnneg : n < 0
    · have hnk : n < k := by omega
      have hknNe : k ≠ n := Ne.symm (ne_of_lt hnk)
      have hfk : 0 < (f k).re :=
        sourceStandardRoot_normalized_re_pos_of_nonneg_after
          hp hp1 ψ hreal hk.le hnk hx
      by_cases hnegk : -k = n
      · simp only [if_neg hknNe, if_pos hnegk, mul_one]
        exact hfk
      · have hnegLess : -k < n := by dsimp [k] at *; omega
        have hfn : 0 < (f (-k)).re :=
          sourceStandardRoot_normalized_re_pos_of_neg_before
            hp hp1 ψ hreal (by omega) hnegLess hx
        simp only [if_neg hknNe, if_neg hnegk]
        exact mul_pos hfk hfn
    · have hn : n = 0 := by omega
      subst n
      have hknNe : k ≠ (0:ℤ) := ne_of_gt hk
      have hnegNe : -k ≠ (0:ℤ) := ne_of_lt (by omega : -k < 0)
      have hfk : 0 < (f k).re :=
        sourceStandardRoot_normalized_re_pos_of_nonneg_after
          hp hp1 ψ hreal hk.le hk hx
      have hfn : 0 < (f (-k)).re :=
        sourceStandardRoot_normalized_re_pos_of_neg_before
          hp hp1 ψ hreal (by omega) (by omega) hx
      simp only [if_neg hknNe, if_neg hnegNe]
      exact mul_pos hfk hfn

end NLS.ZakharovShabat
