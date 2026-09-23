import NLS.SequenceSpaces.SquaredReciprocalRows
import NLS.ZakharovShabat.SourcePeriodicGapSummability

/-!
# The squared-gap reciprocal rows of Lemma 10.8

The source gap sequence is in `ℓᵖ`. Squaring it gives an `ℓ^(p/2)`
sequence. Powered Young then puts the reciprocal-square row sums in
the same space, uniformly in the row index, also for `1 < p < 2`.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The squared source gap as an actual coefficient sequence at the
half exponent. -/
def sourcePeriodicSquaredGapCoeff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff (ENNReal.ofReal (p.toReal/2)) := by
  have heq : ENNReal.ofReal (p.toReal/2) = p/2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
      ENNReal.ofReal_toReal hp]
    norm_num
  exact ⟨fun n =>
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n)^2,
    by rw [heq]; exact memℓp_sourcePeriodicSquaredGap hp hp1 ψ⟩

@[simp] theorem sourcePeriodicSquaredGapCoeff_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourcePeriodicSquaredGapCoeff hp hp1 ψ n =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 := by
  simp only [sourcePeriodicSquaredGapCoeff, sourcePeriodicGapDisplacement_apply]

/-- The actual reciprocal-square row sums of gap magnitudes form an
`ℓ^(p/2)` coefficient sequence. -/
theorem exists_sourceSquaredGapReciprocalRows
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ∃ S : Coeff (ENNReal.ofReal (p.toReal/2)),
      (∀ n : ℤ,
        Summable (fun k : ℤ =>
          ‖sourcePeriodicGapDisplacement hp hp1 ψ (n-k)‖^2 *
            (if k = 0 then (0:ℝ) else |(k:ℝ)|^(-(2:ℝ)))) ∧
        S n = ((∑' k : ℤ,
          ‖sourcePeriodicGapDisplacement hp hp1 ψ (n-k)‖^2 *
            (if k = 0 then (0:ℝ) else |(k:ℝ)|^(-(2:ℝ))) : ℝ) : ℂ)) ∧
      ‖S‖ ≤ ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
        ‖squaredReciprocalKernel (min 1 (p.toReal/2))
          (lt_min (by norm_num : (1/2:ℝ)<1)
            (by
              have hpr : 1 < p.toReal :=
                (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
              linarith))‖ := by
  have hpr : 1 < p.toReal :=
    (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  have hr : (1/2:ℝ) < p.toReal/2 := by linarith
  let a := sourcePeriodicSquaredGapCoeff hp hp1 ψ
  let t := min 1 (p.toReal/2)
  let b := squaredReciprocalKernel t (lt_min (by norm_num) hr)
  obtain ⟨S, hS, hbound⟩ := exists_squaredReciprocalRow (p.toReal/2) hr a
  refine ⟨S, ?_, hbound⟩
  intro n
  have hterm (k : ℤ) : ‖a (n-k) * b k‖ =
      ‖sourcePeriodicGapDisplacement hp hp1 ψ (n-k)‖^2 *
        (if k = 0 then (0:ℝ) else |(k:ℝ)|^(-(2:ℝ))) := by
    rw [norm_mul, sourcePeriodicSquaredGapCoeff_apply, norm_pow]
    by_cases hk : k = 0
    · simp [b, hk]
    · simp only [b, squaredReciprocalKernel_apply, if_neg hk,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  constructor
  · exact (hS n).1.congr (fun k => hterm k)
  calc
    S n = ((∑' k : ℤ, ‖a (n-k) * b k‖ : ℝ) : ℂ) := (hS n).2
    _ = ((∑' k : ℤ,
        ‖sourcePeriodicGapDisplacement hp hp1 ψ (n-k)‖^2 *
          (if k = 0 then (0:ℝ) else |(k:ℝ)|^(-(2:ℝ))) : ℝ) : ℂ) := by
      congr 1
      apply tsum_congr
      intro k
      exact hterm k

/-- The physical-index summand in Lemma 10.8, with the diagonal
excluded before taking the reciprocal square. -/
def sourceSquaredGapReciprocalTerm
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (n m : ℤ) : ℝ :=
  if m = n then 0 else
    ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2 *
      |((m-n : ℤ) : ℝ)|^(-(2:ℝ))

/-- The physical row is the same reciprocal-square convolution row. -/
theorem sourceSquaredGapReciprocalTerm_reindex
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    (∑' m : ℤ, sourceSquaredGapReciprocalTerm hp hp1 ψ n m) =
      ∑' k : ℤ, ‖sourcePeriodicGapDisplacement hp hp1 ψ (n-k)‖^2 *
        (if k = 0 then (0:ℝ) else |(k:ℝ)|^(-(2:ℝ))) := by
  rw [← (Equiv.subLeft n).tsum_eq
    (fun m : ℤ => sourceSquaredGapReciprocalTerm hp hp1 ψ n m)]
  apply tsum_congr
  intro k
  change sourceSquaredGapReciprocalTerm hp hp1 ψ n (n-k) = _
  by_cases hk : k = 0
  · subst k
    simp [sourceSquaredGapReciprocalTerm]
  · have hnk : n-k ≠ n := by omega
    simp only [sourceSquaredGapReciprocalTerm, if_neg hnk, if_neg hk]
    rw [show (n-k)-n = -k by ring, Int.cast_neg, abs_neg]

/-- Every physical reciprocal-square row converges, and the entire
sequence of row sums has the claimed `ℓ^(p/2)` bound. -/
theorem exists_sourceSquaredGapPhysicalRows
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    ∃ S : Coeff (ENNReal.ofReal (p.toReal/2)),
      (∀ n : ℤ,
        Summable (sourceSquaredGapReciprocalTerm hp hp1 ψ n) ∧
        S n = ((∑' m : ℤ,
          sourceSquaredGapReciprocalTerm hp hp1 ψ n m : ℝ) : ℂ)) ∧
      ‖S‖ ≤ ‖sourcePeriodicSquaredGapCoeff hp hp1 ψ‖ *
        ‖squaredReciprocalKernel (min 1 (p.toReal/2))
          (lt_min (by norm_num : (1/2:ℝ)<1)
            (by
              have hpr : 1 < p.toReal :=
                (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
              linarith))‖ := by
  obtain ⟨S, hS, hnorm⟩ := exists_sourceSquaredGapReciprocalRows hp hp1 ψ
  refine ⟨S, ?_, hnorm⟩
  intro n
  have hterm (m : ℤ) :
      (‖sourcePeriodicGapDisplacement hp hp1 ψ (n-(n-m))‖^2 *
        (if n-m = 0 then (0:ℝ) else |((n-m):ℝ)|^(-(2:ℝ)))) =
        sourceSquaredGapReciprocalTerm hp hp1 ψ n m := by
    simp only [sub_sub_cancel]
    by_cases hmn : m = n
    · subst m
      simp [sourceSquaredGapReciprocalTerm]
    · have hnm : n-m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmn)
      simp only [sourceSquaredGapReciprocalTerm, if_neg hmn, if_neg hnm]
      have habs : |(n:ℝ)-(m:ℝ)| = |(((m-n:ℤ):ℝ))| := by
        rw [← Int.cast_sub, show n-m = -(m-n) by ring, Int.cast_neg, abs_neg]
      rw [habs]
  have hsum : Summable (sourceSquaredGapReciprocalTerm hp hp1 ψ n) := by
    have h := (hS n).1.comp_injective (Equiv.subLeft n).injective
    exact h.congr (fun m => by
      simpa only [Function.comp_def, Equiv.subLeft_apply, Int.cast_sub] using hterm m)
  refine ⟨hsum, ?_⟩
  rw [(hS n).2, ← sourceSquaredGapReciprocalTerm_reindex hp hp1 ψ n]

end NLS.ZakharovShabat
