import NLS.SequenceSpaces.CompactRowMajorant
import NLS.SequenceSpaces.PuncturedLattice
import NLS.SequenceSpaces.ConjugateDuality

/-!
# Compactness from punctured reciprocal matrix bounds

The off-diagonal entries in Lemma 12.6 are bounded by a common `ℓᵖ`
sequence in the output index times `1 / |m-r|`. A translated
punctured reciprocal sequence belongs to the conjugate coefficient
space, uniformly in the output index. Hölder's inequality therefore
turns the entrywise bound into the row majorant needed for compactness.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [Fact (1 ≤ p)] [p.HolderConjugate q] in
/-- The translated punctured lattice has precisely the absolute
off-diagonal reciprocal entries. -/
theorem norm_shift_puncturedLattice_apply (hq : 1 < q) (m r : ℤ) :
    ‖(shift m (puncturedLattice q hq)) r‖ =
      if r = m then 0 else |((r - m : ℤ) : ℝ)|⁻¹ := by
  rw [shift_apply, puncturedLattice_apply]
  by_cases hrm : r = m
  · subst r
    simp
  · rw [if_neg (sub_ne_zero.mpr hrm), if_neg hrm]
    simp only [norm_inv, Complex.norm_intCast]

omit [Fact (1 ≤ p)] in
/-- The norm of each kernel row is bounded by the corresponding
majorant entry times the fixed reciprocal-lattice norm. -/
theorem norm_puncturedKernel_row_le (hp : p ≠ ⊤)
    (b : Coeff p) (k : ℤ → Coeff q)
    (hentry : ∀ m r : ℤ,
      ‖k m r‖ ≤ ‖b m‖ *
        ‖(shift m (puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top))) r‖)
    (m : ℤ) :
    ‖k m‖ ≤ ‖b m‖ *
      ‖puncturedLattice q
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)‖ := by
  let c : Coeff q := puncturedLattice q
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)
  calc
    ‖k m‖ ≤ ‖(‖b m‖ : ℂ) • shift m c‖ := by
      apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
      intro r
      simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg (b m))] using hentry m r
    _ = ‖b m‖ * ‖c‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg (b m)), norm_shift]

/-- A represented operator is compact when its kernel entries have
the punctured reciprocal bound with one `ℓᵖ` output majorant. -/
theorem isCompactOperator_of_puncturedKernelMajorant
    (hp : p ≠ ⊤) (ι : E →L[ℂ] Coeff p)
    (hι : ∀ a : E, ‖ι a‖ ≤ ‖a‖)
    (T : E →L[ℂ] Coeff p) (b : Coeff p) (k : ℤ → Coeff q)
    (hrow : ∀ (m : ℤ) (a : E), T a m = dualPairing (ι a) (k m))
    (hentry : ∀ m r : ℤ,
      ‖k m r‖ ≤ ‖b m‖ *
        ‖(shift m (puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top))) r‖) :
    IsCompactOperator T := by
  let c : Coeff q := puncturedLattice q
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top)
  let B : Coeff p := (‖c‖ : ℂ) • b
  apply isCompactOperator_of_rowMajorant hp T B
  intro m a
  have hk : ‖k m‖ ≤ ‖b m‖ * ‖c‖ :=
    norm_puncturedKernel_row_le hp b k hentry m
  calc
    ‖T a m‖ = ‖dualPairing (ι a) (k m)‖ := by rw [hrow]
    _ ≤ ‖ι a‖ * ‖k m‖ := norm_dualPairing_le _ _
    _ ≤ ‖ι a‖ * (‖b m‖ * ‖c‖) :=
      mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ ≤ ‖a‖ * (‖b m‖ * ‖c‖) :=
      mul_le_mul_of_nonneg_right (hι a)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ‖B m‖ * ‖a‖ := by
      simp only [B, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg c)]
      ring

/-- The same matrix criterion for the omitted-coordinate psi parameter
space, with the input and output interpreted as ambient sequences. -/
theorem isCompactOperator_deleted_of_puncturedKernelMajorant
    (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (k : ℤ → Coeff q)
    (hrow : ∀ (m : ℤ) (a : DeletedCoeff p n),
      ((T a : DeletedCoeff p n) : Coeff p) m =
        dualPairing (a : Coeff p) (k m))
    (hentry : ∀ m r : ℤ,
      ‖k m r‖ ≤ ‖b m‖ *
        ‖(shift m (puncturedLattice q
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top))) r‖) :
    IsCompactOperator T := by
  let ι : DeletedCoeff p n →L[ℂ] Coeff p :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have hι (a : DeletedCoeff p n) : ‖ι a‖ ≤ ‖a‖ := le_refl _
  have hcompact : IsCompactOperator (ι.comp T) :=
    isCompactOperator_of_puncturedKernelMajorant hp ι hι (ι.comp T)
      b k hrow hentry
  have hfactor : T = (deleteCoordinateTo n).comp (ι.comp T) := by
    apply ContinuousLinearMap.ext
    intro a
    apply Subtype.ext
    exact ((deleteCoordinate_eq_self_iff n
      ((T a : DeletedCoeff p n) : Coeff p)).2 (T a).property).symm
  rw [hfactor]
  exact hcompact.clm_comp (deleteCoordinateTo n)

/-- Direct off-diagonal form of the deleted-coordinate compactness
criterion used in Lemma 12.6. The diagonal remainder must vanish. -/
theorem isCompactOperator_deleted_of_reciprocalEntryBound
    (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (k : ℤ → Coeff q)
    (hrow : ∀ (m : ℤ) (a : DeletedCoeff p n),
      ((T a : DeletedCoeff p n) : Coeff p) m =
        dualPairing (a : Coeff p) (k m))
    (hdiag : ∀ m : ℤ, k m m = 0)
    (hoff : ∀ m r : ℤ, r ≠ m →
      ‖k m r‖ ≤ ‖b m‖ / |((r - m : ℤ) : ℝ)|) :
    IsCompactOperator T := by
  apply isCompactOperator_deleted_of_puncturedKernelMajorant hp n T b k hrow
  intro m r
  have hq : 1 < q :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp.lt_top
  rw [norm_shift_puncturedLattice_apply hq]
  by_cases hrm : r = m
  · subst r
    simp [hdiag]
  · rw [if_neg hrm]
    simpa only [div_eq_mul_inv] using hoff m r hrm

end NLS.Coeff
