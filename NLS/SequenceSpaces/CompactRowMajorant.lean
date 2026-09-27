import NLS.SequenceSpaces.Compact
import NLS.SequenceSpaces.DeletedCoordinate

/-!
# Compactness from an `ℓᵖ` row majorant

For a finite exponent, a bounded operator whose every output row is
bounded by one `ℓᵖ` sequence times the input norm is compact. Its
finite output truncations converge in operator norm. This is the
compactness argument used for the off-diagonal Jacobian remainder in
Lemma 12.6, where a Hölder estimate supplies the row majorant.
-/

noncomputable section
open Filter Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The output truncation error is bounded by the tail norm of the
common row-majorant sequence. -/
theorem norm_truncate_operator_sub_le_rowTail
    (T : E →L[ℂ] Coeff p) (b : Coeff p)
    (hrow : ∀ (m : ℤ) (a : E), ‖T a m‖ ≤ ‖b m‖ * ‖a‖)
    (s : Finset ℤ) (a : E) :
    ‖truncate s (T a)-T a‖ ≤ ‖truncate s b-b‖ * ‖a‖ := by
  have hpoint (m : ℤ) :
      ‖(truncate s (T a)-T a) m‖ ≤
      ‖((‖a‖ : ℂ) • (truncate s b-b)) m‖ := by
    by_cases hm : m ∈ s
    · simp [hm]
    · simp only [lp.coeFn_sub, Pi.sub_apply, truncate_apply, if_neg hm,
        zero_sub, norm_neg, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg a)]
      simpa only [mul_comm] using hrow m a
  have hnorm : ‖truncate s (T a)-T a‖ ≤
      ‖(‖a‖ : ℂ) • (truncate s b-b)‖ := by
    apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out))
    exact hpoint
  calc
    ‖truncate s (T a)-T a‖ ≤
        ‖(‖a‖ : ℂ) • (truncate s b-b)‖ := hnorm
    _ = ‖truncate s b-b‖ * ‖a‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg a)]
      ring

/-- The output cutoffs converge to the operator in operator norm. -/
theorem tendsto_truncate_operator_of_rowMajorant
    (hp : p ≠ ⊤) (T : E →L[ℂ] Coeff p) (b : Coeff p)
    (hrow : ∀ (m : ℤ) (a : E), ‖T a m‖ ≤ ‖b m‖ * ‖a‖) :
    Tendsto (fun s : Finset ℤ => (truncateCLM s).comp T)
      atTop (nhds T) := by
  have hnorm (s : Finset ℤ) :
      ‖(truncateCLM s).comp T-T‖ ≤ ‖truncate s b-b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro a
    change ‖truncate s (T a)-T a‖ ≤ ‖truncate s b-b‖ * ‖a‖
    exact norm_truncate_operator_sub_le_rowTail T b hrow s a
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp b) ε hε
  refine ⟨s,fun t ht => ?_⟩
  rw [dist_eq_norm]
  have hb := hs t ht
  rw [dist_eq_norm] at hb
  exact (hnorm t).trans_lt hb

/-- A bounded operator with a single finite-`p` majorant for all its
coordinate rows is compact. -/
theorem isCompactOperator_of_rowMajorant
    (hp : p ≠ ⊤) (T : E →L[ℂ] Coeff p) (b : Coeff p)
    (hrow : ∀ (m : ℤ) (a : E), ‖T a m‖ ≤ ‖b m‖ * ‖a‖) :
    IsCompactOperator T :=
  isCompactOperator_of_tendsto
    (tendsto_truncate_operator_of_rowMajorant hp T b hrow)
    (Eventually.of_forall fun s =>
      (isCompactOperator_truncateCLM (p := p) s).comp_clm T)

/-- The same row-majorant criterion on the omitted-coordinate space
of the psi root parameters. -/
theorem isCompactOperator_deleted_of_rowMajorant
    (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n) (b : Coeff p)
    (hrow : ∀ (m : ℤ) (a : DeletedCoeff p n),
      ‖((T a : DeletedCoeff p n) : Coeff p) m‖ ≤ ‖b m‖ * ‖a‖) :
    IsCompactOperator T := by
  let ι : DeletedCoeff p n →L[ℂ] Coeff p :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have hcompact : IsCompactOperator (ι.comp T) :=
    isCompactOperator_of_rowMajorant hp (ι.comp T) b hrow
  have hfactor : T = (deleteCoordinateTo n).comp (ι.comp T) := by
    apply ContinuousLinearMap.ext
    intro a
    apply Subtype.ext
    exact ((deleteCoordinate_eq_self_iff n
      ((T a : DeletedCoeff p n) : Coeff p)).2 (T a).property).symm
  rw [hfactor]
  exact hcompact.clm_comp (deleteCoordinateTo n)

end NLS.Coeff
