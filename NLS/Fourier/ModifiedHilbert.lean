import NLS.Fourier.ModifiedHilbertKernel

/-! # Appendix C.2: bounded Hilbert transforms on two perturbed lattices

The square-kernel correction is bounded even at the Banach endpoints.
Adding the ordinary Hilbert transform proves the printed statement for
all `1 < p < infinity`, with its normalization and omitted diagonal.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (s r : Coeff ⊤) {c : ℝ} (hc : 0 < c) (hsep : HilbertLatticeSeparated s r c)
include hc hsep

/-- The absolutely summable difference from the ordinary Hilbert row. -/
theorem summable_norm_modifiedHilbert_correction (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n))‖) := by
  apply ((summable_hilbertSquareMajorant_row a n).mul_left
    (modifiedHilbertCorrectionBound s r c)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro k
  rw [norm_mul]
  calc
    _ ≤ ‖a k‖*(modifiedHilbertCorrectionBound s r c*‖hilbertSquareCoeffs (n-k)‖) :=
      mul_le_mul_of_nonneg_left (norm_modifiedHilbertKernel_sub_le s r hc hsep n k) (norm_nonneg _)
    _ = _ := by ring

/-- The correction is pointwise bounded by a positive square-kernel convolution. -/
theorem norm_tsum_modifiedHilbert_correction_le (a : Coeff p) (n : ℤ) :
    ‖∑' k : ℤ, a k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n))‖ ≤
      modifiedHilbertCorrectionBound s r c*‖hilbertSquareMajorant a n‖ := by
  rw [norm_hilbertSquareMajorant_apply, ← tsum_mul_left]
  apply (norm_tsum_le_tsum_norm (summable_norm_modifiedHilbert_correction s r hc hsep a n)).trans
  apply (summable_norm_modifiedHilbert_correction s r hc hsep a n).tsum_le_tsum
  · intro k
    rw [norm_mul]
    calc
      _ ≤ ‖a k‖*(modifiedHilbertCorrectionBound s r c*‖hilbertSquareCoeffs (n-k)‖) :=
        mul_le_mul_of_nonneg_left (norm_modifiedHilbertKernel_sub_le s r hc hsep n k) (norm_nonneg _)
      _ = _ := by ring
  · exact (summable_hilbertSquareMajorant_row a n).mul_left _

/-- The correction sequence, available for every Banach exponent. -/
def modifiedHilbertCorrection (a : Coeff p) : Coeff p :=
  ⟨fun n => ∑' k : ℤ, a k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n)), by
    apply (lp.memℓp ((modifiedHilbertCorrectionBound s r c:ℂ) • hilbertSquareMajorant a)).mono'
    intro n
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul,
      Complex.norm_of_nonneg (show 0 ≤ modifiedHilbertCorrectionBound s r c from
        mul_nonneg hc.le (add_nonneg (norm_nonneg _) (norm_nonneg _)))] using
      norm_tsum_modifiedHilbert_correction_le s r hc hsep a n⟩

/-- Young's inequality bounds the correction uniformly in the input. -/
theorem norm_modifiedHilbertCorrection_le (a : Coeff p) :
    ‖modifiedHilbertCorrection s r hc hsep a‖ ≤
      (modifiedHilbertCorrectionBound s r c*‖hilbertSquareCoeffs‖)*‖a‖ := by
  have hB : 0 ≤ modifiedHilbertCorrectionBound s r c :=
    mul_nonneg hc.le (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have h : ‖modifiedHilbertCorrection s r hc hsep a‖ ≤
      ‖(modifiedHilbertCorrectionBound s r c:ℂ) • hilbertSquareMajorant a‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro n
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_of_nonneg hB, modifiedHilbertCorrection] using
      norm_tsum_modifiedHilbert_correction_le s r hc hsep a n
  rw [norm_smul, Complex.norm_of_nonneg hB] at h
  exact (h.trans (mul_le_mul_of_nonneg_left (norm_hilbertSquareMajorant_le a) hB)).trans_eq (by ring)

/-- The correction is complex linear. -/
def modifiedHilbertCorrectionLinear : Coeff p →ₗ[ℂ] Coeff p where
  toFun := modifiedHilbertCorrection s r hc hsep
  map_add' a b := by
    ext n
    change (∑' k : ℤ, (a+b) k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n))) = _
    simp only [lp.coeFn_add, Pi.add_apply, add_mul]
    exact (summable_norm_modifiedHilbert_correction s r hc hsep a n).of_norm.tsum_add
      (summable_norm_modifiedHilbert_correction s r hc hsep b n).of_norm
  map_smul' z a := by
    ext n
    change (∑' k : ℤ, (z • a) k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n))) = _
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
    rfl

/-- The bounded correction; no endpoint restriction is needed for this part. -/
def modifiedHilbertCorrectionCLM : Coeff p →L[ℂ] Coeff p :=
  (modifiedHilbertCorrectionLinear s r hc hsep).mkContinuous
    (modifiedHilbertCorrectionBound s r c*‖hilbertSquareCoeffs‖)
    (norm_modifiedHilbertCorrection_le s r hc hsep)

/-- The source's modified Hilbert transform on the whole sequence space. -/
def modifiedHilbert (hp1 : 1 < p) (hp : p ≠ ⊤) : Coeff p →L[ℂ] Coeff p :=
  hilbertTransform hp1 hp + modifiedHilbertCorrectionCLM s r hc hsep

/-- Its norm bound depends only on p, c, and the two displacement norms. -/
theorem norm_modifiedHilbert_apply_le (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) :
    ‖modifiedHilbert s r hc hsep hp1 hp a‖ ≤
      (hilbertTransformBound hp1 hp+c*(‖s‖+‖r‖)*‖hilbertSquareCoeffs‖)*‖a‖ := by
  apply (norm_add_le _ _).trans
  exact (add_le_add (norm_hilbertTransform_apply_le hp1 hp a)
    (norm_modifiedHilbertCorrection_le s r hc hsep a)).trans_eq (by
      unfold modifiedHilbertCorrectionBound; ring)

/-- All rows converge absolutely, also for inputs of infinite support. -/
theorem summable_norm_modifiedHilbertSeries (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k*modifiedHilbertKernel s r n k‖) := by
  apply ((summable_norm_hilbertSeries_of_finite hp1 hp a n).add
    (summable_norm_modifiedHilbert_correction s r hc hsep a n)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  have he : a k*modifiedHilbertKernel s r n k =
      a k/((k:ℂ)-n)+a k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n)) := by ring
  rw [he]
  exact norm_add_le _ _

/-- The source's series without its outer pi factor also converges absolutely. -/
theorem summable_norm_modifiedHilbert_source_series (hp1 : 1 < p) (hp : p ≠ ⊤)
    (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖if k = n then 0 else a k/(hilbertLattice r k-hilbertLattice s n)‖) := by
  have he (k : ℤ) : (if k = n then 0 else a k/(hilbertLattice r k-hilbertLattice s n)) =
      (Real.pi:ℂ)⁻¹*(a k*modifiedHilbertKernel s r n k) := by
    by_cases h : k = n
    · simp [modifiedHilbertKernel, h]
    · simp only [modifiedHilbertKernel, if_neg h]
      field_simp
  simp_rw [he, norm_mul]
  simpa only [norm_mul] using
    (summable_norm_modifiedHilbertSeries s r hc hsep hp1 hp a n).mul_left ‖(Real.pi:ℂ)⁻¹‖

/-- The continuous operator has exactly the printed normalized kernel. -/
theorem modifiedHilbert_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    modifiedHilbert s r hc hsep hp1 hp a n = ∑' k : ℤ, a k*modifiedHilbertKernel s r n k := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  change hilbertTransform hp1 hp a n +
    (∑' k : ℤ, a k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n))) = _
  rw [hilbertTransform_apply hp1 hp
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne,
    ← (summable_norm_hilbertSeries_of_finite hp1 hp a n).of_norm.tsum_add
      (summable_norm_modifiedHilbert_correction s r hc hsep a n).of_norm]
  apply tsum_congr
  intro k
  ring

/-- The source formula, retaining the factor pi and explicitly omitted diagonal. -/
theorem modifiedHilbert_source_apply (hp1 : 1 < p) (hp : p ≠ ⊤) (a : Coeff p) (n : ℤ) :
    modifiedHilbert s r hc hsep hp1 hp a n =
      (Real.pi:ℂ)*(∑' k : ℤ, if k = n then 0 else a k/(hilbertLattice r k-hilbertLattice s n)) := by
  rw [modifiedHilbert_apply, ← tsum_mul_left]
  apply tsum_congr
  intro k
  by_cases h : k = n
  · simp [modifiedHilbertKernel, h]
  · simp only [modifiedHilbertKernel, if_neg h]
    ring

/-- The operator norm has the same explicit bound as its action on inputs. -/
theorem norm_modifiedHilbert_le (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ‖modifiedHilbert s r hc hsep hp1 hp‖ ≤
      hilbertTransformBound hp1 hp+c*(‖s‖+‖r‖)*‖hilbertSquareCoeffs‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact add_nonneg (hilbertTransformBound_nonneg hp1 hp)
      (mul_nonneg (mul_nonneg hc.le (add_nonneg (norm_nonneg _) (norm_nonneg _))) (norm_nonneg _))
  · exact norm_modifiedHilbert_apply_le s r hc hsep hp1 hp

omit hsep in
/-- The bound can be chosen before the two lattices, using only their norm bounds. -/
theorem exists_modifiedHilbert_uniform_bound (hp1 : 1 < p) (hp : p ≠ ⊤)
    {S R : ℝ} (hS : 0 ≤ S) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s r : Coeff ⊤, ‖s‖ ≤ S → ‖r‖ ≤ R →
      ∀ hsep : HilbertLatticeSeparated s r c,
        ‖modifiedHilbert s r hc hsep hp1 hp‖ ≤ C := by
  refine ⟨hilbertTransformBound hp1 hp+c*(S+R)*‖hilbertSquareCoeffs‖,
    add_nonneg (hilbertTransformBound_nonneg hp1 hp)
      (mul_nonneg (mul_nonneg hc.le (add_nonneg hS hR)) (norm_nonneg _)), ?_⟩
  intro s r hs hr hsep
  apply (norm_modifiedHilbert_le s r hc hsep hp1 hp).trans
  gcongr

omit hc hsep in
/-- Common translations of any size give exactly the ordinary Hilbert transform. -/
theorem modifiedHilbert_common_constant (s : Coeff ⊤) (hs : ∀ n, s n = s 0)
    (hp1 : 1 < p) (hp : p ≠ ⊤) :
    modifiedHilbert s s (inv_pos.mpr Real.pi_pos)
      (hilbertLatticeSeparated_common_constant s hs) hp1 hp = hilbertTransform hp1 hp := by
  ext a n
  change hilbertTransform hp1 hp a n+
    (∑' k : ℤ, a k*(modifiedHilbertKernel s s n k-1/((k:ℂ)-n))) = _
  simp only [modifiedHilbertKernel_common_constant s hs, sub_self, mul_zero, tsum_zero, add_zero]

end NLS.Fourier
