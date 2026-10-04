import NLS.SequenceSpaces.ConvolutionRows

/-! # One convolution majorant for a family of Holder rows

Powered Young bounds the conjugate norms of translated weighted kernels.
Pairing with any lp sequence gives one output majorant independent of
that sequence, so the input may change with the output index while its
norm remains bounded.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p q r t : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ t)]

/-- One coefficient sequence controls every Holder pairing with the
translated weighted kernel; the majorant precedes the varying input row. -/
theorem exists_uniform_holder_convolution_majorant
    (hc : p.toReal.HolderConjugate q.toReal) (hr : r ≠ ⊤) (htr : t ≤ r) (htq : t ≤ q)
    (g : Coeff r) (K : Coeff t) :
    ∃ D : Coeff r, ‖D‖ ≤ ‖g‖*‖K‖ ∧ ∀ a : Coeff p, ∀ n : ℤ,
      Summable (fun j : ℤ => ‖a j‖*‖g j*K (n-j)‖) ∧
      (∑' j : ℤ, ‖a j‖*‖g j*K (n-j)‖) ≤ ‖a‖*‖D n‖ := by
  obtain ⟨D,hD,hDnorm⟩ := exists_convolutionRowNorm hr htr g K
  refine ⟨D,hDnorm,?_⟩
  intro a n
  let Q := exponentInclusion htq (convolutionRow g K n)
  have hQ : ‖Q‖ ≤ ‖D n‖ := by
    rw [hD n,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
    exact norm_exponentInclusion_le htq _
  have hb := lp.tsum_mul_le_mul_norm hc (reindex (Equiv.subLeft n) a) Q
  have hsum : Summable (fun j : ℤ => ‖a j‖*‖g j*K (n-j)‖) := by
    have h := hb.1.comp_injective (Equiv.subLeft n).injective
    simpa only [Function.comp_def,reindex_apply,Q,exponentInclusion_apply,
      convolutionRow_apply,Equiv.subLeft_apply,sub_sub_cancel] using h
  refine ⟨hsum,?_⟩
  calc
    _ = ∑' j : ℤ, ‖reindex (Equiv.subLeft n) a j‖*‖Q j‖ := by
      rw [← (Equiv.subLeft n).tsum_eq (fun j : ℤ => ‖a j‖*‖g j*K (n-j)‖)]
      simp only [reindex_apply,Q,exponentInclusion_apply,convolutionRow_apply,
        Equiv.subLeft_apply,sub_sub_cancel]
    _ ≤ ‖reindex (Equiv.subLeft n) a‖*‖Q‖ := hb.2
    _ ≤ ‖a‖*‖D n‖ := by
      rw [norm_reindex]
      exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _)

end NLS.Coeff
