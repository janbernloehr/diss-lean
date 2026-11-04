import NLS.Fourier.AbsoluteReciprocalYoungRows
import NLS.SequenceSpaces.QuasiHolderProduct
import NLS.SequenceSpaces.QuasiExponentEmbedding

/-! # A quantitative reciprocal-row bootstrap step

A Hölder product, contractive exponent inclusion, and a reciprocal Young
row improve a gap-normalized sequence. The error row is an ℓ¹ product
uniformly in its translated index. A finite central part is retained with
an explicit norm bound; quasi-Banach product exponents are allowed.
-/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.Coeff
variable {p q r R t v : ℝ≥0∞}

/-- A finite central part plus a sequence tail majorant gives a norm bound
at the new Banach exponent, with the original coefficients retained. -/
theorem exists_coeff_of_tail_majorant [Fact (1 ≤ q)] [Fact (1 ≤ t)]
    (a : Coeff q) (b : Coeff t) (K : ℕ)
    (hb : ∀ k : ℤ, K ≤ k.natAbs → ‖a k‖ ≤ ‖b k‖) :
    ∃ a' : Coeff t, (∀ k, a' k = a k) ∧
      ‖a'‖ ≤ (Finset.Icc (-(K:ℤ)) K).card*‖a‖+‖b‖ := by
  let S := Finset.Icc (-(K:ℤ)) K
  let h : Coeff t := ∑ k ∈ S, lp.single t k (a k)
  have hh (k : ℤ) : h k = if k ∈ S then a k else 0 := by
    simp only [h,lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Pi.single_apply]
    simp
  have hhnorm : ‖h‖ ≤ S.card*‖a‖ := by
    calc
      ‖h‖ ≤ ∑ k ∈ S, ‖(lp.single t k (a k) : Coeff t)‖ := norm_sum_le _ _
      _ = ∑ k ∈ S, ‖a k‖ := Finset.sum_congr rfl (fun k _ =>
        lp.norm_single (E := fun _ : ℤ => ℂ) (zero_lt_one.trans_le (Fact.out : 1 ≤ t)) k (a k))
      _ ≤ ∑ _k ∈ S, ‖a‖ := Finset.sum_le_sum (fun k _ =>
        lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' a k)
      _ = _ := by simp
  let M := magnitude h+magnitude b
  have hM (k : ℤ) : ‖M k‖ = ‖h k‖+‖b k‖ := by
    simp only [M,lp.coeFn_add,Pi.add_apply,magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hpoint (k : ℤ) : ‖a k‖ ≤ ‖M k‖ := by
    rw [hM,hh]
    by_cases hk : k ∈ S
    · simp only [if_pos hk]
      linarith [norm_nonneg (b k)]
    · simp only [if_neg hk,norm_zero,zero_add]
      exact hb k (by simp only [S,Finset.mem_Icc] at hk; omega)
  let a' : Coeff t := ⟨fun k => a k,(lp.memℓp M).mono' hpoint⟩
  refine ⟨a',fun _ => rfl,?_⟩
  calc
    ‖a'‖ ≤ ‖M‖ := lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ t)).ne' hpoint
    _ ≤ ‖magnitude h‖+‖magnitude b‖ := norm_add_le _ _
    _ = ‖h‖+‖b‖ := by simp
    _ ≤ _ := add_le_add hhnorm le_rfl

/-- One bootstrap step, with a quasi-Hölder product optionally embedded into ℓ¹
before applying the reciprocal Young estimate. -/
theorem exists_reciprocal_bootstrap_step [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [Fact (1 ≤ R)] [Fact (1 ≤ t)] [Fact (1 ≤ v)] [p.HolderTriple q r]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hr : 0 < r)
    (hRt : R ≠ ⊤) (hrR : r ≤ R)
    (hY : YoungRelation R v t) (hv1 : 1 < v)
    (g : Coeff p) (a : Coeff q) (n : ℤ) (K : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hineq : ∀ k : ℤ, K ≤ k.natAbs → ‖a k‖ ≤ C*
      ((∑' m, ‖g m*a m‖*‖NLS.Fourier.hilbertKernel (k-m)‖)+
        ‖g k‖*‖NLS.Fourier.hilbertKernel (n-k)‖)) :
    ∃ a' : Coeff t, (∀ k, a' k = a k) ∧
      ‖a'‖ ≤ (Finset.Icc (-(K:ℤ)) K).card*‖a‖+
        C*(‖g‖*‖a‖*‖NLS.Fourier.hilbertKernelCoeffs hv1‖+
          ‖g‖*‖NLS.Fourier.hilbertKernelCoeffs
            ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ q)).ne' hq
  let u0 := quasiHolderProduct (r := r) g a
  let u : Coeff R := ⟨fun k => u0 k,(lp.memℓp u0).of_exponent_ge hrR⟩
  have hu : ‖u‖ ≤ ‖g‖*‖a‖ :=
    (norm_quasiExponentInclusion_le hr (zero_lt_one.trans_le (Fact.out : 1 ≤ R)) hRt hrR u0).trans
      (norm_quasiHolderProduct_le hp0 hq0 g a)
  let B := NLS.Fourier.absoluteReciprocalYoungMajorant hY hv1 u
  have hB : ‖B‖ ≤ ‖g‖*‖a‖*‖NLS.Fourier.hilbertKernelCoeffs hv1‖ :=
    (NLS.Fourier.norm_absoluteReciprocalYoungMajorant_le hY hv1 u).trans
      (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
  have hpc1 : 1 < p.conjExponent :=
    (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hpc : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let : Fact (1 ≤ p.conjExponent) := ⟨hpc1.le⟩
  let E := quasiHolderProduct (r := 1) g (shift n (NLS.Fourier.hilbertKernelCoeffs hpc1))
  let Et : Coeff t := exponentInclusion (Fact.out : 1 ≤ t) E
  have hE : ‖Et‖ ≤ ‖g‖*‖NLS.Fourier.hilbertKernelCoeffs hpc1‖ := by
    apply (norm_exponentInclusion_le (Fact.out : 1 ≤ t) E).trans
    have hpc0 : 0 < p.conjExponent.toReal := ENNReal.toReal_pos (zero_lt_one.trans hpc1).ne' hpc
    simpa only [norm_shift] using norm_quasiHolderProduct_le hp0 hpc0 g
      (shift n (NLS.Fourier.hilbertKernelCoeffs hpc1))
  let F := (C:ℂ) • (magnitude B+magnitude Et)
  have hF (k : ℤ) : ‖F k‖ = C*(‖B k‖+‖g k‖*‖NLS.Fourier.hilbertKernel (n-k)‖) := by
    have he : ‖Et k‖ = ‖g k‖*‖NLS.Fourier.hilbertKernel (n-k)‖ := by
      simp only [Et,exponentInclusion_apply,E,quasiHolderProduct_apply,shift_apply,norm_mul,
        NLS.Fourier.hilbertKernelCoeffs]
      congr 1
      rw [← neg_sub n k,NLS.Fourier.hilbertKernel_neg,norm_neg]
    simp only [F,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hC,lp.coeFn_add,Pi.add_apply,magnitude_apply,← Complex.ofReal_add]
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ ‖B k‖+‖Et k‖),he]
  obtain ⟨a',ha',hbound⟩ := exists_coeff_of_tail_majorant a F K (by
    intro k hk
    rw [hF,NLS.Fourier.norm_absoluteReciprocalYoungMajorant_apply]
    exact hineq k hk)
  refine ⟨a',ha',hbound.trans ?_⟩
  apply add_le_add le_rfl
  calc
    ‖F‖ = C*‖magnitude B+magnitude Et‖ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC]
    _ ≤ C*(‖B‖+‖Et‖) := mul_le_mul_of_nonneg_left (by simpa only [norm_magnitude] using norm_add_le (magnitude B) (magnitude Et)) hC
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hB hE) hC

end NLS.Coeff
