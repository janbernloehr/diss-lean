import NLS.ZakharovShabat.PeriodicSpectrum

/-! # Imaginary spectral height from absolutely summable potentials

The two diagonal eigenvector equations give a geometric-mean bound for the
imaginary part. This keeps both potential components instead of taking their
maximum and is suitable for the dissertation's Hilbert pair norm.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Moving the absolutely summable factor to the potential preserves multiplication. -/
theorem potentialMul_eq_convolution_of_l1 (hp : p ≠ ⊤) (φ : Coeff p)
    (a : Coeff 1) (ha : ∀ n, φ n = a n) (f : ScalarDomain p) :
    potentialMul hp φ f = Coeff.convolution (scalarInclusion f) a := by
  ext n
  rw [potentialMul_apply,Coeff.convolution_apply,
    ← (Equiv.subLeft n).tsum_eq (fun k : ℤ => scalarInclusion f (n-k)*a k)]
  apply tsum_congr
  intro k
  simp only [Equiv.subLeft_apply,sub_sub_cancel,scalarInclusion_apply,ha,mul_comm]

/-- A real diagonal cannot absorb the imaginary part of the spectral parameter. -/
theorem abs_im_mul_norm_le_of_diagonal (f g : Coeff p) (c : ℤ → ℝ) (z : ℂ)
    (he : ∀ k, g k = (z-(c k:ℂ))*f k) : |z.im| *‖f‖ ≤ ‖g‖ := by
  have h : ‖((|z.im|:ℝ):ℂ) • f‖ ≤ ‖g‖ := by
    apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)))
    intro k
    rw [he k]
    change ‖((|z.im|:ℝ):ℂ)*f k‖ ≤ ‖(z-(c k:ℂ))*f k‖
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa using Complex.abs_im_le_norm (z-(c k:ℂ))
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_abs] using h

/-- The two off-diagonal bounds control imaginary spectral height by their geometric mean. -/
theorem periodicSpectrum_im_sq_le_l1 (hp : p ≠ ⊤) (φ : PairSpace p)
    (a b : Coeff 1) (ha : ∀ k, φ.1 k = a k) (hb : ∀ k, φ.2 k = b k)
    (z : ℂ) (hz : z ∈ periodicSpectrum hp φ) : |z.im|^2 ≤ ‖a‖*‖b‖ := by
  obtain ⟨f,hf,he⟩ := (mem_periodicSpectrum_iff_exists_eigenvector hp φ z).mp hz
  have hfst : |z.im| *‖scalarInclusion f.1‖ ≤ ‖a‖*‖scalarInclusion f.2‖ := by
    have h := abs_im_mul_norm_le_of_diagonal (scalarInclusion f.1) (potentialMul hp φ.1 f.2)
      (fun k => -Real.pi*k) z (fun k => by
        have hk := congrArg (fun v : PairSpace p => v.1 k) he
        simp only [operator_fst_apply,Prod.smul_fst,lp.coeFn_smul,Pi.smul_apply,
          smul_eq_mul,domainInclusion_apply,scalarInclusion_apply] at hk
        rw [potentialMul_apply,scalarInclusion_apply]
        push_cast
        linear_combination hk)
    rw [potentialMul_eq_convolution_of_l1 hp φ.1 a ha f.2] at h
    exact h.trans (by simpa only [mul_comm] using Coeff.norm_convolution_le (scalarInclusion f.2) a)
  have hsnd : |z.im| *‖scalarInclusion f.2‖ ≤ ‖b‖*‖scalarInclusion f.1‖ := by
    have h := abs_im_mul_norm_le_of_diagonal (scalarInclusion f.2) (potentialMul hp φ.2 f.1)
      (fun k => Real.pi*k) z (fun k => by
        have hk := congrArg (fun v : PairSpace p => v.2 k) he
        simp only [operator_snd_apply,Prod.smul_snd,lp.coeFn_smul,Pi.smul_apply,
          smul_eq_mul,domainInclusion_apply,scalarInclusion_apply] at hk
        rw [potentialMul_apply,scalarInclusion_apply]
        push_cast
        linear_combination hk)
    rw [potentialMul_eq_convolution_of_l1 hp φ.2 b hb f.1] at h
    exact h.trans (by simpa only [mul_comm] using Coeff.norm_convolution_le (scalarInclusion f.1) b)
  by_cases hi : z.im = 0
  · simp only [hi,abs_zero,zero_pow (by decide : 2 ≠ 0)]
    positivity
  have hi' : 0 < |z.im| := abs_pos.mpr hi
  have hnorm : ‖scalarInclusion f.1‖*‖scalarInclusion f.2‖ > 0 := by
    have hzero (h₁ : scalarInclusion f.1 = 0) (h₂ : scalarInclusion f.2 = 0) : False := by
      apply hf
      exact Prod.ext (scalarInclusion_injective (h₁.trans (map_zero _).symm))
        (scalarInclusion_injective (h₂.trans (map_zero _).symm))
    have h₁ : 0 < ‖scalarInclusion f.1‖ := by
      by_contra h
      have hh : ‖scalarInclusion f.1‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      have hh₂ : ‖scalarInclusion f.2‖ = 0 := by
        apply le_antisymm _ (norm_nonneg _)
        by_contra hpos
        exact (mul_pos hi' (lt_of_not_ge hpos)).not_ge (by simpa only [hh,mul_zero] using hsnd)
      exact hzero (norm_eq_zero.mp hh) (norm_eq_zero.mp hh₂)
    have h₂ : 0 < ‖scalarInclusion f.2‖ := by
      by_contra h
      have hh : ‖scalarInclusion f.2‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
      exact (mul_pos hi' h₁).not_ge (by simpa only [hh,mul_zero] using hfst)
    exact mul_pos h₁ h₂
  have hmul := mul_le_mul hfst hsnd (by positivity) (by positivity)
  have hmul' : |z.im|^2*(‖scalarInclusion f.1‖*‖scalarInclusion f.2‖) ≤
      (‖a‖*‖b‖)*(‖scalarInclusion f.1‖*‖scalarInclusion f.2‖) := by nlinarith [hmul]
  exact (mul_le_mul_iff_left₀ hnorm).mp hmul'

end NLS.ZakharovShabat
