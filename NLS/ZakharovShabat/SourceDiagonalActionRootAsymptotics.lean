import NLS.ZakharovShabat.SourceDiagonalActionRootCommonDomain

/-! # High-frequency asymptotics of the physical action roots

The regularized physical ratio is the reciprocal of twice a spectral
point between the canonical endpoints. Their bounded displacements
force the scaled ratio and its positive root to have their free limits,
without an open-gap hypothesis.
-/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourceDiagonalActionRatio_frequency_displacement_bound
    (φ : realDiagonalSourceLocus 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℤ, 0 < n →
      ∃ ζ : ℝ, 0 < ζ ∧ |ζ-Real.pi*(n : ℝ)| ≤ B ∧
        sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val = ((1/(2*ζ) : ℝ) : ℂ) := by
  let l := canonicalPeriodicLeftDisplacement (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
  let r := canonicalPeriodicRightDisplacement (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem φ.val)
  refine ⟨‖l‖+‖r‖,by positivity,?_⟩
  intro n hn
  obtain ⟨ζ,hζ,hpos,he⟩ := sourceDiagonalActionRatio_eq_inverse_frequency φ n hn
  have hl := (Complex.abs_re_le_norm (l n)).trans
    (lp.norm_apply_le_norm (by norm_num) l n)
  have hr := (Complex.abs_re_le_norm (r n)).trans
    (lp.norm_apply_le_norm (by norm_num) r n)
  have hl' : |(canonicalPeriodicLeft (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n).re-Real.pi*(n : ℝ)| ≤ ‖l‖ := by
    simpa [l,canonicalPeriodicLeftDisplacement_apply] using! hl
  have hr' : |(canonicalPeriodicRight (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n).re-Real.pi*(n : ℝ)| ≤ ‖r‖ := by
    simpa [r,canonicalPeriodicRightDisplacement_apply] using! hr
  refine ⟨ζ,hpos,abs_le.mpr ⟨?_,?_⟩,he⟩
  · linarith [(abs_le.mp hl').1,hζ.1,norm_nonneg r]
  · linarith [(abs_le.mp hr').2,hζ.2,norm_nonneg l]

theorem tendsto_sourceDiagonalScaledActionRatio_positive
    (φ : realDiagonalSourceLocus 2) :
    Tendsto (fun n : ℕ => sourceDiagonalScaledActionRatio (n+1) φ.val)
      atTop (𝓝 ((1/(2*Real.pi) : ℝ) : ℂ)) := by
  obtain ⟨B,hB,hfreq⟩ := sourceDiagonalActionRatio_frequency_displacement_bound φ
  have he (n : ℕ) := hfreq ((n : ℤ)+1) (by omega)
  choose ζ hζ hbound hratio using he
  have hk (n : ℕ) : 0 < (n : ℝ)+1 := by positivity
  have htop : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => ζ n/((n : ℝ)+1)) atTop (𝓝 Real.pi) := by
    apply tendsto_sub_nhds_zero_iff.mp
    apply squeeze_zero_norm (fun n => ?_) (htop.const_div_atTop B)
    rw [show ζ n/((n : ℝ)+1)-Real.pi =
      (ζ n-Real.pi*((n : ℝ)+1))/((n : ℝ)+1) by field_simp]
    rw [norm_div,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (hk n)]
    apply div_le_div_of_nonneg_right _ (hk n).le
    simpa only [Int.cast_add,Int.cast_natCast,Int.cast_one] using hbound n
  have hnum : Tendsto (fun n : ℕ => 1+1/((n : ℝ)+1)) atTop (𝓝 (1 : ℝ)) := by
    simpa using (htop.const_div_atTop 1).const_add 1
  have hlim := hnum.div (hd.const_mul 2) (by positivity : (2 : ℝ)*Real.pi ≠ 0)
  have hc := Complex.continuous_ofReal.tendsto (1/(2*Real.pi)) |>.comp hlim
  apply hc.congr
  intro n
  change (((1+1/((n : ℝ)+1))/(2*(ζ n/((n : ℝ)+1))) : ℝ) : ℂ) = _
  rw [sourceDiagonalScaledActionRatio,if_pos (by omega : (0 : ℤ) < n+1),hratio n]
  simp only [Int.cast_add,Int.cast_natCast,Int.cast_one,abs_of_pos (hk n),← ofReal_mul]
  congr 1
  field_simp [(hk n).ne', (hζ n).ne']
  ring

theorem sourceDiagonalActionRoot_scaled_eq_sqrt_ratio
    (φ : realDiagonalSourceLocus 2) (n : ℤ) (hn : 0 < n) :
    ((Weight.sobolev (1/2) n : ℝ) : ℂ)*sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val =
      Complex.sqrt (sourceDiagonalScaledActionRatio n φ.val) := by
  obtain ⟨hi,hpos⟩ := sourceDiagonalActionRatio_real_positive (by simp) (by norm_num) φ n hn
  have he : sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val =
      ((sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val).re : ℂ) :=
    Complex.ext rfl (by simpa only [ofReal_im] using hi)
  have hroot : sourceDiagonalActionRoot (by simp) (by norm_num) n φ.val =
      ((Real.sqrt (sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val).re : ℝ) : ℂ) := by
    change Complex.sqrt (sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val) = _
    calc
      _ = Complex.sqrt (((sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val).re : ℝ) : ℂ) :=
        congrArg Complex.sqrt he
      _ = _ := by
        rw [Complex.sqrt_of_nonneg (by exact_mod_cast hpos.le)]
        rfl
  have hscale : sourceDiagonalScaledActionRatio n φ.val =
      (((1+|(n : ℝ)|)*(sourceDiagonalActionRatio (by simp) (by norm_num) n φ.val).re : ℝ) : ℂ) := by
    rw [sourceDiagonalScaledActionRatio,if_pos hn,he,ofReal_mul]
    simp only [ofReal_re]
  rw [hroot,hscale,Complex.sqrt_of_nonneg (by exact_mod_cast
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 1+|(n : ℝ)|) hpos.le)),ofReal_re,
    Real.sqrt_mul (by positivity),Weight.sobolev_apply,← Real.sqrt_eq_rpow,ofReal_mul]

theorem tendsto_sourceDiagonalActionRoot_scaled_positive
    (φ : realDiagonalSourceLocus 2) :
    Tendsto (fun n : ℕ => ((Weight.sobolev (1/2) (n+1) : ℝ) : ℂ)*
      sourceDiagonalActionRoot (by simp) (by norm_num) (n+1) φ.val)
      atTop (𝓝 ((Real.sqrt (1/(2*Real.pi)) : ℝ) : ℂ)) := by
  have hc := (Complex.continuousAt_sqrt (Or.inl (by simpa only [ofReal_re] using
      (by positivity : (0 : ℝ) ≤ 1/(2*Real.pi))))).tendsto.comp
    (tendsto_sourceDiagonalScaledActionRatio_positive φ)
  rw [Complex.sqrt_of_nonneg (by exact_mod_cast
    (by positivity : (0 : ℝ) ≤ 1/(2*Real.pi)))] at hc
  apply hc.congr
  intro n
  exact (sourceDiagonalActionRoot_scaled_eq_sqrt_ratio φ (n+1) (by omega)).symm

end NLS.ZakharovShabat
