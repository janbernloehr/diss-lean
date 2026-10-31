import NLS.ZakharovShabat.AppendixDExteriorAsymptotic

/-! # The scalar denominator estimate in the proof of Lemma D.5 -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The printed factor four works on the exterior, including disc boundaries. -/
theorem appendixDExterior_denominator_le_four {z : ℂ} (hz : z ∈ appendixDExterior)
    (n : ℤ) (hn : |z.re-Real.pi*n| ≤ Real.pi/2) (m : ℤ) :
    1+|((n-m:ℤ):ℝ)|+|z.im| ≤ 4*‖z-(Real.pi:ℂ)*m‖ := by
  have hre : |z.re-Real.pi*m| ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    simpa using Complex.abs_re_le_norm (z-(Real.pi:ℂ)*m)
  have him : |z.im| ≤ ‖z-(Real.pi:ℂ)*m‖ := by
    simpa using Complex.abs_im_le_norm (z-(Real.pi:ℂ)*m)
  have he : Real.pi*((n-m:ℤ):ℝ) = (Real.pi*n-z.re)+(z.re-Real.pi*m) := by
    push_cast
    ring
  have ht : Real.pi*|((n-m:ℤ):ℝ)| ≤ Real.pi/2+‖z-(Real.pi:ℂ)*m‖ := by
    calc
      _ = |(Real.pi*n-z.re)+(z.re-Real.pi*m)| := by
        rw [← he,abs_mul,abs_of_pos Real.pi_pos]
      _ ≤ _ := (abs_add_le _ _).trans
        (add_le_add (by simpa only [abs_sub_comm] using hn) hre)
  have hgap : 3*|((n-m:ℤ):ℝ)| ≤ 2+‖z-(Real.pi:ℂ)*m‖ := by
    nlinarith [Real.pi_gt_three,Real.pi_lt_four,abs_nonneg (((n-m:ℤ):ℝ))]
  have hsep := hz m
  nlinarith [Real.pi_gt_three]

/-- The corresponding relative-factor bound, with the source constant four. -/
theorem norm_appendixDExterior_relativeFactor_le {z : ℂ} (hz : z ∈ appendixDExterior)
    (n : ℤ) (hn : |z.re-Real.pi*n| ≤ Real.pi/2) (m : ℤ) (a : ℂ) :
    ‖a/(z-(Real.pi:ℂ)*m)‖ ≤
      4*‖a‖/(1+|((n-m:ℤ):ℝ)|+|z.im|) := by
  have hd : 0 < ‖z-(Real.pi:ℂ)*m‖ := (by positivity : (0:ℝ) < Real.pi/4).trans_le (hz m)
  have hS : 0 < 1+|((n-m:ℤ):ℝ)|+|z.im| := by positivity
  rw [norm_div]
  apply (div_le_div_iff₀ hd hS).mpr
  have h := mul_le_mul_of_nonneg_left (appendixDExterior_denominator_le_four hz n hn m) (norm_nonneg a)
  nlinarith

end NLS.ZakharovShabat
