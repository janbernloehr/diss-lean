import NLS.SequenceSpaces.ShiftedHilbertInverse

/-! # Sobolev Hilbert bounds from one extra inverse power

A uniform inverse-power coefficient bound gives the actual weighted Hilbert sequence and its norm bound, including the central index.
-/

noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

/-- One more full inverse power than the target Sobolev weight gives a
uniform Hilbert norm bound, including the zero mode. -/
theorem exists_sobolev_coeff_of_inverse_power_bound (s : ℕ) (f : ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n : ℤ, (1+|(n:ℝ)|)^(s+1)*‖f n‖ ≤ C) :
    ∃ a : WeightedCoeff (Weight.sobolev (s:ℝ)) 2,
      (∀ n, a.val n = f n) ∧ ‖a‖ ≤ 2*C := by
  let d := Coeff.shiftedInverse 1 le_rfl
  let w := Weight.sobolev (s:ℝ)
  have hd : ‖d‖ ≤ 2 := by
    have h := Coeff.norm_shiftedInverse_sq_le 1 le_rfl
    norm_num at h
    nlinarith [norm_nonneg d]
  have hdom (n : ℤ) : ‖(w n:ℂ)*f n‖ ≤ ‖((C:ℂ) • d) n‖ := by
    change ‖(w n:ℂ)*f n‖ ≤ ‖(C:ℂ)*d n‖
    simp only [w,Weight.sobolev_apply,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg hC,d,Coeff.shiftedInverse_apply,norm_inv,
      abs_of_pos (by positivity : 0 < 1+|(n:ℝ)|),Real.rpow_natCast,
      abs_of_nonneg (by positivity : 0 ≤ (1+|(n:ℝ)|)^s)]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity : 0 < 1+|(n:ℝ)|)).mpr
    have h := hf n
    rw [pow_succ] at h
    nlinarith
  have hmem : Memℓp (fun n => (w n:ℂ)*f n) 2 :=
    (lp.memℓp ((C:ℂ) • d)).mono' hdom
  let a : WeightedCoeff w 2 := ⟨f,hmem⟩
  refine ⟨a,fun _ => rfl,?_⟩
  calc
    ‖a‖ = ‖weightEquiv w 2 a‖ := norm_eq _ _ _
    _ ≤ ‖(C:ℂ) • d‖ := lp.norm_mono (by norm_num) hdom
    _ = C*‖d‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]
    _ ≤ 2*C := by nlinarith

end NLS.WeightedCoeff
