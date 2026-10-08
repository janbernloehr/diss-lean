import NLS.Fourier.SampledHilbert

/-! # The two-lattice reciprocal kernel of Appendix C.2

Both lattices may have arbitrary bounded complex displacements. Uniform
linear separation off the diagonal makes the difference from the ordinary
Hilbert kernel dominated by its summable square.
-/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- A bounded displacement of the source's pi-spaced lattice. -/
def hilbertLattice (s : Coeff ⊤) (n : ℤ) : ℂ := (Real.pi:ℂ)*n+s n

/-- The source separation hypothesis, with the diagonal deliberately excluded. -/
def HilbertLatticeSeparated (s r : Coeff ⊤) (c : ℝ) : Prop :=
  ∀ n k : ℤ, k ≠ n → c⁻¹*‖(k:ℂ)-n‖ ≤ ‖hilbertLattice r k-hilbertLattice s n‖

/-- The normalized two-lattice reciprocal kernel, omitting its diagonal. -/
def modifiedHilbertKernel (s r : Coeff ⊤) (n k : ℤ) : ℂ :=
  if k = n then 0 else (Real.pi:ℂ)/(hilbertLattice r k-hilbertLattice s n)

/-- A constant depending only on the separation and displacement norms. -/
def modifiedHilbertCorrectionBound (s r : Coeff ⊤) (c : ℝ) : ℝ := c*(‖s‖+‖r‖)

/-- The source algebra gains two reciprocal factors in the difference kernel. -/
theorem modifiedHilbertKernel_sub (s r : Coeff ⊤) {c : ℝ} (hc : 0 < c)
    (hsep : HilbertLatticeSeparated s r c) {n k : ℤ} (hkn : k ≠ n) :
    modifiedHilbertKernel s r n k-1/((k:ℂ)-n) =
      (s n-r k)/(((k:ℂ)-n)*(hilbertLattice r k-hilbertLattice s n)) := by
  have hd : (k:ℂ)-n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkn)
  have hD : hilbertLattice r k-hilbertLattice s n ≠ 0 :=
    norm_pos_iff.mp ((mul_pos (inv_pos.mpr hc) (norm_pos_iff.mpr hd)).trans_le (hsep n k hkn))
  rw [modifiedHilbertKernel, if_neg hkn]
  field_simp
  simp only [hilbertLattice]
  ring

/-- A square-kernel majorant with no smallness condition on either lattice. -/
theorem norm_modifiedHilbertKernel_sub_le (s r : Coeff ⊤) {c : ℝ} (hc : 0 < c)
    (hsep : HilbertLatticeSeparated s r c) (n k : ℤ) :
    ‖modifiedHilbertKernel s r n k-1/((k:ℂ)-n)‖ ≤
      modifiedHilbertCorrectionBound s r c*‖hilbertSquareCoeffs (n-k)‖ := by
  by_cases hkn : k = n
  · subst k
    simp [modifiedHilbertKernel, hilbertSquareCoeffs_apply]
  have hd : 0 < ‖(k:ℂ)-n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by exact_mod_cast hkn))
  have hD := (mul_pos (inv_pos.mpr hc) hd).trans_le (hsep n k hkn)
  have hi : ‖hilbertLattice r k-hilbertLattice s n‖⁻¹ ≤ c*‖(k:ℂ)-n‖⁻¹ := by
    have h := (inv_le_inv₀ hD (mul_pos (inv_pos.mpr hc) hd)).mpr (hsep n k hkn)
    simpa [mul_inv_rev, mul_comm] using h
  have hn : ‖s n-r k‖ ≤ ‖s‖+‖r‖ :=
    (norm_sub_le _ _).trans (add_le_add (lp.norm_apply_le_norm (by simp) s n)
      (lp.norm_apply_le_norm (by simp) r k))
  rw [modifiedHilbertKernel_sub s r hc hsep hkn, norm_div, norm_mul, div_eq_mul_inv, mul_inv_rev]
  have he : ‖hilbertSquareCoeffs (n-k)‖ = ‖(k:ℂ)-n‖⁻¹^2 := by
    simp only [hilbertSquareCoeffs_apply, hilbertKernel, norm_pow, norm_neg, norm_inv, Int.cast_sub]
    rw [norm_sub_rev]
  rw [he]
  calc
    _ ≤ (‖s‖+‖r‖)*(c*‖(k:ℂ)-n‖⁻¹*‖(k:ℂ)-n‖⁻¹) := by gcongr
    _ = _ := by unfold modifiedHilbertCorrectionBound; ring

/-- Translating both lattices by one common constant preserves their separation. -/
theorem hilbertLatticeSeparated_common_constant (s : Coeff ⊤) (hs : ∀ n, s n = s 0) :
    HilbertLatticeSeparated s s (Real.pi⁻¹) := by
  intro n k _
  have he : hilbertLattice s k-hilbertLattice s n = (Real.pi:ℂ)*((k:ℂ)-n) := by
    simp only [hilbertLattice, hs k, hs n]
    ring
  rw [inv_inv, he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- The factor pi exactly cancels the free lattice spacing, at every common translation. -/
theorem modifiedHilbertKernel_common_constant (s : Coeff ⊤) (hs : ∀ n, s n = s 0) (n k : ℤ) :
    modifiedHilbertKernel s s n k = 1/((k:ℂ)-n) := by
  by_cases h : k = n
  · subst k
    simp [modifiedHilbertKernel]
  have he : hilbertLattice s k-hilbertLattice s n = (Real.pi:ℂ)*((k:ℂ)-n) := by
    simp only [hilbertLattice, hs k, hs n]
    ring
  rw [modifiedHilbertKernel, if_neg h, he, div_mul_eq_div_div,
    div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]

end NLS.Fourier
