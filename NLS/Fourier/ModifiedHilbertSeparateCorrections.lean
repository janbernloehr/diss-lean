import NLS.Fourier.ModifiedHilbert
import NLS.SequenceSpaces.Multiplier

/-! # The two separate correction operators in the proof of Lemma C.2 -/
noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- The two-denominator kernel has zero diagonal even when the lattices differ there. -/
def modifiedHilbertSecondKernel (s r : Coeff ⊤) (n k : ℤ) : ℂ :=
  1 / (((k : ℂ)-n)*(hilbertLattice r k-hilbertLattice s n))

theorem norm_modifiedHilbertSecondKernel_le (s r : Coeff ⊤) {c : ℝ} (hc : 0 < c)
    (hsep : HilbertLatticeSeparated s r c) (n k : ℤ) :
    ‖modifiedHilbertSecondKernel s r n k‖ ≤ c*‖hilbertSquareCoeffs (n-k)‖ := by
  by_cases hkn : k = n
  · subst k
    simp [modifiedHilbertSecondKernel]
  have hd : 0 < ‖(k:ℂ)-n‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by exact_mod_cast hkn))
  have hD := (mul_pos (inv_pos.mpr hc) hd).trans_le (hsep n k hkn)
  have hi : ‖hilbertLattice r k-hilbertLattice s n‖⁻¹ ≤ c*‖(k:ℂ)-n‖⁻¹ := by
    have h := (inv_le_inv₀ hD (mul_pos (inv_pos.mpr hc) hd)).mpr (hsep n k hkn)
    simpa [mul_inv_rev, mul_comm] using h
  have he : ‖hilbertSquareCoeffs (n-k)‖ = ‖(k:ℂ)-n‖⁻¹^2 := by
    simp only [hilbertSquareCoeffs_apply, hilbertKernel, norm_pow, norm_neg, norm_inv, Int.cast_sub]
    rw [norm_sub_rev]
  rw [modifiedHilbertSecondKernel, norm_div, norm_one, norm_mul, one_div, mul_inv_rev, he]
  calc
    _ ≤ (c*‖(k:ℂ)-n‖⁻¹)*‖(k:ℂ)-n‖⁻¹ :=
      mul_le_mul_of_nonneg_right hi (inv_nonneg.mpr hd.le)
    _ = _ := by ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable (s r : Coeff ⊤) {c : ℝ} (hc : 0 < c) (hsep : HilbertLatticeSeparated s r c)
include hc hsep

/-- Each row of the second kernel is absolutely summable against every Banach input. -/
theorem summable_norm_modifiedHilbertSecond (a : Coeff p) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k*modifiedHilbertSecondKernel s r n k‖) := by
  apply ((summable_hilbertSquareMajorant_row a n).mul_left c).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  rw [norm_mul]
  calc
    _ ≤ ‖a k‖*(c*‖hilbertSquareCoeffs (n-k)‖) :=
      mul_le_mul_of_nonneg_left (norm_modifiedHilbertSecondKernel_le s r hc hsep n k) (norm_nonneg _)
    _ = _ := by ring

theorem norm_tsum_modifiedHilbertSecond_le (a : Coeff p) (n : ℤ) :
    ‖∑' k : ℤ, a k*modifiedHilbertSecondKernel s r n k‖ ≤ c*‖hilbertSquareMajorant a n‖ := by
  rw [norm_hilbertSquareMajorant_apply, ← tsum_mul_left]
  apply (norm_tsum_le_tsum_norm (summable_norm_modifiedHilbertSecond s r hc hsep a n)).trans
  apply (summable_norm_modifiedHilbertSecond s r hc hsep a n).tsum_le_tsum
  · intro k
    rw [norm_mul]
    calc
      _ ≤ ‖a k‖*(c*‖hilbertSquareCoeffs (n-k)‖) :=
        mul_le_mul_of_nonneg_left (norm_modifiedHilbertSecondKernel_le s r hc hsep n k) (norm_nonneg _)
      _ = _ := by ring
  · exact (summable_hilbertSquareMajorant_row a n).mul_left c

/-- The common two-denominator operator before inserting either displacement. -/
def modifiedHilbertSecond (a : Coeff p) : Coeff p :=
  ⟨fun n => ∑' k : ℤ, a k*modifiedHilbertSecondKernel s r n k, by
    apply (lp.memℓp ((c:ℂ) • hilbertSquareMajorant a)).mono'
    intro n
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_of_nonneg hc.le] using
      norm_tsum_modifiedHilbertSecond_le s r hc hsep a n⟩

theorem norm_modifiedHilbertSecond_le (a : Coeff p) :
    ‖modifiedHilbertSecond s r hc hsep a‖ ≤ (c*‖hilbertSquareCoeffs‖)*‖a‖ := by
  have h : ‖modifiedHilbertSecond s r hc hsep a‖ ≤ ‖(c:ℂ) • hilbertSquareMajorant a‖ := by
    apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    intro n
    simpa only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_of_nonneg hc.le,
      modifiedHilbertSecond] using norm_tsum_modifiedHilbertSecond_le s r hc hsep a n
  rw [norm_smul, Complex.norm_of_nonneg hc.le] at h
  exact (h.trans (mul_le_mul_of_nonneg_left (norm_hilbertSquareMajorant_le a) hc.le)).trans_eq (by ring)

def modifiedHilbertSecondLinear : Coeff p →ₗ[ℂ] Coeff p where
  toFun := modifiedHilbertSecond s r hc hsep
  map_add' a b := by
    ext n
    change (∑' k : ℤ, (a+b) k*modifiedHilbertSecondKernel s r n k) = _
    simp only [lp.coeFn_add, Pi.add_apply, add_mul]
    exact (summable_norm_modifiedHilbertSecond s r hc hsep a n).of_norm.tsum_add
      (summable_norm_modifiedHilbertSecond s r hc hsep b n).of_norm
  map_smul' z a := by
    ext n
    change (∑' k : ℤ, (z • a) k*modifiedHilbertSecondKernel s r n k) = _
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left]
    rfl

def modifiedHilbertSecondCLM : Coeff p →L[ℂ] Coeff p :=
  (modifiedHilbertSecondLinear s r hc hsep).mkContinuous
    (c*‖hilbertSquareCoeffs‖) (norm_modifiedHilbertSecond_le s r hc hsep)

/-- F uses the output-index displacement sigma-tilde. -/
def modifiedHilbertF : Coeff p →L[ℂ] Coeff p :=
  (Coeff.multiplierCLM s).comp (modifiedHilbertSecondCLM s r hc hsep)

/-- G uses the input-index displacement rho-tilde. -/
def modifiedHilbertG : Coeff p →L[ℂ] Coeff p :=
  (modifiedHilbertSecondCLM s r hc hsep).comp (Coeff.multiplierCLM r)

theorem norm_modifiedHilbertF_le (a : Coeff p) :
    ‖modifiedHilbertF s r hc hsep a‖ ≤ (c*‖s‖*‖hilbertSquareCoeffs‖)*‖a‖ := by
  change ‖Coeff.multiplier s (modifiedHilbertSecond s r hc hsep a)‖ ≤ _
  apply (Coeff.norm_multiplier_le s _).trans
  exact (mul_le_mul_of_nonneg_left (norm_modifiedHilbertSecond_le s r hc hsep a)
    (norm_nonneg s)).trans_eq (by ring)

theorem norm_modifiedHilbertG_le (a : Coeff p) :
    ‖modifiedHilbertG s r hc hsep a‖ ≤ (c*‖r‖*‖hilbertSquareCoeffs‖)*‖a‖ := by
  change ‖modifiedHilbertSecond s r hc hsep (Coeff.multiplier r a)‖ ≤ _
  apply (norm_modifiedHilbertSecond_le s r hc hsep _).trans
  exact (mul_le_mul_of_nonneg_left (Coeff.norm_multiplier_le r a)
    (mul_nonneg hc.le (norm_nonneg _))).trans_eq (by ring)

/-- The source's pointwise majorant retains the separation factor c. -/
theorem norm_modifiedHilbertF_apply_le (a : Coeff p) (n : ℤ) :
    ‖modifiedHilbertF s r hc hsep a n‖ ≤
      (c*‖s‖)*‖hilbertSquareMajorant a n‖ := by
  change ‖s n*(∑' k : ℤ, a k*modifiedHilbertSecondKernel s r n k)‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul (lp.norm_apply_le_norm (by simp) s n)
    (norm_tsum_modifiedHilbertSecond_le s r hc hsep a n) (norm_nonneg _) (norm_nonneg s)).trans_eq
      (by ring)

/-- The first powered sum in the source proof, with its explicit c^p factor. -/
theorem tsum_norm_modifiedHilbertF_rpow_le_majorant (hp : p ≠ ⊤) (a : Coeff p) :
    (∑' n : ℤ, ‖modifiedHilbertF s r hc hsep a n‖^p.toReal) ≤
      c^p.toReal*‖s‖^p.toReal*(∑' n : ℤ, ‖hilbertSquareMajorant a n‖^p.toReal) := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [← tsum_mul_left]
  apply ((modifiedHilbertF s r hc hsep a).property.summable hp0).tsum_le_tsum
  · intro n
    simpa only [Real.mul_rpow hc.le (norm_nonneg s),
      Real.mul_rpow (mul_nonneg hc.le (norm_nonneg s)) (norm_nonneg _)] using
      Real.rpow_le_rpow (norm_nonneg _) (norm_modifiedHilbertF_apply_le s r hc hsep a n) hp0.le
  · exact ((hilbertSquareMajorant a).property.summable hp0).mul_left _

/-- Young's inequality gives the final F estimate, retaining c^p explicitly. -/
theorem tsum_norm_modifiedHilbertF_rpow_le (hp : p ≠ ⊤) (a : Coeff p) :
    (∑' n : ℤ, ‖modifiedHilbertF s r hc hsep a n‖^p.toReal) ≤
      c^p.toReal*‖s‖^p.toReal*‖hilbertSquareCoeffs‖^p.toReal*‖a‖^p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [← lp.norm_rpow_eq_tsum hp0]
  have h := Real.rpow_le_rpow (norm_nonneg _) (norm_modifiedHilbertF_le s r hc hsep a) hp0.le
  simpa only [Real.mul_rpow hc.le (norm_nonneg s),
    Real.mul_rpow (mul_nonneg hc.le (norm_nonneg s)) (norm_nonneg _),
    Real.mul_rpow (mul_nonneg (mul_nonneg hc.le (norm_nonneg s)) (norm_nonneg _)) (norm_nonneg _)] using h

/-- The analogous powered G estimate uses the input displacement norm. -/
theorem tsum_norm_modifiedHilbertG_rpow_le (hp : p ≠ ⊤) (a : Coeff p) :
    (∑' n : ℤ, ‖modifiedHilbertG s r hc hsep a n‖^p.toReal) ≤
      c^p.toReal*‖r‖^p.toReal*‖hilbertSquareCoeffs‖^p.toReal*‖a‖^p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) hp
  rw [← lp.norm_rpow_eq_tsum hp0]
  have h := Real.rpow_le_rpow (norm_nonneg _) (norm_modifiedHilbertG_le s r hc hsep a) hp0.le
  simpa only [Real.mul_rpow hc.le (norm_nonneg r),
    Real.mul_rpow (mul_nonneg hc.le (norm_nonneg r)) (norm_nonneg _),
    Real.mul_rpow (mul_nonneg (mul_nonneg hc.le (norm_nonneg r)) (norm_nonneg _)) (norm_nonneg _)] using h

/-- F has the literal source row, with its diagonal explicitly omitted. -/
theorem modifiedHilbertF_hasSum (a : Coeff p) (n : ℤ) :
    HasSum (fun k : ℤ => if k=n then 0 else
      (a k/((k:ℂ)-n))*(s n/(hilbertLattice r k-hilbertLattice s n)))
      (modifiedHilbertF s r hc hsep a n) := by
  have h := ((summable_norm_modifiedHilbertSecond s r hc hsep a n).of_norm.hasSum).mul_left (s n)
  apply h.congr_fun
  intro k
  by_cases hk : k=n
  · simp [hk, modifiedHilbertSecondKernel]
  · simp only [if_neg hk, modifiedHilbertSecondKernel, div_eq_mul_inv, mul_inv_rev]
    ring

/-- G has the literal source row, with its diagonal explicitly omitted. -/
theorem modifiedHilbertG_hasSum (a : Coeff p) (n : ℤ) :
    HasSum (fun k : ℤ => if k=n then 0 else
      (a k/((k:ℂ)-n))*(r k/(hilbertLattice r k-hilbertLattice s n)))
      (modifiedHilbertG s r hc hsep a n) := by
  have h := (summable_norm_modifiedHilbertSecond s r hc hsep (Coeff.multiplier r a) n).of_norm.hasSum
  apply h.congr_fun
  intro k
  by_cases hk : k=n
  · simp [hk, modifiedHilbertSecondKernel]
  · simp only [if_neg hk, modifiedHilbertSecondKernel, Coeff.multiplier_apply, div_eq_mul_inv, mul_inv_rev]
    ring

/-- The separate source operators give exactly the existing bounded correction. -/
theorem modifiedHilbertCorrection_eq_F_sub_G :
    modifiedHilbertCorrectionCLM (p := p) s r hc hsep =
      modifiedHilbertF s r hc hsep-modifiedHilbertG s r hc hsep := by
  ext a n
  change (∑' k : ℤ, a k*(modifiedHilbertKernel s r n k-1/((k:ℂ)-n))) =
    s n*(∑' k : ℤ, a k*modifiedHilbertSecondKernel s r n k)-
      (∑' k : ℤ, (Coeff.multiplier r a) k*modifiedHilbertSecondKernel s r n k)
  rw [← tsum_mul_left, ← ((summable_norm_modifiedHilbertSecond s r hc hsep a n).of_norm.mul_left (s n)).tsum_sub
    (summable_norm_modifiedHilbertSecond s r hc hsep (Coeff.multiplier r a) n).of_norm]
  apply tsum_congr
  intro k
  by_cases hk : k=n
  · simp [hk, modifiedHilbertKernel, modifiedHilbertSecondKernel]
  · rw [modifiedHilbertKernel_sub s r hc hsep hk]
    simp only [modifiedHilbertSecondKernel, Coeff.multiplier_apply]
    ring

/-- The corrected labels in the source proof give A=H+F-G. -/
theorem modifiedHilbert_eq_H_add_F_sub_G (hp1 : 1 < p) (hp : p ≠ ⊤) :
    modifiedHilbert s r hc hsep hp1 hp =
      hilbertTransform hp1 hp+modifiedHilbertF s r hc hsep-modifiedHilbertG s r hc hsep := by
  rw [modifiedHilbert, modifiedHilbertCorrection_eq_F_sub_G]
  abel

end NLS.Fourier
