import NLS.SequenceSpaces.SignedSobolevWeight
import NLS.SequenceSpaces.WeightedDomination

/-! A zero-mode-free sequence gains one full signed Sobolev order when
its physical spatial generator belongs to the lower-order space. The
literal max(1,abs(k)) bracket and original2*pi frequency are retained. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact weighted coordinate norm identity for the physical generator. -/
theorem signedSobolev_generator_norm_identity (s : ℝ) (a : ℤ → ℂ) (h0 : a 0=0) (k : ℤ) :
    Weight.signedSobolev (s+1) k*‖a k‖=
      (1/(2*Real.pi))*Weight.signedSobolev s k*‖I*((2*Real.pi*k:ℝ):ℂ)*a k‖ := by
  by_cases hk : k=0
  · subst k
    simp [h0]
  · have hkabs : (1:ℝ) ≤ |(k:ℝ)| := by
      exact_mod_cast (show (1:ℤ) ≤ |k| by have h := abs_pos.mpr hk; omega)
    have hnorm : ‖I*((2*Real.pi*k:ℝ):ℂ)*a k‖=(2*Real.pi)*|(k:ℝ)| *‖a k‖ := by
      rw [norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_pos Real.pi_pos]
    rw [hnorm]
    change (max (1:ℝ) |(k:ℝ)|)^(s+1)*‖a k‖=
      (1/(2*Real.pi))*(max (1:ℝ) |(k:ℝ)|)^s*((2*Real.pi)*|(k:ℝ)| *‖a k‖)
    rw [max_eq_right hkabs,Real.rpow_add (by linarith : 0 < |(k:ℝ)|),Real.rpow_one]
    field_simp

/-- The SAME entire raw sequence gains one signed order, including the
infinity exponent; no bounded-frequency or finite-support hypothesis. -/
theorem exists_signedSobolev_succ_of_spatialGenerator (s : ℝ) (a : ℤ → ℂ) (h0 : a 0=0)
    (v : WeightedCoeff (Weight.signedSobolev s) p)
    (hv : ∀ k : ℤ, v.val k=I*((2*Real.pi*k:ℝ):ℂ)*a k) :
    ∃ b : WeightedCoeff (Weight.signedSobolev (s+1)) p,
      (∀ k, b.val k=a k) ∧ ‖b‖ ≤ (1/(2*Real.pi))*‖v‖ := by
  let f : ℤ → ℂ := fun k =>
    ((Weight.signedSobolev (s+1) k:ℂ)/(Weight.signedSobolev s k:ℂ))*a k
  obtain ⟨c,hc,hn⟩ := exists_of_norm_le (Weight.signedSobolev s) v f (1/(2*Real.pi)) (by positivity) (by
    intro k
    have hi := signedSobolev_generator_norm_identity s a h0 k
    rw [← hv] at hi
    change ‖((Weight.signedSobolev (s+1) k:ℂ)/(Weight.signedSobolev s k:ℂ))*a k‖ ≤ _
    rw [norm_mul,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos ((Weight.signedSobolev (s+1)).positive k),abs_of_pos ((Weight.signedSobolev s).positive k)]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ((Weight.signedSobolev s).positive k)).mpr
    convert hi.le using 1; ring)
  have hmem : Memℓp (fun k => (Weight.signedSobolev (s+1) k:ℂ)*a k) p := by
    have hcm : Memℓp (fun k => (Weight.signedSobolev s k:ℂ)*c.val k) p := c.property
    convert hcm using 1
    funext k
    rw [hc]
    dsimp only [f]
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ((Weight.signedSobolev s).positive k))]
  let b : WeightedCoeff (Weight.signedSobolev (s+1)) p := ⟨a,hmem⟩
  refine ⟨b,fun _ => rfl,?_⟩
  have he : weightEquiv (Weight.signedSobolev (s+1)) p b=weightEquiv (Weight.signedSobolev s) p c := by
    ext k
    change (Weight.signedSobolev (s+1) k:ℂ)*a k=(Weight.signedSobolev s k:ℂ)*c.val k
    rw [hc]
    dsimp only [f]
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ((Weight.signedSobolev s).positive k))]
  have hnorm : ‖b‖=‖c‖ := by
    change ‖weightEquiv (Weight.signedSobolev (s+1)) p b‖=‖weightEquiv (Weight.signedSobolev s) p c‖
    rw [he]
  exact hnorm.trans_le hn

end NLS.WeightedCoeff
