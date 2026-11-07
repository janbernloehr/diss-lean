import NLS.SequenceSpaces.RealWeightedNatPair

noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace NLS.RealWeightedNatPair

variable {w v : ℕ → ℝ} {hw : ∀ k, 0 < w k} {hv : ∀ k, 0 < v k}

include hw hv in
theorem normalization_norm_le (C : ℝ) (h : ∀ k, v k ≤ C*w k)
    (a : ℕ → ℝ × ℝ) (k : ℕ) :
    ‖realNatPairNormalization v a k‖ ≤ C*‖realNatPairNormalization w a k‖ := by
  change ‖(v k : ℂ)*_‖ ≤ C*‖(w k : ℂ)*_‖
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (hv k).le,Real.norm_of_nonneg (hw k).le]
  exact (mul_le_mul_of_nonneg_right (h k) (norm_nonneg _)).trans_eq (by ring)

include hw hv in
theorem mem_normalization_of_le (C : ℝ) (hC : 0 ≤ C) (h : ∀ k, v k ≤ C*w k)
    (a : ℕ → ℝ × ℝ) (ha : Memℓp (realNatPairNormalization w a) 2) :
    Memℓp (realNatPairNormalization v a) 2 := by
  apply (ha.const_smul (C : ℂ)).mono'
  intro k
  simpa only [Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
    Real.norm_of_nonneg hC] using normalization_norm_le (hw := hw) (hv := hv) C h a k

def inclusion (w v : ℕ → ℝ) (hw : ∀ k, 0 < w k) (hv : ∀ k, 0 < v k) (C : ℝ) (hC : 0 ≤ C) (h : ∀ k, v k ≤ C*w k)
    (a : RealWeightedNatPair w hw) : RealWeightedNatPair v hv :=
  ⟨a.val,mem_normalization_of_le (hw := hw) (hv := hv) C hC h a.val a.property⟩

theorem inclusion_apply (C : ℝ) (hC : 0 ≤ C) (h : ∀ k, v k ≤ C*w k)
    (a : RealWeightedNatPair w hw) (k : ℕ) :
    (inclusion w v hw hv C hC h a).val k = a.val k := by
  unfold inclusion
  rfl

theorem norm_inclusion_le (C : ℝ) (hC : 0 ≤ C) (h : ∀ k, v k ≤ C*w k)
    (a : RealWeightedNatPair w hw) : ‖inclusion w v hw hv C hC h a‖ ≤ C*‖a‖ := by
  rw [← (normalizationIsometry v hv).norm_map,← (normalizationIsometry w hw).norm_map]
  have hp (k : ℕ) : ‖normalizationIsometry v hv (inclusion w v hw hv C hC h a) k‖ ≤
      ‖((C : ℂ) • normalizationIsometry w hw a) k‖ := by
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg hC]
    change ‖realNatPairNormalization v a.val k‖ ≤ C*‖realNatPairNormalization w a.val k‖
    exact normalization_norm_le (hw := hw) (hv := hv) C h a.val k
  have hh := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hp
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg hC] using hh

theorem norm_eq_of_coordinates (a b : RealWeightedNatPair w hw)
    (h : ∀ k, a.val k = b.val k) : ‖a‖ = ‖b‖ :=
  congrArg norm (Subtype.ext (funext h))

theorem norm_eq_of_pair_sq (a b : RealWeightedNatPair w hw)
    (h : ∀ k, (a.val k).1^2+(a.val k).2^2 = (b.val k).1^2+(b.val k).2^2) :
    ‖a‖ = ‖b‖ := by
  have he : ‖a‖^2 = ‖b‖^2 := by
    rw [norm_sq_eq_tsum w hw a,norm_sq_eq_tsum w hw b]
    exact tsum_congr (fun k => congrArg (fun t : ℝ => (w k)^2*t) (h k))
  nlinarith [norm_nonneg a,norm_nonneg b]

end NLS.RealWeightedNatPair
