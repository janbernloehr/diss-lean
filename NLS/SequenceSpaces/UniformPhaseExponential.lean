import NLS.SequenceSpaces.RefinedOnePlusDecomposition
import NLS.ComplexAnalysis.SharpExponentialRemainder

/-! # Uniform exponential errors in refined sequence spaces

The scalar exponential estimate supplies a uniform sequence bound on
compact time intervals. Simultaneous refined bounds give one mixed
decomposition, chosen before every OnePlus projection exponent.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff

/-- Compact-time exponential errors retain a uniformly bounded sequence norm. -/
theorem exists_uniform_phase_error_sequence {r : ℝ≥0∞} [Fact (1 ≤ r)]
    (R C t : ℝ) (hR : 0 ≤ R) (ht : |t| ≤ R)
    (b : Coeff r) (hb : ‖b‖ ≤ C) :
    ∃ c : Coeff r, (∀ n, c n = Complex.exp ((t : ℂ)*Complex.I*b n)-1) ∧
      ‖c‖ ≤ R*Real.exp (R*C)*C := by
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ r from Fact.out)).ne'
  let K : ℝ := R*Real.exp (R*C)
  have hK : 0 ≤ K := mul_nonneg hR (Real.exp_pos _).le
  have hpoint (n : ℤ) : ‖Complex.exp ((t : ℂ)*Complex.I*b n)-1‖ ≤ K*‖b n‖ := by
    have hn : ‖b n‖ ≤ C := (lp.norm_apply_le_norm hr0 b n).trans hb
    have htbn : |t| *‖b n‖ ≤ R*C := mul_le_mul ht hn (norm_nonneg _) hR
    have he := NLS.ComplexAnalysis.norm_exp_sub_one_le_norm_mul_exp ((t : ℂ)*Complex.I*b n)
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one] at he
    calc
      _ ≤ |t| *‖b n‖*Real.exp (|t| *‖b n‖) := he
      _ ≤ R*‖b n‖*Real.exp (R*C) :=
        mul_le_mul (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
          (Real.exp_le_exp.mpr htbn) (Real.exp_pos _).le (mul_nonneg hR (norm_nonneg _))
      _ = _ := by dsimp [K]; ring
  let c : Coeff r := ⟨fun n => Complex.exp ((t : ℂ)*Complex.I*b n)-1,
    (b.property.norm.const_mul K).mono hpoint⟩
  refine ⟨c,fun _ => rfl,?_⟩
  have hnorm : ‖c‖ ≤ ‖(K : ℂ) • b‖ := by
    apply lp.norm_mono hr0
    intro n
    simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hK] using hpoint n
  calc
    _ ≤ ‖(K : ℂ) • b‖ := hnorm
    _ = K*‖b‖ := by simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK]
    _ ≤ K*C := mul_le_mul_of_nonneg_left hb hK

/-- A single mixed decomposition is uniform on a compact time interval and
on the supplied source set, before every OnePlus projection exponent. -/
theorem exists_uniform_phase_error_onePlus_decomposition {E : Type*}
    (S : Set E) (f : E → ℤ → ℂ) {a : ℝ≥0∞} (ha : a ≠ ⊤)
    (hb : ∀ r : ℝ≥0∞, r ≠ ⊤ → 1 < r → a ≤ r →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ ∈ S, ∃ b : Coeff r,
        (∀ n, b n = f ψ n) ∧ ‖b‖ ≤ C)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ g : ℝ × E → Coeff a, ∃ h : ℝ × E → CoeffOnePlus,
      (∀ x ∈ Icc (-R) R ×ˢ S, ∀ n,
        Complex.exp ((x.1 : ℂ)*Complex.I*f x.2 n)-1 = g x n+(h x).1 n) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-R) R ×ˢ S, ‖g x‖ ≤ C) ∧
      ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-R) R ×ˢ S,
          ‖CoeffOnePlus.toCoeff q hq1 hq (h x)‖ ≤ C := by
  apply exists_onePlus_decomposition_of_refined (Icc (-R) R ×ˢ S)
    (fun x n => Complex.exp ((x.1 : ℂ)*Complex.I*f x.2 n)-1) ha
  intro r hr hr1 har
  let : Fact (1 ≤ r) := ⟨hr1.le⟩
  obtain ⟨C,hC,hb⟩ := hb r hr hr1 har
  refine ⟨R*Real.exp (R*C)*C,mul_nonneg (mul_nonneg hR (Real.exp_pos _).le) hC,?_⟩
  intro x hx
  obtain ⟨b,he,hbn⟩ := hb x.2 hx.2
  obtain ⟨c,hce,hcn⟩ := exists_uniform_phase_error_sequence R C x.1 hR (abs_le.mpr hx.1) b hbn
  exact ⟨c,fun n => (hce n).trans (by rw [he n]),hcn⟩

end NLS.Coeff


open Set
open scoped ENNReal
namespace NLS.Coeff

/-- A real free frequency has unit modulus; only the bounded complex
correction controls the growth on a compact time interval. -/
theorem norm_complex_phase_mul_le (freq t R C : ℝ) (b a : ℂ)
    (hR : 0 ≤ R) (ht : |t| ≤ R) (hb : ‖b‖ ≤ C) :
    ‖Complex.exp ((t : ℂ)*Complex.I*((freq : ℂ)+b))*a‖ ≤ Real.exp (R*C)*‖a‖ := by
  have he : (t : ℂ)*Complex.I*((freq : ℂ)+b) =
      ((t*freq : ℝ) : ℂ)*Complex.I+(t : ℂ)*Complex.I*b := by push_cast; ring
  rw [he,Complex.exp_add,norm_mul,norm_mul,Complex.norm_exp_ofReal_mul_I,one_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
  calc
    _ ≤ Real.exp ‖(t : ℂ)*Complex.I*b‖ := Complex.norm_exp_le_exp_norm _
    _ ≤ Real.exp (R*C) := by
      apply Real.exp_le_exp.mpr
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
      exact mul_le_mul ht hb (norm_nonneg b) hR

/-- A common coordinate bound controls the sequence-pair norm. -/
theorem norm_pair_le_of_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a z : Coeff p × Coeff p) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ n, ‖a.1 n‖ ≤ K*‖z.1 n‖ ∧ ‖a.2 n‖ ≤ K*‖z.2 n‖) :
    ‖a‖ ≤ K*‖z‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)).ne'
  have hc (a z : Coeff p) (h : ∀ n, ‖a n‖ ≤ K*‖z n‖) : ‖a‖ ≤ K*‖z‖ := by
    have hn : ‖a‖ ≤ ‖(K : ℂ) • z‖ := by
      apply lp.norm_mono hp0
      intro n
      simpa only [lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg hK] using h n
    simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hK] using hn
  rw [Prod.norm_def,Prod.norm_def]
  exact max_le (le_trans (hc _ _ (fun n => (h n).1))
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hK))
    (le_trans (hc _ _ (fun n => (h n).2)) (mul_le_mul_of_nonneg_left (le_max_right _ _) hK))

end NLS.Coeff

