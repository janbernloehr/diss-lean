import NLS.SequenceSpaces.CompactPuncturedKernel
import NLS.SequenceSpaces.ShiftedHilbertInverse
import NLS.SequenceSpaces.WeightedMultiplier

/-! # Inverse-bracket decay from weighted Hilbert sequences

A punctured reciprocal sum with a one-derivative Hilbert majorant has
inverse-bracket decay at every signed index, including zero. Such decay
also gives membership in every sequence exponent above one and a bounded
multiplier gaining one Sobolev derivative.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff

private theorem norm_shiftedInverse_one_le_two : ‖shiftedInverse 1 le_rfl‖ ≤ 2 := by
  have h := norm_shiftedInverse_sq_le 1 le_rfl
  norm_num at h
  nlinarith [norm_nonneg (shiftedInverse 1 le_rfl)]

/-- A bracket in the selected index can be distributed over the two reciprocal centers. -/
theorem weighted_punctured_row_le (n m : ℤ) :
    (1+|(n:ℝ)|)*‖shift n (puncturedLattice 2 (by norm_num)) m‖ ≤
      (1+|(m:ℝ)|)*(‖shift n (puncturedLattice 2 (by norm_num)) m‖+
        ‖shiftedInverse 1 le_rfl m‖) := by
  rw [norm_shift_puncturedLattice_apply]
  by_cases hm : m=n
  · simp only [if_pos hm,mul_zero,zero_add]
    positivity
  rw [if_neg hm,shiftedInverse_apply,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1+|(m:ℝ)|)]
  have hd : 0 < |((m-n:ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hm)
  have ht : |(n:ℝ)| ≤ |(m:ℝ)|+|((m-n:ℤ):ℝ)| := by
    have h := abs_add_le (m:ℝ) ((n:ℝ)-m)
    rw [show (m:ℝ)+(n-m)=n by ring] at h
    simpa only [Int.cast_sub,abs_sub_comm] using h
  rw [mul_add,mul_inv_cancel₀ (by positivity : 1+|(m:ℝ)| ≠ 0)]
  have hmul := mul_le_mul_of_nonneg_right (show 1+|(n:ℝ)| ≤ 1+|(m:ℝ)|+|((m-n:ℤ):ℝ)| by linarith)
    (inv_nonneg.mpr hd.le)
  simpa only [add_mul,mul_inv_cancel₀ hd.ne'] using hmul

/-- A one-derivative Hilbert majorant gives inverse-bracket decay of an entire reciprocal sum. -/
theorem summable_norm_reciprocal_of_weighted_hilbert (a : Coeff 2) (u : ℤ → ℂ)
    (n : ℤ) (C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ m, ‖u m‖ ≤ C*‖a m‖/(1+|(m:ℝ)|)*
      ‖shift n (puncturedLattice 2 (by norm_num)) m‖) :
    Summable (fun m => ‖u m‖) ∧
      (1+|(n:ℝ)|)*(∑' m, ‖u m‖) ≤ 4*C*‖a‖ := by
  let b := shift n (puncturedLattice 2 (by norm_num))
  let d := shiftedInverse 1 le_rfl
  have hb := lp.tsum_mul_le_mul_norm (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from
    Real.HolderConjugate.two_two) a b
  have hd := lp.tsum_mul_le_mul_norm (show (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal from
    Real.HolderConjugate.two_two) a d
  let M := fun m => C*(‖a m‖*‖b m‖+‖a m‖*‖d m‖)
  have hMs : Summable M := (hb.1.add hd.1).mul_left C
  have hdom (m : ℤ) : (1+|(n:ℝ)|)*‖u m‖ ≤ M m := by
    have h := weighted_punctured_row_le n m
    have h' := mul_le_mul_of_nonneg_left h (show 0 ≤ C*‖a m‖/(1+|(m:ℝ)|) by positivity)
    have he : C*‖a m‖/(1+|(m:ℝ)|)*
        ((1+|(m:ℝ)|)*(‖b m‖+‖d m‖)) = M m := by
      dsimp [M]
      field_simp
    calc
      _ ≤ (1+|(n:ℝ)|)*(C*‖a m‖/(1+|(m:ℝ)|)*‖b m‖) :=
        mul_le_mul_of_nonneg_left (hu m) (by positivity)
      _ = C*‖a m‖/(1+|(m:ℝ)|)*((1+|(n:ℝ)|)*‖b m‖) := by ring
      _ ≤ C*‖a m‖/(1+|(m:ℝ)|)*((1+|(m:ℝ)|)*(‖b m‖+‖d m‖)) := h'
      _ = M m := he
  have hs := hMs.of_nonneg_of_le (fun m => by positivity) hdom
  have hus : Summable (fun m => ‖u m‖) := by
    have h := hs.mul_left (1+|(n:ℝ)|)⁻¹
    simpa only [← mul_assoc,inv_mul_cancel₀ (by positivity : 1+|(n:ℝ)| ≠ 0),one_mul] using h
  refine ⟨hus,?_⟩
  have hsum := hs.tsum_le_tsum hdom hMs
  simp only [M,tsum_mul_left,(hb.1).tsum_add hd.1] at hsum
  have hbnd : ‖b‖ ≤ 2 := by simpa only [b,norm_shift] using norm_puncturedLattice_two_le
  have hdnd : ‖d‖ ≤ 2 := norm_shiftedInverse_one_le_two
  exact hsum.trans (by nlinarith [hb.2,hd.2,mul_nonneg hC (norm_nonneg a),
    mul_le_mul_of_nonneg_left hbnd (norm_nonneg a),mul_le_mul_of_nonneg_left hdnd (norm_nonneg a)])

end NLS.Coeff

namespace NLS
open scoped ENNReal

/-- Inverse-bracket decay implies membership in every sequence exponent strictly above one. -/
theorem memlp_of_inverse_bracket_bound {q : ℝ≥0∞} (hq : 1 < q)
    (f : ℤ → ℂ) (K : ℝ)
    (hf : ∀ n : ℤ, (1+|(n:ℝ)|)*‖f n‖ ≤ K) : Memℓp f q := by
  apply ((Weight.inverse_sobolev_one_memlp hq).norm.const_mul K).mono
  intro n
  simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,
    Weight.sobolev_apply,Real.rpow_one,abs_of_pos (by positivity : 0 < 1+|(n:ℝ)|)]
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hf n)

end NLS


namespace NLS.WeightedCoeff
open scoped ENNReal

/-- Inverse-bracket decay gives a bounded multiplier gaining one derivative at any real order. -/
theorem exists_sobolev_gain_multiplier {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (r : ℝ) (f : ℤ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ n : ℤ, (1 + |(n : ℝ)|) * ‖f n‖ ≤ K) :
    ∃ T : WeightedCoeff (Weight.sobolev r) p →L[ℂ] WeightedCoeff (Weight.sobolev (r + 1)) p,
      (∀ a n, (T a).val n = f n * a.val n) ∧ ‖T‖ ≤ K := by
  have hw (n : ℤ) : Weight.sobolev (r + 1) n * ‖f n‖ ≤ K * Weight.sobolev r n := by
    simp only [Weight.sobolev_apply, Real.rpow_add (by positivity : 0 < 1 + |(n : ℝ)|),
      Real.rpow_one]
    calc
      _ = (1 + |(n : ℝ)|) ^ r * ((1 + |(n : ℝ)|) * ‖f n‖) := by ring
      _ ≤ (1 + |(n : ℝ)|) ^ r * K :=
        mul_le_mul_of_nonneg_left (hf n) (Real.rpow_pos_of_pos (by positivity) r).le
      _ = _ := by ring
  let T := weightedMultiplierCLM (p := p) (Weight.sobolev r) (Weight.sobolev (r + 1)) f K hK hw
  refine ⟨T, fun _ _ => rfl, T.opNorm_le_bound hK (fun a => ?_)⟩
  exact norm_weightedMultiplier_le _ _ f K hK hw a

end NLS.WeightedCoeff
