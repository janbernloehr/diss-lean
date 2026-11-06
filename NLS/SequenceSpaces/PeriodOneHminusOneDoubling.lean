import NLS.SequenceSpaces.PeriodOneHminusOneRealDensity
import NLS.SequenceSpaces.WeightedInsertion
import NLS.SequenceSpaces.WeightedMultiplier
import NLS.SequenceSpaces.PeriodDoubling
import NLS.SequenceSpaces.HilbertSampling

/-! # Exact period doubling of the original H^-1 potential

A unit-period frequency n occupies period-two frequency 2n. The negative
Sobolev weight makes this a norm contraction, preserving every raw
coefficient and inserting zero at all odd frequencies.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS

theorem periodOneHminusDouble_weight_bound (n : ℤ) :
    Weight.sobolev (-1) (Coeff.parityEmbedding 0 n) ≤ Weight.sobolev (-1) n := by
  simp only [Coeff.parityEmbedding_apply,add_zero,Weight.sobolev_apply,Real.rpow_neg_one,
    Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact inv_anti₀ (by positivity) (by nlinarith [abs_nonneg (n : ℝ)])

def periodOneHminusDouble : PeriodOneHminusOne →L[ℂ] PeriodOneHminusOne :=
  (WeightedCoeff.insertIsometry (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)).toContinuousLinearMap.comp
    (WeightedCoeff.inclusionCLM (Weight.sobolev (-1))
      ((Weight.sobolev (-1)).pullback (Coeff.parityEmbedding 0)) periodOneHminusDouble_weight_bound)

@[simp] theorem periodOneHminusDouble_even (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneHminusDouble q).val (2*n) = q.val n := by
  have he := WeightedCoeff.insertIsometry_image (p := 2) (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    ((WeightedCoeff.inclusionCLM (Weight.sobolev (-1))
      ((Weight.sobolev (-1)).pullback (Coeff.parityEmbedding 0)) periodOneHminusDouble_weight_bound) q) n
  have hi := WeightedCoeff.inclusionCLM_apply (p := 2) (Weight.sobolev (-1))
    ((Weight.sobolev (-1)).pullback (Coeff.parityEmbedding 0)) periodOneHminusDouble_weight_bound q n
  simpa only [Coeff.parityEmbedding_apply,add_zero] using! he.trans hi

@[simp] theorem periodOneHminusDouble_odd (q : PeriodOneHminusOne) (n : ℤ) :
    (periodOneHminusDouble q).val (2*n+1) = 0 := by
  have hout : 2*n+1 ∉ range (Coeff.parityEmbedding 0) := by
    rintro ⟨j,hj⟩
    change 2*j+0 = 2*n+1 at hj
    omega
  exact WeightedCoeff.insertIsometry_outside (p := 2) (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    ((WeightedCoeff.inclusionCLM (Weight.sobolev (-1))
      ((Weight.sobolev (-1)).pullback (Coeff.parityEmbedding 0)) periodOneHminusDouble_weight_bound) q) _ hout

theorem norm_periodOneHminusDouble_le (q : PeriodOneHminusOne) : ‖periodOneHminusDouble q‖ ≤ ‖q‖ := by
  have he := WeightedCoeff.norm_insertIsometry (p := 2) (Weight.sobolev (-1)) (Coeff.parityEmbedding 0)
    ((WeightedCoeff.inclusionCLM (Weight.sobolev (-1))
      ((Weight.sobolev (-1)).pullback (Coeff.parityEmbedding 0)) periodOneHminusDouble_weight_bound) q)
  change ‖periodOneHminusDouble q‖ = _ at he
  rw [he]
  exact WeightedCoeff.norm_inclusionCLM_le _ _ periodOneHminusDouble_weight_bound q

theorem norm_le_two_norm_periodOneHminusDouble (q : PeriodOneHminusOne) :
    ‖q‖ ≤ 2*‖periodOneHminusDouble q‖ := by
  have hb (n : ℤ) : Weight.sobolev (-1) n ≤ 2*Weight.sobolev (-1) (2*n) := by
    simp only [Weight.sobolev_apply,Real.rpow_neg_one,Int.cast_mul,Int.cast_ofNat,
      abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [← one_div,← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [abs_nonneg (n : ℝ)]
  let a := WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2 q
  let b := Coeff.hilbertSample (Coeff.parityEmbedding 0)
    (WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2 (periodOneHminusDouble q))
  have hp (n : ℤ) : ‖a n‖ ≤ ‖((2 : ℂ) • b) n‖ := by
    dsimp only [a,b]
    simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Coeff.hilbertSample_apply,Coeff.parityEmbedding_apply,add_zero]
    change ‖(Weight.sobolev (-1) n : ℂ)*q.val n‖ ≤
      ‖(2 : ℂ)*((Weight.sobolev (-1) (2*n) : ℂ)*(periodOneHminusDouble q).val (2*n))‖
    rw [periodOneHminusDouble_even]
    simp only [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (-1)).positive n),abs_of_pos ((Weight.sobolev (-1)).positive (2*n))]
    nlinarith [mul_le_mul_of_nonneg_right (hb n) (norm_nonneg (q.val n))]
  have h := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hp
  calc
    ‖q‖ = ‖a‖ := rfl
    _ ≤ 2*‖b‖ := by simpa only [norm_smul,Complex.norm_ofNat] using h
    _ ≤ 2*‖WeightedCoeff.weightIsometry (Weight.sobolev (-1)) 2 (periodOneHminusDouble q)‖ :=
      mul_le_mul_of_nonneg_left (Coeff.norm_hilbertSample_le _ _) (by norm_num)
    _ = 2*‖periodOneHminusDouble q‖ := by rw [LinearIsometryEquiv.norm_map]

theorem periodOneHminusDouble_injective : Function.Injective periodOneHminusDouble := by
  intro q p he
  apply Subtype.ext
  funext n
  have hh := congrArg (fun v : PeriodOneHminusOne => v.val (2*n)) he
  simpa only [periodOneHminusDouble_even] using hh

theorem periodOneHminusDouble_eq_L2 (a : Coeff 2) :
    periodOneHminusDouble (periodOneL2Inclusion a) = periodOneL2Inclusion (Coeff.periodDouble a) := by
  apply Subtype.ext
  funext k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,periodOneHminusDouble_even,periodOneL2Inclusion_apply,periodOneL2Inclusion_apply,Coeff.periodDouble_even]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,periodOneHminusDouble_odd,periodOneL2Inclusion_apply,Coeff.periodDouble_odd]

theorem periodOneHminusDouble_real (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    IsRealPeriodOneHminusOne (periodOneHminusDouble q) := by
  intro k
  by_cases hk : k % 2 = 0
  · have he : k = 2*(k/2) := by omega
    rw [he,show -(2*(k/2)) = 2*(-(k/2)) by ring,periodOneHminusDouble_even,periodOneHminusDouble_even,hr]
  · have he : k = 2*(k/2)+1 := by omega
    rw [he,show -(2*(k/2)+1) = 2*(-(k/2)-1)+1 by ring,
      periodOneHminusDouble_odd,periodOneHminusDouble_odd,map_zero]

end NLS
