import NLS.SequenceSpaces.LogarithmicWeightGrowth
import NLS.SequenceSpaces.WeightedMultiplier
import Mathlib.Topology.Order.LiminfLimsup

noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.SpectralWeight

/-- The logarithm of the inhomogeneous bracket is smaller than every positive power. -/
theorem log_one_add_div_rpow_tendsto_zero (t : ℝ) (ht : 0 < t) :
    Tendsto (fun x : ℝ => Real.log (1+x)/x^t) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => 1+x) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 tendsto_id
  have hl := (isLittleO_log_rpow_atTop ht).tendsto_div_nhds_zero.comp hshift
  have hratio : Tendsto (fun x : ℝ => (1+x)/x) atTop (𝓝 (1:ℝ)) := by
    have h : Tendsto (fun x : ℝ => 1+x⁻¹) atTop (𝓝 (1:ℝ)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add tendsto_inv_atTop_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    field_simp
    ring
  have hprod := hl.mul (hratio.rpow_const (p := t) (Or.inl one_ne_zero))
  simp only [Real.one_rpow,zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  dsimp only [Function.comp_apply]
  rw [Real.div_rpow (by linarith) hx.le]
  field_simp

/-- A dominating exponential absorbs arbitrary polynomial orders and slower exponential profiles. -/
theorem polynomial_exp_ratio_tendsto_zero (f g : ℝ → ℝ) (s a b : ℝ) (hb : 0 < b)
    (hg : Tendsto g atTop atTop)
    (hl : Tendsto (fun x => Real.log (1+x)/g x) atTop (𝓝 0))
    (hf : Tendsto (fun x => f x/g x) atTop (𝓝 0)) :
    Tendsto (fun x => (1+x)^s*Real.exp (a*f x)/Real.exp (b*g x)) atTop (𝓝 0) := by
  have hsum := ((hl.const_mul s).add (hf.const_mul a)).sub_const b
  simp only [mul_zero,add_zero,zero_sub] at hsum
  have hbot := hsum.neg_mul_atTop (neg_neg_of_pos hb) hg
  have hexp := Real.tendsto_exp_atBot.comp hbot
  apply hexp.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),hg.eventually (eventually_gt_atTop (0:ℝ))] with x hx hgx
  dsimp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1+x),← Real.exp_add,← Real.exp_sub]
  congr 1
  field_simp

/-- The logarithmic profile diverges for every real denominator exponent. -/
theorem logarithmicProfile_tendsto_atTop (σ : ℝ) :
    Tendsto (logarithmicProfile σ) atTop atTop := by
  simpa only [Real.rpow_zero,div_one] using
    logarithmicProfile_div_rpow_tendsto_atTop σ 0 (by norm_num)

/-- Polynomial factors do not change domination of the logarithmic family by Abel rates. -/
theorem polynomial_logarithmic_abel_ratio_tendsto_zero (s a b σ : ℝ)
    (hb : 0 < b) (hσ : 0 < σ) :
    Tendsto (fun x : ℝ => (1+x)^s*Real.exp (a*logarithmicProfile σ x)/Real.exp (b*x))
      atTop (𝓝 0) := by
  apply polynomial_exp_ratio_tendsto_zero (logarithmicProfile σ) id s a b hb tendsto_id
  · simpa only [Real.rpow_one,id_eq] using log_one_add_div_rpow_tendsto_zero 1 zero_lt_one
  · exact logarithmicProfile_div_self_tendsto_zero σ hσ

/-- Polynomial factors do not change domination of any sublinear Gevrey rate by the logarithmic family. -/
theorem polynomial_gevrey_logarithmic_ratio_tendsto_zero (s a b σ ρ : ℝ)
    (hb : 0 < b) (hρ : ρ < 1) :
    Tendsto (fun x : ℝ => (1+x)^s*Real.exp (a*x^ρ)/Real.exp (b*logarithmicProfile σ x))
      atTop (𝓝 0) := by
  have hf : Tendsto (fun x : ℝ => x^ρ/logarithmicProfile σ x) atTop (𝓝 0) := by
    simpa only [Pi.inv_def,inv_div] using
      (logarithmicProfile_div_rpow_tendsto_atTop σ ρ hρ).inv_tendsto_atTop
  have hl : Tendsto (fun x : ℝ => Real.log (1+x)/logarithmicProfile σ x) atTop (𝓝 0) := by
    have hhalf : Tendsto (fun x : ℝ => x^(1/2:ℝ)/logarithmicProfile σ x) atTop (𝓝 0) := by
      simpa only [Pi.inv_def,inv_div] using
        (logarithmicProfile_div_rpow_tendsto_atTop σ (1/2) (by norm_num)).inv_tendsto_atTop
    have hp := (log_one_add_div_rpow_tendsto_zero (1/2) (by norm_num)).mul hhalf
    simp only [mul_zero] at hp
    apply hp.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    have hpow : x^(1/2:ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
    field_simp
  exact polynomial_exp_ratio_tendsto_zero (fun x => x^ρ) (logarithmicProfile σ)
    s a b hb (logarithmicProfile_tendsto_atTop σ) hl hf

/-- The ratio of the actual Gevrey and logarithmic weights vanishes, for arbitrary polynomial orders. -/
theorem gevrey_div_logarithmic_tendsto_zero (s t a b σ ρ : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 < b)
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Tendsto (fun n : ℕ => gevrey s a ρ hs ha hρ hρ1.le n /
      logarithmic t b σ ht hb.le hσ hσ1 n) atTop (𝓝 0) := by
  have h := (polynomial_gevrey_logarithmic_ratio_tendsto_zero (s-t) a b σ ρ hb hρ1).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr
  intro n
  simp only [Function.comp_apply,gevrey_apply,logarithmic_apply,Int.cast_natCast,Nat.abs_cast,
    logarithmicProfile,mul_div_assoc]
  rw [Real.rpow_sub (by positivity : (0:ℝ) < 1+n)]
  ring

/-- The ratio of the actual logarithmic and pi-scaled Abel weights vanishes. -/
theorem logarithmic_div_abel_tendsto_zero (s t a b σ : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 < b)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Tendsto (fun n : ℕ => logarithmic s a σ hs ha hσ.le hσ1 n /
      abel t b ht hb.le n) atTop (𝓝 0) := by
  have h := (polynomial_logarithmic_abel_ratio_tendsto_zero s a b σ hb hσ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply squeeze_zero (fun n : ℕ => (div_pos
    ((logarithmic s a σ hs ha hσ.le hσ1).positive n) ((abel t b ht hb.le).positive n)).le) _ h
  intro n
  simp only [Function.comp_apply,logarithmic_apply,abel_apply,Int.cast_natCast,Nat.abs_cast,
    logarithmicProfile,mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) _
  have hp : 1 ≤ (1+|(n:ℝ)*Real.pi|)^t := Real.one_le_rpow (by linarith [abs_nonneg ((n:ℝ)*Real.pi)]) ht
  nlinarith [Real.exp_pos (b*(n:ℝ))]

/-- Vanishing ratios give a global weight comparison, including the finite head and negative indices. -/
theorem le_mul_of_ratio_tendsto_zero (v w : SpectralWeight)
    (h : Tendsto (fun n : ℕ => v n/w n) atTop (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, v n ≤ C*w n := by
  obtain ⟨C,hC⟩ := h.bddAbove_range
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro n
  have hn := hC (mem_range_self n.natAbs)
  simp only [Int.natCast_natAbs,apply_abs] at hn
  exact (div_le_iff₀ (w.positive n)).mp (hn.trans (le_max_left C 1))


/-- The resulting inclusion of weighted coefficient spaces preserves every raw coefficient,
for every Banach exponent, including infinity. -/
theorem exists_coefficient_inclusion_of_ratio_tendsto_zero
    (v w : SpectralWeight) (h : Tendsto (fun n : ℕ => v n/w n) atTop (𝓝 0))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ L : WeightedCoeff w.toWeight p →L[ℂ] WeightedCoeff v.toWeight p,
      Function.Injective L ∧ ∀ a n, (L a).val n = a.val n := by
  obtain ⟨C,hC,hbound⟩ := le_mul_of_ratio_tendsto_zero v w h
  have hm : ∀ n, v.toWeight n*‖(1:ℂ)‖ ≤ C*w.toWeight n := by
    simpa only [norm_one,mul_one,toWeight_apply] using hbound
  let L := WeightedCoeff.weightedMultiplierCLM (p := p) w.toWeight v.toWeight (fun _ => (1:ℂ)) C hC.le hm
  have he (a : WeightedCoeff w.toWeight p) (n : ℤ) : (L a).val n = a.val n := by
    exact one_mul _
  refine ⟨L,?_,he⟩
  intro a b hab
  apply Subtype.ext
  funext n
  simpa only [he] using congrArg (fun c => c.val n) hab

end NLS.SpectralWeight
