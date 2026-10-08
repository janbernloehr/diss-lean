import NLS.SequenceSpaces.DisjointCoefficientSums
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.NonnegativeActions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Nonnegative finite blocks with fixed Hilbert norm and vanishing larger-exponent norms -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- A block of N+1 unit coordinates, on nonnegative signed indices. -/
def positiveUnitBlock (p : ℝ≥0∞) (N : ℕ) : Coeff p :=
  ∑ k ∈ Finset.range (N+1), lp.single p (k:ℤ) (1:ℂ)

/-- Normalize the block in the Hilbert norm, using the same coefficients at every exponent. -/
def positiveFlatBlock (p : ℝ≥0∞) (N : ℕ) : Coeff p :=
  (((((N+1:ℕ):ℝ)^(-(1/2:ℝ))) : ℝ) : ℂ) • positiveUnitBlock p N

private theorem block_disjoint (p : ℝ≥0∞) (N : ℕ) :
    ((Finset.range (N+1) : Finset ℕ) : Set ℕ).Pairwise
      (fun i j => Disjoint (Function.support (lp.single p (i:ℤ) (1:ℂ)))
        (Function.support (lp.single p (j:ℤ) (1:ℂ)))) := by
  intro i _ j _ hij
  apply Set.disjoint_left.mpr
  intro n hn hi
  have hni : n = (i:ℤ) := by
    by_contra h
    exact hn (by simp [lp.single_apply,h])
  have hnj : n = (j:ℤ) := by
    by_contra h
    exact hi (by simp [lp.single_apply,h])
  exact hij (by exact_mod_cast hni.symm.trans hnj)

theorem norm_positiveUnitBlock (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (N : ℕ) :
    ‖positiveUnitBlock p N‖ = ((N+1:ℕ):ℝ)^(1/p.toReal) := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) hp
  apply (Real.rpow_left_inj (norm_nonneg _) (by positivity) hpR.ne').mp
  rw [positiveUnitBlock,norm_sum_rpow_of_disjoint hpR _ _ (block_disjoint p N),
    ← Real.rpow_mul (by positivity : (0:ℝ) ≤ ((N+1:ℕ):ℝ)),one_div_mul_cancel hpR.ne',Real.rpow_one]
  simp only [lp.norm_single (lt_of_lt_of_le zero_lt_one Fact.out),norm_one,Real.one_rpow,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]

theorem norm_positiveFlatBlock (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (N : ℕ) :
    ‖positiveFlatBlock p N‖ = ((N+1:ℕ):ℝ)^(1/p.toReal-1/2) := by
  rw [positiveFlatBlock,norm_smul,Complex.norm_of_nonneg (Real.rpow_nonneg (by positivity) _),
    norm_positiveUnitBlock p hp N,← Real.rpow_add (by positivity)]
  congr 1
  ring

@[simp] theorem norm_positiveFlatBlock_two (N : ℕ) : ‖positiveFlatBlock 2 N‖ = 1 := by
  rw [norm_positiveFlatBlock 2 (by simp)]
  norm_num

theorem positiveUnitBlock_exponent {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (N : ℕ) : exponentInclusion hpq (positiveUnitBlock p N) = positiveUnitBlock q N := by
  rw [positiveUnitBlock,map_sum,positiveUnitBlock]
  apply Finset.sum_congr rfl
  intro k _
  ext n
  simp only [exponentInclusion_apply,lp.single_apply]

theorem positiveFlatBlock_exponent {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (N : ℕ) : exponentInclusion hpq (positiveFlatBlock p N) = positiveFlatBlock q N := by
  rw [positiveFlatBlock,map_smul,positiveUnitBlock_exponent,positiveFlatBlock]

theorem positiveFlatBlock_mem_nonnegativeLocus (p : ℝ≥0∞) (N : ℕ) :
    positiveFlatBlock p N ∈ nonnegativeLocus p := by
  intro n
  simp only [positiveFlatBlock,positiveUnitBlock,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    lp.coeFn_sum,Finset.sum_apply,lp.single_apply,Pi.single_apply]
  constructor
  · simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero]
    have h : (∑ k ∈ Finset.range (N+1), if n = (k:ℤ) then (1:ℂ) else 0).im = 0 := by
      rw [Complex.im_sum]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs <;> rfl
    rw [h,mul_zero]
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro k _
    split_ifs <;> norm_num

/-- Above the Hilbert exponent the same normalized blocks converge to zero. -/
theorem tendsto_positiveFlatBlock {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) (h2q : 2 < q) :
    Tendsto (positiveFlatBlock q) atTop (𝓝 0) := by
  have hqR : 2 < q.toReal := by exact_mod_cast (ENNReal.toReal_lt_toReal (by norm_num) hq).mpr h2q
  have he : 0 < (1/2:ℝ)-1/q.toReal := by
    apply sub_pos.mpr
    exact (div_lt_div_iff₀ (by linarith : 0 < q.toReal) (by norm_num : (0:ℝ) < 2)).mpr (by linarith)
  have ht := (tendsto_rpow_neg_atTop he).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_positiveFlatBlock q hq,neg_sub,Function.comp_def] using! ht

end NLS.Coeff
