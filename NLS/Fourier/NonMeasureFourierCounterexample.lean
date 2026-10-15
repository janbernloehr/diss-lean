import NLS.Fourier.ShiftedRudinShapiro
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.Fourier.PeriodicDistributionMeasure
import Mathlib.Analysis.PSeries

/-!
# Lemma A.3: a Fourier–Lebesgue distribution which is not a measure

Rudin–Shapiro blocks with amplitudes (j+1)/2^j have summable ℓᵖ norms for
every finite p > 2. Their ℓ³ sum defines one original periodic distribution;
its coefficients belong to all these spaces, including infinity.

Testing against the conjugate polynomial in block j gives (j+1)*2^j,
while that test has uniform norm at most sqrt(2)*2^j. Thus the distribution
has no bounded extension to continuous functions, and cannot be a complex
measure. The construction works at every positive physical period.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal ZeroAtInfty
namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

local instance instOneLeThreeNonMeasure : Fact ((1:ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

/-- The jth block of the distributional counterexample at exponent p. -/
def nonMeasureBlockCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) : Coeff p :=
  (((((j+1:ℕ):ℝ) / (2:ℝ)^j) : ℝ) : ℂ) •
    Coeff.shift (4^j:ℕ) (Coeff.ofFinsupp (rudinShapiroCoefficients (L := L) (2*j)))

/-- The block has the scaled actual Fourier coefficients of the shifted polynomial. -/
theorem nonMeasureBlockCoefficients_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ℕ) (k : ℤ) :
    nonMeasureBlockCoefficients (L := L) p j k =
      (((((j+1:ℕ):ℝ) / (2:ℝ)^j) : ℝ) : ℂ) * fourierCoeff (shiftedRudinShapiro (L := L) j) k := by
  simp only [nonMeasureBlockCoefficients,lp.coeFn_smul,Pi.smul_apply,Coeff.shift_apply,
    Coeff.ofFinsupp_apply,rudinShapiroCoefficients_apply,shiftedRudinShapiro,fourierCoeff_fourier_mul,smul_eq_mul]

/-- The exact finite-p block norm is a polynomial factor times a geometric factor. -/
theorem norm_nonMeasureBlockCoefficients {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) (j : ℕ) :
    ‖nonMeasureBlockCoefficients (L := L) p j‖ =
      ((j+1:ℕ):ℝ) * ((2:ℝ)^(2/p.toReal-1))^j := by
  rw [nonMeasureBlockCoefficients,norm_smul,Coeff.norm_shift,norm_rudinShapiroCoefficients hp,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  have hpow : (((2:ℝ)^(2*j))^(1/p.toReal)) = ((2:ℝ)^(2/p.toReal))^j := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [hpow,Real.rpow_sub (by norm_num : (0:ℝ) < 2),Real.rpow_one,div_pow]
  field_simp

/-- For every finite p > 2, the block series converges absolutely in ℓᵖ. -/
theorem summable_norm_nonMeasureBlockCoefficients {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp₂ : 2 < p) (hpt : p ≠ ⊤) :
    Summable (fun j : ℕ => ‖nonMeasureBlockCoefficients (L := L) p j‖) := by
  have hp : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hpt
  have hp₂r : 2 < p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_lt_toReal (by norm_num) hpt).mpr hp₂
  let r : ℝ := 2^(2/p.toReal-1)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
    have h : (2:ℝ)/p.toReal < 1 := (div_lt_iff₀ hp).mpr (by simpa using hp₂r)
    linarith)
  have hs1 : Summable (fun j : ℕ => (j:ℝ)*r^j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖r‖ < 1 by rwa [Real.norm_eq_abs,abs_of_nonneg hr0])
  have hs0 : Summable (fun j : ℕ => r^j) := summable_geometric_of_lt_one hr0 hr
  simpa only [norm_nonMeasureBlockCoefficients hp,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    using hs1.add hs0

/-- The Banach-space sum of the counterexample blocks, used at finite p > 2. -/
def nonMeasureCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] : Coeff p :=
  ∑' j : ℕ, nonMeasureBlockCoefficients (L := L) p j

/-- At every finite p > 2, coefficient extraction gives the same scalar series. -/
theorem nonMeasureCoefficients_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp₂ : 2 < p) (hpt : p ≠ ⊤) (k : ℤ) :
    nonMeasureCoefficients (L := L) p k = ∑' j : ℕ,
      (((((j+1:ℕ):ℝ) / (2:ℝ)^j) : ℝ) : ℂ) * fourierCoeff (shiftedRudinShapiro (L := L) j) k := by
  let F := lp.evalCLM ℂ (fun _ : ℤ => ℂ) p k
  change F (∑' j : ℕ, nonMeasureBlockCoefficients p j) = _
  rw [F.map_tsum (summable_norm_nonMeasureBlockCoefficients (L := L) hp₂ hpt).of_norm]
  change (∑' j : ℕ, nonMeasureBlockCoefficients (L := L) p j k) = _
  simp only [nonMeasureBlockCoefficients_apply]

open SmoothPeriodicTest

/-- The original periodic distribution obtained by synthesizing the ℓ³ coefficient sum. -/
def nonMeasureDistribution : Distribution L :=
  ((PeriodicFourierLebesgue.unweightedCoefficients (L := L) 3).symm (nonMeasureCoefficients (L := L) 3)).val

/-- The original distribution has the constructed Fourier coefficients. -/
theorem nonMeasureDistribution_coefficient (k : ℤ) :
    nonMeasureDistribution (L := L) (mode (-k)) = ∑' j : ℕ,
      (((((j+1:ℕ):ℝ) / (2:ℝ)^j) : ℝ) : ℂ) * fourierCoeff (shiftedRudinShapiro (L := L) j) k := by
  rw [nonMeasureDistribution,← PeriodicFourierLebesgue.unweightedCoefficients_apply]
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact nonMeasureCoefficients_apply (by norm_num) (by norm_num) k

/-- The same distribution belongs to every FLᵖ with p > 2, including infinity. -/
theorem nonMeasureDistribution_mem_fourierLebesgue {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp₂ : 2 < p) : nonMeasureDistribution (L := L) ∈ periodicFourierLebesgueSubmodule Weight.one p := by
  change Memℓp (fun k => (Weight.one k : ℂ) * nonMeasureDistribution (L := L) (mode (-k))) p
  simp only [Weight.one_apply,Complex.ofReal_one,one_mul]
  by_cases hpt : p = ⊤
  · subst p
    let a := Coeff.exponentInclusion (show (3:ℝ≥0∞) ≤ ⊤ from le_top) (nonMeasureCoefficients (L := L) 3)
    have he : (fun k => nonMeasureDistribution (L := L) (mode (-k))) = fun k => a k := by
      funext k
      rw [nonMeasureDistribution_coefficient]
      exact (nonMeasureCoefficients_apply (L := L) (p := 3) (by norm_num) (by norm_num) k).symm
    rw [he]
    exact a.property
  · have he : (fun k => nonMeasureDistribution (L := L) (mode (-k))) = fun k => nonMeasureCoefficients (L := L) p k := by
      funext k
      rw [nonMeasureDistribution_coefficient,nonMeasureCoefficients_apply hp₂ hpt]
    rw [he]
    exact (nonMeasureCoefficients (L := L) p).property

/-- On a selected block, all other blocks contribute zero. -/
theorem nonMeasureDistribution_block_coefficient (j : ℕ) (k : ℤ)
    (hk : (4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ)) :
    nonMeasureDistribution (L := L) (mode (-k)) =
      (((((j+1:ℕ):ℝ) / (2:ℝ)^j) : ℝ) : ℂ) * fourierCoeff (shiftedRudinShapiro (L := L) j) k := by
  rw [nonMeasureDistribution_coefficient,tsum_eq_single j]
  intro i hi
  have hn := shiftedRudinShapiro_blocks_disjoint (Ne.symm hi) k hk
  have hz : fourierCoeff (shiftedRudinShapiro (L := L) i) k = 0 := by
    apply norm_eq_zero.mp
    rw [shiftedRudinShapiro_coeff_norm,if_neg hn]
  rw [hz,mul_zero]

/-- The conjugate block polynomial as an original smooth periodic test. -/
def nonMeasureBlockTest (j : ℕ) : SmoothPeriodicTest L :=
  ∑ k ∈ shiftedRudinShapiroBlock j, star (fourierCoeff (shiftedRudinShapiro (L := L) j) k) • mode (-k)

/-- The physical-circle test is exactly the conjugate shifted polynomial. -/
theorem toContinuous_nonMeasureBlockTest (j : ℕ) :
    toContinuousCLM (nonMeasureBlockTest (L := L) j) = star (shiftedRudinShapiro j) := by
  rw [← continuousFourierPolynomial_shiftedRudinShapiro j]
  simp only [nonMeasureBlockTest,map_sum,map_smul,toContinuousCLM_mode,continuousFourierPolynomial]
  ext x
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    ContinuousMap.star_apply,star_sum,star_mul,fourier_neg,starRingEnd_apply,mul_comm]

/-- The exact pairing with a conjugate block grows as (j+1)*2^j. -/
theorem nonMeasureDistribution_blockTest (j : ℕ) :
    nonMeasureDistribution (L := L) (nonMeasureBlockTest j) =
      ((((j+1:ℕ):ℝ) * (2:ℝ)^j : ℝ) : ℂ) := by
  classical
  rw [nonMeasureBlockTest,map_sum]
  have ht (k : ℤ) (hk : k ∈ shiftedRudinShapiroBlock j) :
      nonMeasureDistribution (L := L)
          (star (fourierCoeff (shiftedRudinShapiro (L := L) j) k) • mode (-k)) =
        (((((j+1:ℕ):ℝ) / (2:ℝ)^j) : ℝ) : ℂ) := by
    have hki : (4^j:ℕ) ≤ k ∧ k < 2*(4^j:ℕ) := Finset.mem_Ico.mp hk
    rw [map_smul,nonMeasureDistribution_block_coefficient j k hki,smul_eq_mul]
    rw [mul_left_comm,← mul_assoc]
    have hc : star (fourierCoeff (shiftedRudinShapiro (L := L) j) k) *
        fourierCoeff (shiftedRudinShapiro (L := L) j) k = 1 := by
      change (starRingEnd ℂ) _ * _ = 1
      rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,
        shiftedRudinShapiro_coeff_norm,if_pos hki]
      norm_num
    rw [mul_assoc,hc,mul_one]
  rw [Finset.sum_congr rfl ht,Finset.sum_const]
  have hcard : (shiftedRudinShapiroBlock j).card = 4^j := by
    rw [shiftedRudinShapiroBlock,Int.card_Ico]
    have he : (2*(4^j:ℕ):ℤ) - (4^j:ℕ) = (4^j:ℕ) := by omega
    rw [he,Int.toNat_natCast]
  rw [hcard,nsmul_eq_mul]
  have hpow : (4:ℝ)^j = ((2:ℝ)^j)^2 := by
    rw [← pow_mul,show j*2 = 2*j by omega,pow_mul]
    norm_num
  push_cast
  have hpowC : (4:ℂ)^j = ((2:ℂ)^j)^2 := by exact_mod_cast hpow
  rw [hpowC]
  field_simp

/-- No bounded functional on continuous functions can extend this distribution. -/
theorem nonMeasureDistribution_order_ne_zero : (nonMeasureDistribution (L := L)).order ≠ 0 := by
  intro ho
  obtain ⟨F,hF,_⟩ := (Distribution.order_zero_iff_physical_extension _).mp ho
  have hb (j : ℕ) : ((j+1:ℕ):ℝ) ≤ ‖F‖ * Real.sqrt 2 := by
    have h := F.le_opNorm (toContinuousCLM (nonMeasureBlockTest (L := L) j))
    rw [hF,nonMeasureDistribution_blockTest,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (by positivity),toContinuous_nonMeasureBlockTest,norm_star] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left (norm_shiftedRudinShapiro_le j) (norm_nonneg F))
    rw [← mul_assoc] at h'
    exact (mul_le_mul_iff_left₀ (show (0:ℝ) < 2^j by positivity)).mp h'
  obtain ⟨j,hj⟩ := exists_nat_gt (‖F‖ * Real.sqrt 2)
  have h := hb j
  push_cast at h
  linarith

/-- No actual complex measure represents the constructed original distribution. -/
theorem nonMeasureDistribution_not_measure :
    ¬∃ μ : ComplexMeasure (AddCircle L), Distribution.ofComplexMeasure μ = nonMeasureDistribution := by
  rintro ⟨μ,hμ⟩
  apply nonMeasureDistribution_order_ne_zero (L := L)
  rw [← hμ]
  exact Distribution.ofComplexMeasure_order μ

/-- Lemma A.3 on the original physical circle, including the infinity exponent. -/
theorem exists_fourierLebesgue_above_two_not_measure :
    ∃ u : Distribution L,
      (∀ p : ℝ≥0∞, 2 < p → u ∈ periodicFourierLebesgueSubmodule Weight.one p) ∧
      ¬∃ μ : ComplexMeasure (AddCircle L), Distribution.ofComplexMeasure μ = u := by
  refine ⟨nonMeasureDistribution,?_,nonMeasureDistribution_not_measure⟩
  intro p hp
  let : Fact (1 ≤ p) := ⟨(by norm_num : (1:ℝ≥0∞) ≤ 2).trans hp.le⟩
  exact nonMeasureDistribution_mem_fourierLebesgue hp

end NLS.Fourier
