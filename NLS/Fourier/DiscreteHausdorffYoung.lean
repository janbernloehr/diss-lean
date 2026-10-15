import NLS.SequenceSpaces.FiniteMatrixInterpolation
import NLS.Fourier.DiscreteParseval

/-!
# Discrete Hausdorff–Young with exact normalization

The finite cyclic Fourier transform maps ℓp to ℓq with factor N^(1/q)
for conjugate finite exponents and 1 < p ≤ 2. The normalized qth moment
therefore has constant one.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.Fourier
open NLS.FiniteMatrix
variable {N : ℕ} [NeZero N]

/-- The negative-phase kernel used by Mathlib’s unnormalized discrete Fourier transform. -/
def dftKernel (k j : ZMod N) : ℂ := ZMod.stdAddChar (-(j*k))

theorem pair_dftKernel (a b : ZMod N → ℂ) :
    pair dftKernel a b = ∑ k, ZMod.dft a k * b k := by
  simp only [pair,ZMod.dft_apply,smul_eq_mul,Finset.sum_mul,dftKernel]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem norm_pair_dftKernel_one (a b : ZMod N → ℂ) :
    ‖pair dftKernel a b‖ ≤ 1*‖WithLp.toLp 1 a‖*‖WithLp.toLp 1 b‖ := by
  rw [pair_dftKernel]
  calc
    _ ≤ ∑ k, ‖ZMod.dft a k * b k‖ := norm_sum_le _ _
    _ ≤ ∑ k, (∑ j, ‖a j‖)*‖b k‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_dft_le_sum_norm a k) (norm_nonneg _)
    _ = _ := by
      rw [PiLp.norm_eq_sum (by norm_num : 0 < (1:ℝ≥0∞).toReal),
        PiLp.norm_eq_sum (by norm_num : 0 < (1:ℝ≥0∞).toReal)]
      simp [Finset.mul_sum]

theorem norm_pair_dftKernel_two (a b : ZMod N → ℂ) :
    ‖pair dftKernel a b‖ ≤ Real.sqrt N*‖WithLp.toLp 2 a‖*‖WithLp.toLp 2 b‖ := by
  rw [pair_dftKernel]
  calc
    _ ≤ ∑ k, ‖ZMod.dft a k * b k‖ := norm_sum_le _ _
    _ = ∑ k, ‖ZMod.dft a k‖ * ‖b k‖ := by simp only [norm_mul]
    _ ≤ Real.sqrt (∑ k, ‖ZMod.dft a k‖^2)*Real.sqrt (∑ k, ‖b k‖^2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖WithLp.toLp 2 (ZMod.dft a)‖ * ‖WithLp.toLp 2 b‖ := by
      rw [PiLp.norm_eq_sum (by norm_num : 0 < (2:ℝ≥0∞).toReal),
        PiLp.norm_eq_sum (by norm_num : 0 < (2:ℝ≥0∞).toReal)]
      simp only [ENNReal.toReal_ofNat,Real.rpow_two,Real.sqrt_eq_rpow]
    _ = _ := by rw [norm_dft_piLp_two]

theorem norm_pair_dftKernel_interpolate {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp₂ : p ≤ 2)
    (a b : ZMod N → ℂ) :
    ‖pair dftKernel a b‖ ≤ (N:ℝ)^(1-1/p.toReal)*‖WithLp.toLp p a‖*‖WithLp.toLp p b‖ := by
  have hpt : p ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hp₂
  have hp : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hpt
  have hp₁ : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_le_toReal (by simp) hpt).mpr (Fact.out : 1 ≤ p)
  have hp₂r : p.toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using
      (ENNReal.toReal_le_toReal hpt (by norm_num)).mpr hp₂
  have ht₀ : 0 ≤ 2-2/p.toReal := by
    have h : 2/p.toReal ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
    linarith
  have ht₁ : 2-2/p.toReal ≤ 1 := by
    have h : 1 ≤ 2/p.toReal := (le_div_iff₀ hp).mpr (by linarith)
    linarith
  have hrel : p.toReal*((1-(2-2/p.toReal))/1+(2-2/p.toReal)/2) = 1 := by
    field_simp
    ring
  have h := norm_pair_interpolate (r := p) (s := p) (t := 2-2/p.toReal)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp hp ht₀ ht₁
    (by simpa only [ENNReal.toReal_one,ENNReal.toReal_ofNat] using hrel)
    (by simpa only [ENNReal.toReal_one,ENNReal.toReal_ofNat] using hrel)
    dftKernel zero_le_one (Real.sqrt_nonneg N) norm_pair_dftKernel_one norm_pair_dftKernel_two a b
  have hc : (Real.sqrt (N:ℝ))^(2-2/p.toReal) = (N:ℝ)^(1-1/p.toReal) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 1
    ring
  simpa only [Real.one_rpow,one_mul,hc] using h

/-- Discrete Hausdorff–Young with the exact N^(1/q) norm factor. -/
theorem norm_dft_hausdorffYoung_finite {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp₂ : p ≤ 2) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (a : ZMod N → ℂ) :
    ‖WithLp.toLp q (ZMod.dft a)‖ ≤ (N:ℝ)^(1/q.toReal)*‖WithLp.toLp p a‖ := by
  let : q.HolderConjugate p := inferInstance
  obtain ⟨b,hb,he⟩ := exists_norming_test hq hp (ZMod.dft a)
  have h := norm_pair_dftKernel_interpolate hp₂ a b
  rw [pair_dftKernel,he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at h
  have hpq : p.toReal.HolderConjugate q.toReal := by
    simpa using ENNReal.HolderTriple.toReal 1 hp hq
  have hh : 1/p.toReal + 1/q.toReal = 1 := by simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hexp : 1-1/p.toReal = 1/q.toReal := by linarith
  rw [hexp] at h
  exact h.trans (by
    calc
      _ ≤ (N:ℝ)^(1/q.toReal)*‖WithLp.toLp p a‖*1 := by gcongr
      _ = _ := mul_one _)

end NLS.Fourier

namespace NLS.Fourier
open NLS.FiniteMatrix
variable {L : ℝ} [Fact (0 < L)]

theorem norm_piLp_rpow {ι : Type*} [Fintype ι] {p : ℝ≥0∞} (hp : 0 < p.toReal) (a : ι → ℂ) :
    ‖WithLp.toLp p a‖^p.toReal = ∑ i, ‖a i‖^p.toReal := by
  rw [PiLp.norm_eq_sum hp,← Real.rpow_mul (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)),
    one_div_mul_cancel hp.ne',Real.rpow_one]

/-- The normalized discrete qth moment is bounded by the input p-norm to power q. -/
theorem dft_moment_bound {N : ℕ} [NeZero N] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp₂ : p ≤ 2) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (a : ZMod N → ℂ) :
    (N:ℝ)⁻¹ * ∑ j, ‖ZMod.dft a j‖^q.toReal ≤ ‖WithLp.toLp p a‖^q.toReal := by
  have hd := norm_dft_hausdorffYoung_finite hp₂ hp hq a
  have h := Real.rpow_le_rpow (norm_nonneg _) hd hq.le
  rw [norm_piLp_rpow hq,Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _) (norm_nonneg _),
    ← Real.rpow_mul (Nat.cast_nonneg N),one_div_mul_cancel hq.ne',Real.rpow_one] at h
  have hN : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hm := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N))
  simpa only [← mul_assoc,inv_mul_cancel₀ hN,one_mul] using hm

end NLS.Fourier
