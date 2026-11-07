import NLS.ComplexAnalysis.LexicographicOrder
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.PNat.Basic

/-! Quantitative squaring estimates and isolation of ordered complex
spectral sequences in the literal positive-index energy circles. -/
noncomputable section
open Complex Set Metric
namespace NLS.ComplexAnalysis

/-- A small frequency displacement gives an explicit shifted energy bound. -/
theorem norm_squared_shift_displacement_le (z w c : ℂ) :
    ‖z^2-c-w^2‖ ≤ ‖z-w‖*(2*‖w‖+‖z-w‖)+‖c‖ := by
  have he : z^2-c-w^2 = (z-w)*(2*w+(z-w))-c := by ring
  rw [he]
  calc
    _ ≤ ‖(z-w)*(2*w+(z-w))‖+‖c‖ := norm_sub_le _ _
    _ = ‖z-w‖*‖2*w+(z-w)‖+‖c‖ := by rw [norm_mul]
    _ ≤ ‖z-w‖*(2*‖w‖+‖z-w‖)+‖c‖ := by
      gcongr
      exact (norm_add_le _ _).trans (by simp)

/-- For an ordered full complex sequence, uniformly small high energy
errors isolate EVERY high label from ALL other labels, including the central
block, in the source circle of radius n. -/
theorem squaredFrequencyCircle_isolates_of_monotone
    (mu : ℕ+ → ℂ) (hmono : Monotone (fun n => (mu n).re))
    (K : ℕ) (herr : ∀ m : ℕ+, K < (m:ℕ) →
      ‖mu m-((Real.pi:ℂ)*(m:ℕ))^2‖ < (m:ℝ)/4)
    (n : ℕ+) (hn : K+1 < (n:ℕ)) :
    mu n ∈ ball (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ) ∧
      ∀ m : ℕ+, m ≠ n → (n:ℝ) < ‖mu m-((Real.pi:ℂ)*(n:ℕ))^2‖ := by
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast n.property
  have hpi : 2 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hcenter (k : ℕ+) : (((Real.pi:ℂ)*(k:ℕ))^2).re = (Real.pi*(k:ℝ))^2 := by
    simp only [pow_two,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.natCast_re,Complex.natCast_im,mul_zero,zero_mul,sub_zero,add_zero]
  refine ⟨?_,?_⟩
  · rw [mem_ball,dist_eq_norm]
    exact (herr n (by omega)).trans (by linarith)
  · intro m hmn
    rcases lt_or_gt_of_ne hmn with hmn | hnm
    · have hmnNat : (m:ℕ) < (n:ℕ) := hmn
      let j : ℕ+ := ⟨(n:ℕ)-1,by omega⟩
      have hj : K < (j:ℕ) := by dsimp [j]; omega
      have hjn : (j:ℝ) = (n:ℝ)-1 := by
        have he : (j:ℕ)+1 = (n:ℕ) := by dsimp [j]; omega
        have hh : (j:ℝ)+1 = (n:ℝ) := by exact_mod_cast he
        linarith
      have hmj : m ≤ j := by change (m:ℕ) ≤ (j:ℕ); dsimp [j]; omega
      have he := Complex.re_le_norm (mu j-((Real.pi:ℂ)*(j:ℕ))^2)
      rw [sub_re,hcenter] at he
      have hb := he.trans_lt (herr j hj)
      have hord := hmono hmj
      have hnorm := (neg_le_abs _).trans (Complex.abs_re_le_norm (mu m-((Real.pi:ℂ)*(n:ℕ))^2))
      rw [sub_re,hcenter] at hnorm
      have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast n.property
      have hp : 0 < (2*(n:ℝ)-1) := by linarith
      have hgap := mul_pos (sub_pos.mpr hpi) hp
      rw [hjn] at hb
      nlinarith
    · have hnmNat : (n:ℕ) < (m:ℕ) := hnm
      let j : ℕ+ := n+1
      have hj : K < (j:ℕ) := by dsimp [j]; omega
      have hjn : (j:ℝ) = (n:ℝ)+1 := by simp [j]
      have hjm : j ≤ m := by
        change (j:ℕ) ≤ (m:ℕ)
        dsimp [j]
        omega
      have he := (neg_le_abs _).trans (Complex.abs_re_le_norm (mu j-((Real.pi:ℂ)*(j:ℕ))^2))
      rw [sub_re,hcenter] at he
      have hb := he.trans_lt (herr j hj)
      have hord := hmono hjm
      have hnorm := Complex.re_le_norm (mu m-((Real.pi:ℂ)*(n:ℕ))^2)
      rw [sub_re,hcenter] at hnorm
      have hp : 0 < (2*(n:ℝ)+1) := by linarith
      have hgap := mul_pos (sub_pos.mpr hpi) hp
      rw [hjn] at hb
      nlinarith

end NLS.ComplexAnalysis
