import NLS.SequenceSpaces.WeightedCubicFrequencyPacket
import NLS.SequenceSpaces.SobolevDerivative

/-! The extra actual gap factor absorbs the arbitrarily small loss in
the negative-weight reciprocal columns, strictly above the weak endpoint. -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem norm_int_le_sobolev_one (k : ℤ) : ‖(k : ℂ)‖≤Weight.sobolev 1 k := by
  norm_num only [Complex.norm_intCast,Weight.sobolev_apply,Real.rpow_one]
  linarith

theorem negative_weighted_cubic_coeff_bound
    (A σ t S : ℝ) (horder : 1≤σ+t+(1-A))
    (g : ℤ → ℂ) (h : Coeff 1)
    (hh : ∀ k : ℤ, ‖h k‖=Weight.sobolev (1-A) k*‖g k‖^2)
    (hg : ∀ k : ℤ, Weight.sobolev t k*‖g k‖≤S) (k : ℤ) :
    ‖(k : ℂ)‖*‖g k‖^3/Weight.sobolev σ k≤S*‖h k‖ := by
  have hi := (norm_int_le_sobolev_one k).trans (Weight.sobolev_mono horder k)
  rw [Weight.sobolev_add,Weight.sobolev_add] at hi
  calc
    _≤(Weight.sobolev σ k*Weight.sobolev t k*Weight.sobolev (1-A) k)*‖g k‖^3/Weight.sobolev σ k := by
      apply div_le_div_of_nonneg_right _ ((Weight.sobolev σ).positive k).le
      exact mul_le_mul_of_nonneg_right hi (by positivity)
    _=(Weight.sobolev t k*‖g k‖)*(Weight.sobolev (1-A) k*‖g k‖^2) := by
      rw [show (Weight.sobolev σ k*Weight.sobolev t k*Weight.sobolev (1-A) k)*‖g k‖^3=
        Weight.sobolev σ k*((Weight.sobolev t k*‖g k‖)*(Weight.sobolev (1-A) k*‖g k‖^2)) by ring]
      exact mul_div_cancel_left₀ _ ((Weight.sobolev σ).positive k).ne'
    _≤S*‖h k‖ := by
      rw [←hh k]
      exact mul_le_mul_of_nonneg_right (hg k) (norm_nonneg _)

theorem negative_weighted_diagonal_bound
    (A D : ℝ) (hD : 0≤D) (g : ℤ → ℂ) (h : Coeff 1)
    (hh : ∀ k : ℤ, ‖h k‖=Weight.sobolev (1-A) k*‖g k‖^2)
    (n : ℤ) (x : ℂ) (hx : ‖x‖≤D*‖g n‖^2) :
    Weight.sobolev (-A) n*‖(n : ℂ)‖*‖x‖≤D*‖h n‖ := by
  have hi := mul_le_mul_of_nonneg_left (norm_int_le_sobolev_one n) ((Weight.sobolev (-A)).positive n).le
  rw [←Weight.sobolev_add,show -A+1=1-A by ring] at hi
  calc
    _≤(Weight.sobolev (-A) n*‖(n : ℂ)‖)*(D*‖g n‖^2) :=
      mul_le_mul_of_nonneg_left hx (mul_nonneg ((Weight.sobolev (-A)).positive n).le (norm_nonneg _))
    _≤Weight.sobolev (1-A) n*(D*‖g n‖^2) := mul_le_mul_of_nonneg_right hi (by positivity)
    _=D*‖h n‖ := by rw [hh n];ring

end NLS.Coeff
