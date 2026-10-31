import NLS.ComplexAnalysis.QuadraticCriticalIdentity
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Explicit scalar estimates in the proofs of F.1 and F.2 -/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

/-- The quadratic remainder on the half-gap circle has the exact one-half coefficient. -/
theorem appendixF_quadratic_boundary_estimate (a γ G d : ℂ) (r s : ℝ)
    (ha : ‖a‖ = ‖γ‖/2) (hγ : γ ≠ 0) (hs : 0 < s)
    (hG : s ≤ ‖G‖) (hd : ‖d‖ ≤ r) (hsmall : ‖γ‖*r ≤ s) :
    ‖(a^2-γ^2/4)*d‖ ≤ ‖γ‖^2*r/2 ∧
      ‖γ‖^2*r/2 < s*‖γ‖ ∧ s*‖γ‖ ≤ ‖2*a*G‖ := by
  have hr : 0 ≤ r := (norm_nonneg d).trans hd
  have hg : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hq : ‖a^2-γ^2/4‖ ≤ ‖γ‖^2/2 := by
    have h := norm_sub_le (a^2) (γ^2/4)
    rw [norm_pow,norm_div,norm_pow,Complex.norm_ofNat,ha] at h
    nlinarith
  refine ⟨?_,?_,?_⟩
  · rw [norm_mul]
    have h := mul_le_mul hq hd (norm_nonneg d) (by positivity : 0 ≤ ‖γ‖^2/2)
    nlinarith
  · have h := mul_le_mul_of_nonneg_right hsmall hg.le
    have hp : 0 < s*‖γ‖ := mul_pos hs hg
    nlinarith
  · rw [norm_mul,norm_mul,Complex.norm_ofNat,ha]
    have h := mul_le_mul_of_nonneg_right hG hg.le
    nlinarith

/-- The affine endpoint path has the literal quadratic factorization used in F.2. -/
theorem appendixF_endpoint_segment_factorization (ρ₁ ρ₂ ν t : ℂ) :
    let z := ρ₁+t*(ν-ρ₁)
    (((ρ₁+ρ₂)/2)-z)^2-(ρ₂-ρ₁)^2/4 = t*(ρ₁-ν)*(ρ₂-z) := by
  dsimp only
  ring

/-- The base radicand stays above the source's explicit positive lower bound. -/
theorem appendixF_endpoint_radicand_lower (σ t : ℝ) (hσ : 0 < σ) (ht : t ∈ Icc 0 1) :
    0 < σ/(1/2+σ) ∧ σ/(1/2+σ) ≤ σ*(1+t*σ)/(1/2+t*σ)^2 := by
  have htσ : 0 ≤ t*σ := mul_nonneg ht.1 hσ.le
  have htσ₁ : t*σ ≤ σ := by nlinarith [mul_le_mul_of_nonneg_right ht.2 hσ.le]
  have hden : 0 < (1/2:ℝ)+t*σ := by positivity
  have hden₀ : 0 < (1/2:ℝ)+σ := by positivity
  have hquad : ((1/2:ℝ)+t*σ)^2 ≤ (1+t*σ)*(1/2+σ) := by
    have hprod := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg σ)
    nlinarith
  refine ⟨div_pos hσ hden₀,?_⟩
  apply (div_le_div_iff₀ hden₀ (sq_pos_of_pos hden)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hquad hσ.le]

end NLS.ComplexAnalysis
