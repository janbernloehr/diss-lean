import NLS.ZakharovShabat.FloquetQuadratic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Reciprocal stable and unstable Floquet roots off the unit circle -/
noncomputable section
set_option autoImplicit false
open Complex Matrix
namespace NLS.ZakharovShabat

/-- Every unimodular quadratic has a complex root. -/
theorem exists_root_floquet_quadratic (d : ℂ) :
    ∃ μ : ℂ, μ ^ 2 - d * μ + 1 = 0 := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq (d^2-4) (by norm_num : 0 < 2)
  refine ⟨(d+s)/2,?_⟩
  linear_combination hs / 4

/-- The other root is the reciprocal, with neither root equal to zero. -/
theorem inverse_root_floquet_quadratic (d μ : ℂ) (h : μ^2-d*μ+1 = 0) :
    μ ≠ 0 ∧ μ⁻¹^2-d*μ⁻¹+1 = 0 := by
  have hμ : μ ≠ 0 := by intro hz; simp [hz] at h
  refine ⟨hμ,?_⟩
  field_simp
  linear_combination h

/-- Without a unit-circle root, a unimodular quadratic has a stable root
and its unstable reciprocal. -/
theorem exists_stable_unstable_floquet_roots (d : ℂ)
    (hunit : ¬ ∃ μ : ℂ, ‖μ‖ = 1 ∧ μ^2-d*μ+1 = 0) :
    ∃ μ ν : ℂ, μ * ν = 1 ∧ 0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧
      μ^2-d*μ+1 = 0 ∧ ν^2-d*ν+1 = 0 := by
  obtain ⟨a,ha⟩ := exists_root_floquet_quadratic d
  obtain ⟨ha0,hai⟩ := inverse_root_floquet_quadratic d a ha
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hn : ‖a‖ ≠ 1 := fun h => hunit ⟨a,h,ha⟩
  have hmul : ‖a‖ * ‖a⁻¹‖ = 1 := by rw [← norm_mul,mul_inv_cancel₀ ha0,norm_one]
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · refine ⟨a,a⁻¹,mul_inv_cancel₀ ha0,hnorm,hlt,?_,ha,hai⟩
    nlinarith [norm_nonneg a⁻¹]
  · refine ⟨a⁻¹,a,inv_mul_cancel₀ ha0,norm_pos_iff.mpr (inv_ne_zero ha0),?_,hgt,hai,ha⟩
    nlinarith [norm_nonneg a⁻¹]

/-- Actual unimodular matrices with no unit characteristic root have
stable and unstable reciprocal characteristic roots. -/
theorem exists_stable_unstable_characteristic_roots
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det = 1)
    (hunit : ¬ ∃ μ : ℂ, ‖μ‖ = 1 ∧ (M-μ • 1).det = 0) :
    ∃ μ ν : ℂ, μ * ν = 1 ∧ 0 < ‖μ‖ ∧ ‖μ‖ < 1 ∧ 1 < ‖ν‖ ∧
      (M-μ • 1).det = 0 ∧ (M-ν • 1).det = 0 := by
  simp_rw [det_sub_smul_one_eq_floquet_quadratic M hM] at hunit ⊢
  exact exists_stable_unstable_floquet_roots M.trace hunit

end NLS.ZakharovShabat
