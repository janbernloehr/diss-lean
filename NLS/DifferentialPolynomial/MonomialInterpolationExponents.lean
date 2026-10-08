import NLS.DifferentialPolynomial.TwoFactorSplit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field

/-! # The exponents in the monomial interpolation estimate (5.12) -/
noncomputable section
namespace NLS.DifferentialPolynomial

/-- Collecting finite products of interpolated powers retains exact exponents. -/
theorem prod_interpolated_powers {ι : Type*} (S : Finset ι) (ν : ι → ℕ)
    (c α β : ι → ℝ) (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (∏ k ∈ S, (c k*A^(α k)*B^(β k))^ν k) =
      (∏ k ∈ S, c k^ν k)*A^(∑ k ∈ S, α k*ν k)*B^(∑ k ∈ S, β k*ν k) := by
  simp only [mul_pow,Finset.prod_mul_distrib,← Real.rpow_mul_natCast hA.le,
    ← Real.rpow_mul_natCast hB.le,← Real.rpow_sum_of_pos hA,← Real.rpow_sum_of_pos hB]

/-- The two L² factors lower the H^m exponent by exactly 1/m, independently
of which derivative orders were selected. -/
theorem two_factor_interpolation_exponents (m : ℕ) (hm : 1 ≤ m)
    (μ ν : ℕ → ℕ) (i j : ℕ) (hi : i < m) (hj : j < m)
    (hμ : ∀ k ∈ Finset.range m, μ k = ν k+(if k=i then 1 else 0)+(if k=j then 1 else 0))
    (hw : (∑ k ∈ Finset.range m, ((k:ℝ)+1)*μ k) = 2*m+2) :
    (∑ k ∈ Finset.range m, (((k:ℝ)+1/2)/m)*ν k)+(i:ℝ)/m+(j:ℝ)/m =
      2-((∑ k ∈ Finset.range m, (μ k:ℝ))-2)/(2*m) ∧
    (∑ k ∈ Finset.range m, (1-((k:ℝ)+1/2)/m)*ν k)+(1-(i:ℝ)/m)+(1-(j:ℝ)/m) =
      (1+1/(2*m))*((∑ k ∈ Finset.range m, (μ k:ℝ))-2) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN := sum_weight_two_factor_split (Finset.range m) μ ν i j
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hμ (fun _ => 1)
  simp only [one_mul] at hN
  have hW := sum_weight_two_factor_split (Finset.range m) μ ν i j
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hμ (fun k => (k:ℝ)+1)
  rw [hw] at hW
  have hT : (∑ k ∈ Finset.range m, (((k:ℝ)+1/2)/m)*ν k) =
      ((∑ k ∈ Finset.range m, ((k:ℝ)+1)*ν k)-(1/2:ℝ)*(∑ k ∈ Finset.range m, (ν k:ℝ)))/m := by
    rw [Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hα : (∑ k ∈ Finset.range m, (((k:ℝ)+1/2)/m)*ν k)+(i:ℝ)/m+(j:ℝ)/m =
      2-((∑ k ∈ Finset.range m, (μ k:ℝ))-2)/(2*m) := by
    rw [hT]
    field_simp
    nlinarith [hN,hW]
  refine ⟨hα,?_⟩
  simp only [sub_mul,one_mul,Finset.sum_sub_distrib]
  rw [hT]
  field_simp
  nlinarith [hN,hW]

/-- The field-count restrictions force a strictly subquadratic highest-norm
power and the exact Young-conjugate L² power 4m+2. -/
theorem monomial_interpolation_power_range (m : ℕ) (hm : 1 ≤ m) (D : ℝ)
    (hD : 4 ≤ D) (hDm : D ≤ 2*m+2) :
    0 < 2-(D-2)/(2*m) ∧ 2-(D-2)/(2*m) < 2 ∧
      ((1+1/(2*m))*(D-2)) / (1-(2-(D-2)/(2*m))/2) = 4*m+2 := by
  have hm0 : 0 < (m:ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp : 0 < (D-2)/(2*m) := div_pos (by linarith) (by positivity)
  have hle : (D-2)/(2*m) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨by linarith,by linarith,?_⟩
  have he : 1-(2-(D-2)/(2*m))/2 = (D-2)/(4*m) := by ring
  rw [he]
  field_simp [hm0.ne',show D-2 ≠ 0 by linarith]; ring

end NLS.DifferentialPolynomial
