import NLS.DifferentialPolynomial.MonomialInterpolationExponents

/-! # The scalar KdV two-factor interpolation and Young exponents. -/

noncomputable section
set_option autoImplicit false
namespace NLS.DifferentialPolynomial

/-- Two physical L2 factors give the exact scalar KdV interpolation exponents. -/
theorem scalar_two_factor_interpolation_exponents (m : ℕ) (hm : 1 ≤ m)
    (μ ν : ℕ → ℕ) (i j : ℕ) (hi : i < m) (hj : j < m)
    (hμ : ∀ k ∈ Finset.range m, μ k = ν k+(if k=i then 1 else 0)+(if k=j then 1 else 0))
    (hw : (∑ k ∈ Finset.range m, ((k : ℝ)+2)*μ k) = 2*m+4) :
    (∑ k ∈ Finset.range m, (((k : ℝ)+1/2)/m)*ν k)+(i : ℝ)/m+(j : ℝ)/m =
      2-3*((∑ k ∈ Finset.range m, (μ k : ℝ))-2)/(2*m) ∧
    (∑ k ∈ Finset.range m, (1-((k : ℝ)+1/2)/m)*ν k)+(1-(i : ℝ)/m)+(1-(j : ℝ)/m) =
      (1+3/(2*m))*((∑ k ∈ Finset.range m, (μ k : ℝ))-2) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hN := sum_weight_two_factor_split (Finset.range m) μ ν i j
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hμ (fun _ => 1)
  simp only [one_mul] at hN
  have hW := sum_weight_two_factor_split (Finset.range m) μ ν i j
    (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hμ (fun k => (k : ℝ)+2)
  rw [hw] at hW
  have hT : (∑ k ∈ Finset.range m, (((k : ℝ)+1/2)/m)*ν k) =
      ((∑ k ∈ Finset.range m, ((k : ℝ)+2)*ν k)-(3/2 : ℝ)*(∑ k ∈ Finset.range m, (ν k : ℝ)))/m := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hα : (∑ k ∈ Finset.range m, (((k : ℝ)+1/2)/m)*ν k)+(i : ℝ)/m+(j : ℝ)/m =
      2-3*((∑ k ∈ Finset.range m, (μ k : ℝ))-2)/(2*m) := by
    rw [hT]
    field_simp
    nlinarith [hN,hW]
  refine ⟨hα,?_⟩
  simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
  rw [hT]
  field_simp
  nlinarith [hN,hW]

theorem scalar_monomial_interpolation_power_range (m : ℕ) (hm : 1 ≤ m) (D : ℝ)
    (hD : 3 ≤ D) (hDm : D ≤ m+2) :
    0 < 2-3*(D-2)/(2*m) ∧ 2-3*(D-2)/(2*m) < 2 ∧
      ((1+3/(2*m))*(D-2)) / (1-(2-3*(D-2)/(2*m))/2) = (4*m+6)/3 := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hp : 0 < 3*(D-2)/(2*m) := div_pos (by linarith) (by positivity)
  have hle : 3*(D-2)/(2*m) ≤ 3/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*m)).mpr
    nlinarith
  refine ⟨by linarith,by linarith,?_⟩
  have he : 1-(2-3*(D-2)/(2*m))/2 = 3*(D-2)/(4*m) := by ring
  rw [he]
  field_simp [hm0.ne', show D-2 ≠ 0 by linarith]
  ring

end NLS.DifferentialPolynomial
