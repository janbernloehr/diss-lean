import NLS.Articles.DNLSEstimates.Primitive

/-!
# Finite-gap Laurent expansion: real-source milestone

This module deliberately keeps the real-type premise visible. Lemma 4 is
printed for all complex finite-gap sources; the present construction of
smooth physical representatives does not discharge that larger domain.
The coefficients below are independently defined physical Hamiltonians,
and the series converges in every exterior complex direction.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Articles.DNLSEstimates

/-- The raw Appendix B Riccati Hamiltonian, correcting H1 to positive mass
as required by Section 2. All higher orders keep the raw integral. -/
def smoothHierarchyHamiltonian (a b : ℝ → ℂ) (k : ℕ) : ℂ :=
  if k = 1 then classicalNLSHamiltonian a b 1
  else ∫ x in (0 : ℝ)..1, a x*nlsRiccatiDensity a b (k-1) x

/-- Coefficient-by-coefficient conversion from the physical library phase
to the signs and powers of 2i in the article's Laurent series. -/
theorem laurent_coefficient (a b : ℝ → ℂ) (k : ℕ) (z : ℂ) :
    I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1) =
      if k = 0 then -smoothHierarchyHamiltonian a b 1/(2*I*z)
      else smoothHierarchyHamiltonian a b (k+1)/(2*I*z)^(k+1) := by
  by_cases hk : k = 0
  · subst k
    simp only [Nat.zero_add, pow_one, ↓reduceIte, smoothHierarchyHamiltonian]
    simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
    ring
  · rw [if_neg hk, smoothHierarchyHamiltonian, if_neg (by omega : k+1 ≠ 1),
      classicalNLSHamiltonian]
    simp only [Nat.add_sub_cancel]
    have hp : I*(-I)^(k+2) = (-I)^(k+1) := by
      rw [show k+2 = (k+1)+1 by omega, pow_succ]
      have hI : I*(-I) = (1 : ℂ) := by norm_num [I_sq]
      calc
        _ = (I*(-I))*(-I)^(k+1) := by ring
        _ = _ := by rw [hI, one_mul]
    rw [← mul_assoc, hp]
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, ← inv_pow, Complex.inv_I]
    ring

/-- The real finite-gap part of Lemma 4, with actual convergent sums and
exterior analyticity, retaining independently constructed physical coefficients.
The complex finite-gap extension remains a separate coverage obligation. -/
theorem lemma_four_real {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : realTypeSourceSubmodule 2)
    (hf : a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ R : ℝ, 0 < R ∧
      AnalyticOnNhd ℂ (fun z => primitive W (z,a.val)) {z : ℂ | R < ‖z‖} ∧
      ∀ z : ℂ, R < ‖z‖ →
        HasSum (fun k : ℕ => I*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num)
          a hf (k+1)/(2*z)^(k+1)) (primitive W (z,a.val)+I*z) := by
  obtain ⟨R,hR,hA,hS⟩ := Q.laurent a hf
  exact ⟨R,hR,hA 0,fun z hz => by simpa [primitive] using hS 0 z hz⟩

/-- The cubic asymptotic used in the proof of Lemma 15, including a uniform
O(|z|^-2) remainder in every complex direction at a real finite-gap source. -/
theorem primitive_cube_asymptotic {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (a : realTypeSourceSubmodule 2)
    (hf : a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    (fun z : ℂ => (primitive W (z,a.val))^3 -
      (I*z^3-(3*I/2)*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) a hf 1*z -
        (3*I/4)*sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) a hf 2 -
        (3*I/8)*(sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) a hf 3 -
          2*(sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) a hf 1)^2)/z))
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2) :=
  Q.cube_isBigO a hf

end NLS.Articles.DNLSEstimates
