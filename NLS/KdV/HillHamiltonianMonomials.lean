import NLS.KdV.HillSobolevHierarchy
import NLS.DifferentialPolynomial.RealMonomialBounds

/-! # The exact scalar remainder monomial constraints, including at most two highest jets. -/

noncomputable section
set_option autoImplicit false
open MvPolynomial NLS.DifferentialPolynomial
namespace NLS.KdV

theorem jetMultiplicity_hill_weight (m : ℕ) (d : Monomial)
    (hd : ∀ v ∈ d.support, v.2 < m) :
    (∑ k ∈ Finset.range m, (k+2)*jetMultiplicity d k : ℕ) =
      Finsupp.weight hillJetWeight d := by
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, nsmul_eq_mul]
  rw [monomial_sum_lower_jets m d hd]
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  simp only [jetMultiplicity, hillJetWeight, Nat.cast_add]
  ring

theorem hillReducedPolynomial_multiplicity_weight (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (hillReducedPolynomial m hm).support) :
    (∑ k ∈ Finset.range m, (k+2)*jetMultiplicity d k) = 2*m+4 := by
  have ho (v : Jet) (hv : v ∈ d.support) : v.2 < m := by
    have := hillReducedPolynomial_order m hm d hd v hv
    omega
  have hw := hillReducedPolynomial_homogeneous m hm (MvPolynomial.mem_support_iff.mp hd)
  rw [← jetMultiplicity_hill_weight m d ho] at hw
  exact_mod_cast hw

/-- Every scalar remainder monomial has degree between three and m+2. -/
theorem hillReducedPolynomial_field_degree_bounds (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (hillReducedPolynomial m hm).support) :
    3 ≤ ∑ k ∈ Finset.range m, jetMultiplicity d k ∧
      (∑ k ∈ Finset.range m, jetMultiplicity d k) ≤ m+2 := by
  have hw := hillReducedPolynomial_multiplicity_weight m hm d hd
  have hlow : 2*(∑ k ∈ Finset.range m, jetMultiplicity d k) ≤ 2*m+4 := by
    rw [← hw, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => Nat.mul_le_mul_right _ (by omega))
  have hhigh : 2*m+4 ≤ (m+1)*(∑ k ∈ Finset.range m, jetMultiplicity d k) := by
    rw [← hw, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => Nat.mul_le_mul_right _
      (by have := Finset.mem_range.mp hk; omega))
  refine ⟨?_,by omega⟩
  by_contra h
  have hh : (∑ k ∈ Finset.range m, jetMultiplicity d k) ≤ 2 := by omega
  have := Nat.mul_le_mul_left (m+1) hh
  omega

/-- The highest remaining derivative occurs at most quadratically. -/
theorem hillReducedPolynomial_highest_multiplicity (m : ℕ) (hm : 2 ≤ m)
    (d : Monomial) (hd : d ∈ (hillReducedPolynomial m (by omega)).support) :
    jetMultiplicity d (m-1) ≤ 2 := by
  have hw := hillReducedPolynomial_multiplicity_weight m (by omega) d hd
  have hterm : (m-1+2)*jetMultiplicity d (m-1) ≤ 2*m+4 := by
    rw [← hw]
    exact Finset.single_le_sum (f := fun k => (k+2)*jetMultiplicity d k)
      (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  by_contra h
  have ht : 3 ≤ jetMultiplicity d (m-1) := by omega
  have hc := Nat.mul_le_mul_left (m-1+2) ht
  have hml : m-1+2 = m+1 := by omega
  rw [hml] at hterm hc
  nlinarith

end NLS.KdV
