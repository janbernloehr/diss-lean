import NLS.ZakharovShabat.ParityFiniteApproximation
import NLS.ZakharovShabat.ClassicalDomainPotential
import NLS.ZakharovShabat.CanonicalParityProductsAnalytic

/-!
# The common shifted product for every even Hilbert potential

Density removes the continuous-representative assumption. The two canonical
products agree after their prescribed shifts for arbitrary even-supported
Hilbert coefficients, including potentials with no continuous representative.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ZakharovShabat

/-- Either parity product is continuous in the potential at each spectral parameter. -/
theorem continuous_canonicalParityProduct_potential {p : ENNReal} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (hk : k = 0 ∨ k = 1) (z : ℂ) :
    Continuous (fun φ : pairParitySubspace (p := p) 0 => canonicalParityProduct hp φ.val k z) := by
  have hc : Continuous (fun t : ℂ × pairParitySubspace (p := p) 0 =>
      canonicalParityProduct hp t.2.val k t.1) :=
    (contDiff_canonicalParityProduct_joint hp hp1 k hk).continuous
  exact hc.comp (f := fun ψ : pairParitySubspace (p := p) 0 => (z, ψ))
    (Continuous.prodMk_right z)

/-- Lemma 8.1's shifted-product identity for all even Hilbert potentials. -/
theorem canonicalParity_shifted_eq_hilbert (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalParityProduct (by simp) φ 0 z+2 = canonicalParityProduct (by simp) φ 1 z-2 := by
  have hc (k : ℤ) (hk : k = 0 ∨ k = 1) :=
    continuous_canonicalParityProduct_potential (by simp : (2 : ENNReal) ≠ ⊤) (by norm_num) k hk z
  have he := Continuous.ext_on (dense_domainInclusion_parity (by simp : (2 : ENNReal) ≠ ⊤) 0)
    ((hc 0 (Or.inl rfl)).add continuous_const) ((hc 1 (Or.inr rfl)).sub continuous_const)
    (show EqOn
      (fun ψ : pairParitySubspace (p := 2) 0 => canonicalParityProduct (by simp) ψ.val 0 z+2)
      (fun ψ : pairParitySubspace (p := 2) 0 => canonicalParityProduct (by simp) ψ.val 1 z-2)
      {ψ | ∃ a : Domain 2, domainInclusion a = ψ.val} from by
      rintro ψ ⟨a, ha⟩
      have hpar : a ∈ domainParitySubspace 0 := by
        rw [mem_domainParitySubspace, ha]
        exact ψ.property
      simpa only [ha] using canonicalParity_shifted_eq_domainInclusion a hpar z)
  exact congrFun he ⟨φ, hφ⟩

/-- The odd product differs from the even product by exactly four. -/
theorem canonicalOdd_eq_even_add_four_hilbert (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalParityProduct (by simp) φ 1 z = canonicalParityProduct (by simp) φ 0 z+4 := by
  have h := canonicalParity_shifted_eq_hilbert φ hφ z
  linear_combination -h

/-- The two Hilbert parity products cannot vanish at the same spectral parameter. -/
theorem canonicalParity_not_both_zero_hilbert (φ : PairSpace 2)
    (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    ¬ (canonicalParityProduct (by simp) φ 0 z = 0 ∧ canonicalParityProduct (by simp) φ 1 z = 0) := by
  rintro ⟨he, ho⟩
  have h := canonicalOdd_eq_even_add_four_hilbert φ hφ z
  rw [he, ho] at h
  norm_num at h

end NLS.ZakharovShabat
