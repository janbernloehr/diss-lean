import NLS.ZakharovShabat.ExponentCanonicalProducts
import NLS.ZakharovShabat.ExponentParityDensity
import NLS.ZakharovShabat.HilbertDiscriminant

/-!
# The shifted-product identity at every finite exponent greater than one

Below the Hilbert exponent, exact inclusion compatibility transfers the
Hilbert identity directly. Above it, the Hilbert image is dense within the
even subspace, and continuity of both canonical products passes to the limit.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected two parity products define one discriminant for every finite p>1. -/
theorem canonicalParity_shifted_eq_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalParityProduct hp φ 0 z+2 = canonicalParityProduct hp φ 1 z-2 := by
  rcases le_total p 2 with hp2 | h2p
  · rw [canonicalParityProduct_exponent hp (by simp) hp2,
      canonicalParityProduct_exponent hp (by simp) hp2]
    exact canonicalParity_shifted_eq_hilbert (pairExponentInclusion hp2 φ)
      ((pairExponentInclusion_mem_parity_iff hp2 φ 0).mpr hφ) z
  · have hc (k : ℤ) (hk : k = 0 ∨ k = 1) :=
      continuous_canonicalParityProduct_potential hp hp1 k hk z
    have he := Continuous.ext_on (dense_pairExponentInclusion_parity hp h2p 0)
      ((hc 0 (Or.inl rfl)).add continuous_const) ((hc 1 (Or.inr rfl)).sub continuous_const)
      (show EqOn
        (fun ψ : pairParitySubspace (p := p) 0 => canonicalParityProduct hp ψ.val 0 z+2)
        (fun ψ : pairParitySubspace (p := p) 0 => canonicalParityProduct hp ψ.val 1 z-2)
        {ψ | ∃ a : PairSpace 2, pairExponentInclusion h2p a = ψ.val} from by
        rintro ψ ⟨a, ha⟩
        have hpar : a ∈ pairParitySubspace 0 :=
          (pairExponentInclusion_mem_parity_iff h2p a 0).mp (ha ▸ ψ.property)
        dsimp only
        rw [← ha, ← canonicalParityProduct_exponent (by simp) hp h2p,
          ← canonicalParityProduct_exponent (by simp) hp h2p]
        exact canonicalParity_shifted_eq_hilbert a hpar z)
    exact congrFun he ⟨φ, hφ⟩

/-- The intrinsic discriminant is also the odd product minus two throughout the finite-p domain. -/
theorem canonicalDiscriminant_eq_odd_sub_two_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalDiscriminant hp φ z = canonicalParityProduct hp φ 1 z-2 :=
  canonicalParity_shifted_eq_finite hp hp1 φ hφ z

/-- The odd product is the intrinsic discriminant plus two for all finite p>1. -/
theorem canonicalOdd_eq_discriminant_add_two_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalParityProduct hp φ 1 z = canonicalDiscriminant hp φ z+2 := by
  rw [canonicalDiscriminant_eq_odd_sub_two_finite hp hp1 φ hφ]
  ring

/-- The full product is the squared discriminant minus four throughout the finite-p even space. -/
theorem canonicalPeriodic_eq_discriminant_sq_sub_four_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    canonicalPeriodicProduct hp φ z = (canonicalDiscriminant hp φ z)^2-4 := by
  rw [← canonicalParityProducts_mul hp hp1 φ hφ z,
    canonicalEven_eq_discriminant_sub_two, canonicalOdd_eq_discriminant_add_two_finite hp hp1 φ hφ]
  ring

/-- No finite-p even potential has a common zero of the two parity products. -/
theorem canonicalParity_not_both_zero_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    ¬ (canonicalParityProduct hp φ 0 z = 0 ∧ canonicalParityProduct hp φ 1 z = 0) := by
  rintro ⟨he, ho⟩
  have h := canonicalParity_shifted_eq_finite hp hp1 φ hφ z
  rw [he, ho] at h
  norm_num at h

end NLS.ZakharovShabat
