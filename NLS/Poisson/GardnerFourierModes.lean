import NLS.Poisson.GardnerHamiltonianDirection

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Poisson

/-- The literal symmetric pair of raw Fourier modes in H-minus-one. -/
def hminusCosineMode (n : ℤ) : WeightedCoeff (Weight.sobolev (-1)) 2 :=
  WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single n 1+Finsupp.single (-n) 1)

@[simp] theorem hminusCosineMode_apply (n j : ℤ) :
    (hminusCosineMode n).val j = (if n = j then 1 else 0)+(if -n = j then 1 else 0) := by
  simp only [hminusCosineMode,WeightedCoeff.ofFinsupp_apply,Finsupp.add_apply,Finsupp.single_apply]

/-- The Gardner vector of an antisymmetric Fourier functional is the
literal symmetric mode, with the exact original 2*pi*i multiplier. -/
theorem gardnerHamiltonianDirection_of_antisymmetric_fourier
    (n : ℤ) (c : ℂ) (L : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (hL : ∀ h, L h = c*(h.val n-h.val (-n))) :
    gardnerHamiltonianDirection L = -((2*Real.pi : ℂ)*I*n*c) • hminusCosineMode n := by
  apply Subtype.ext
  funext j
  change (2*Real.pi : ℂ)*I*j*(hminusCotangentCLM L).val j = _
  rw [hminusCotangentCLM_apply,hL]
  change (2*Real.pi : ℂ)*I*j*(c*((WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val n-
      (WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-j) 1)).val (-n))) =
    -((2*Real.pi : ℂ)*I*n*c)*(hminusCosineMode n).val j
  have h1 : -j = n ↔ -n = j := by omega
  have h2 : -j = -n ↔ n = j := by omega
  simp only [WeightedCoeff.ofFinsupp_apply,Finsupp.single_apply,h1,h2,hminusCosineMode_apply]
  by_cases hj : n = j
  · subst j
    by_cases hz : -n = n
    · have hn0 : n = 0 := by omega
      subst n
      simp
    · simp only [if_neg hz]
      ring
  · by_cases hm : -n = j
    · subst j
      simp only [if_neg hj,Int.cast_neg]
      ring
    · simp only [if_neg hj,if_neg hm,sub_self,mul_zero,zero_add]

/-- Pairing an antisymmetric Fourier functional against any cotangent
recovers exactly its symmetric-mode value, with the physical Gardner sign. -/
theorem gardnerCotangentBivector_antisymmetric_fourier
    (n : ℤ) (c : ℂ) (L M : WeightedCoeff (Weight.sobolev (-1)) 2 →L[ℂ] ℂ)
    (hL : ∀ h, L h = c*(h.val n-h.val (-n))) :
    gardnerCotangentBivector L M = ((2*Real.pi : ℂ)*I*n*c)*M (hminusCosineMode n) := by
  rw [gardnerCotangentBivector_antisymm,←apply_gardnerHamiltonianDirection M L,
    gardnerHamiltonianDirection_of_antisymmetric_fourier n c L hL,map_smul,smul_eq_mul]
  ring

end NLS.Poisson
