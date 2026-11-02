import NLS.ZakharovShabat.SobolevHierarchySymmetries

/-! # Initial restrictions from the physical NLS hierarchy

The diagonal is complex: it does not impose conjugacy or reality. The general
even-order vanishing below uses Hˢ with 2m ≤ s+1, and does not yet assert the
article's sharper H^m extension or its vector-field identification.
-/
noncomputable section
open Complex NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

/-- Diagonal inclusion into the original period-one NLS source. -/
def hierarchyDiagonal (s : ℕ) : ScalarSobolev s →L[ℂ] SobolevSource s :=
  (ContinuousLinearMap.id ℂ (ScalarSobolev s)).prod
    (ContinuousLinearMap.id ℂ (ScalarSobolev s))

@[simp] theorem hierarchyDiagonal_apply (s : ℕ) (u : ScalarSobolev s) :
    hierarchyDiagonal s u = (u, u) := rfl

/-- Restrict the existing physical Hamiltonian, without renormalizing it. -/
def diagonalNLSHamiltonian (s k : ℕ) (hk : k ≤ s+1) (u : ScalarSobolev s) : ℂ :=
  sobolevNLSHamiltonian s (hierarchyDiagonal s u) k hk

theorem analyticAt_diagonalNLSHamiltonian (s k : ℕ) (hk : k ≤ s+1) (u : ScalarSobolev s) :
    AnalyticAt ℂ (diagonalNLSHamiltonian s k hk) u :=
  (analyticAt_sobolevNLSHamiltonian s k hk (hierarchyDiagonal s u)).comp
    ((hierarchyDiagonal s).analyticAt u)

/-- All even Hamiltonians vanish on the complex diagonal in the currently
available original Sobolev range. This includes the nonsmooth H¹ endpoint m=1. -/
theorem diagonalNLSHamiltonian_even_eq_zero
    (s m : ℕ) (hm : 1 ≤ m) (hms : 2*m ≤ s+1) (u : ScalarSobolev s) :
    diagonalNLSHamiltonian s (2*m) hms u = 0 := by
  have h := sobolevNLSHamiltonian_swap s (2*m-1) (by omega) (u,u)
  have he : (-1 : ℂ)^(2*m-1) = -1 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [show 2*(n+1)-1 = 2*n+1 by omega, pow_succ, pow_mul]
    norm_num
  have hh : sobolevNLSHamiltonian s (u,u) (2*m) hms =
      -sobolevNLSHamiltonian s (u,u) (2*m) hms := by
    simpa only [show 2*m-1+1 = 2*m by omega, he, neg_one_mul] using h
  change sobolevNLSHamiltonian s (u,u) (2*m) hms = 0
  linear_combination (1/2 : ℂ) * hh

/-- The first restriction is the unconjugated period-one mass, so that
the mKdV normalization K₁ is half of this quantity. -/
theorem diagonalNLSHamiltonian_one (s : ℕ) (u : ScalarSobolev s) :
    diagonalNLSHamiltonian s 1 (by omega) u = ∑' j : ℤ, u.val (-j)*u.val j :=
  sobolevNLSHamiltonian_one s (u,u)

/-- Independently specified first physical mKdV Hamiltonian. -/
def classicalMKdVMass (u : ℝ → ℂ) : ℂ :=
  (1/2 : ℂ) * ∫ x in (0 : ℝ)..1, (u x)^2

/-- Independently specified physical mKdV energy K₂. -/
def classicalMKdVEnergy (u : ℝ → ℂ) : ℂ :=
  (1/2 : ℂ) * ∫ x in (0 : ℝ)..1, (deriv u x)^2 + (u x)^4

theorem classicalNLSHamiltonian_one_diagonal (u : ℝ → ℂ) :
    classicalNLSHamiltonian u u 1 = 2 * classicalMKdVMass u := by
  rw [classicalNLSHamiltonian_one]
  simp only [classicalMKdVMass, pow_two]
  ring

/-- Proposition 6 at m=2 on smooth complex period-one functions, with the
physical factor 1/2 and the positive quartic term retained. -/
theorem classicalNLSHamiltonian_three_diagonal (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hpu : Function.Periodic u 1) :
    classicalNLSHamiltonian u u 3 = 2 * classicalMKdVEnergy u := by
  rw [classicalNLSHamiltonian_three u u hu hu hpu hpu]
  have he : (fun x => deriv u x * deriv u x + (u x)^2 * (u x)^2) =
      (fun x => (deriv u x)^2 + (u x)^4) := by funext x; ring
  rw [he]
  simp only [classicalMKdVEnergy]
  ring

end NLS.MKdV
