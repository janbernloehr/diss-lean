import NLS.ZakharovShabat.BoundaryRootSpaces
import NLS.ZakharovShabat.FreeMultiplicity
import NLS.ZakharovShabat.DiskMultiplicity
import NLS.ZakharovShabat.CentralSpectrum

/-!
# Free Dirichlet and Neumann multiplicities

The free rank-one boundary counts used in Chapter 1, Theorem 1.4 follow from
nonzero boundary modes and the splitting of periodic algebraic multiplicity two.
Both free full root spaces are already attained at level one, so there are no
longer free boundary Jordan chains.
-/

open scoped ENNReal
noncomputable section
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed free mode for the chosen boundary condition. -/
def mode : BoundaryCondition → ℤ → Domain p
  | .dirichlet => dirichletMode
  | .neumann => neumannMode

variable (b : BoundaryCondition)

theorem mode_mem (n : ℤ) : mode (p := p) b n ∈ domain b := by
  cases b
  · exact dirichletMode_mem n
  · exact neumannMode_mem n

theorem domainInclusion_mode_ne_zero (n : ℤ) : domainInclusion (mode (p := p) b n) ≠ 0 := by
  cases b
  · exact domainInclusion_dirichletMode_ne_zero n
  · exact domainInclusion_neumannMode_ne_zero n

theorem freeOperator_mode (n : ℤ) :
    freeOperator (mode (p := p) b n) = ((Real.pi : ℂ) * n) • domainInclusion (mode b n) := by
  cases b
  · exact freeOperator_dirichletMode n
  · exact freeOperator_neumannMode n

theorem free_index_mem_spectrum (hp : p ≠ ⊤) (n : ℤ) :
    (Real.pi : ℂ) * n ∈ spectrum (p := p) b hp 0 (by simp) := by
  rw [mem_spectrum_iff_exists_eigenvector]
  refine ⟨mode b n, mode_mem b n, ?_, ?_⟩
  · intro h
    exact domainInclusion_mode_ne_zero b n (by rw [h, map_zero])
  · rw [operator_zero]
    exact freeOperator_mode b n

/-- The free boundary spectra are precisely the signed Fourier lattice. -/
theorem spectrum_zero (hp : p ≠ ⊤) : spectrum (p := p) b hp 0 (by simp) = freeLattice := by
  ext z
  constructor
  · intro hz
    by_contra hn
    exact hz (mem_resolventSet_of_periodic b hp 0 (by simp) z
      (mem_resolventSet_zero_of_notMem hp z hn))
  · rintro ⟨n, rfl⟩
    exact free_index_mem_spectrum b hp n

/-- Every free boundary eigenvalue has algebraic multiplicity one. -/
theorem algebraicMultiplicity_zero (hp : p ≠ ⊤) (n : ℤ) :
    algebraicMultiplicity (p := p) b hp 0 (by simp) ((Real.pi : ℂ) * n) = 1 := by
  have hD := (algebraicMultiplicity_pos_iff .dirichlet hp 0 (by simp) _).mpr
    (free_index_mem_spectrum (p := p) .dirichlet hp n)
  have hN := (algebraicMultiplicity_pos_iff .neumann hp 0 (by simp) _).mpr
    (free_index_mem_spectrum (p := p) .neumann hp n)
  have hs := periodicAlgebraicMultiplicity_eq_boundary_sum (p := p) hp 0 (by simp) ((Real.pi : ℂ) * n)
  rw [periodicAlgebraicMultiplicity_zero] at hs
  cases b <;> omega

/-- Free boundary generalized eigenvectors are ordinary eigenvectors. -/
theorem rootSpace_one_zero_eq_top (hp : p ≠ ⊤) (n : ℤ) :
    rootSpace (p := p) b hp 0 (by simp) ((Real.pi : ℂ) * n) 1 =
      rootSpaceTop b hp 0 (by simp) ((Real.pi : ℂ) * n) := by
  ext x
  rw [mem_rootSpace_iff_periodic, mem_rootSpaceTop_iff_periodic, periodicRootSpace_one_zero_eq_top]

/-- The free quarter-pi contour has rank one in each boundary summand. -/
theorem finrank_free_contour_boundary (hp : p ≠ ⊤) (n : ℤ) :
    Module.finrank ℂ ↥((resolventCircleIntegral (p := p) hp 0
      ((Real.pi : ℂ) * n) (Real.pi / 4)).range ⊓ space b) = 1 := by
  have hr : 0 < Real.pi / 4 := by positivity
  have hc : Metric.sphere ((Real.pi : ℂ) * n) (Real.pi / 4) ⊆
      ZakharovShabat.resolventSet (p := p) hp 0 :=
    sphere_subset_resolventSet_of_smallPotential hp 0 n hr le_rfl (by simpa using hr)
  rw [range_resolventCircleIntegral hp 0 _ _ hr.le hc,
    enclosedPeriodicSpectrum_zero hp n hr (by linarith [Real.pi_pos])]
  have hs : periodicClusterSpace (p := p) hp 0 {((Real.pi : ℂ) * n)} =
      periodicRootSpaceTop hp 0 ((Real.pi : ℂ) * n) := by simp [periodicClusterSpace]
  rw [hs, finrank_periodicRootSpaceTop_inf b hp 0 (by simp), algebraicMultiplicity_zero]

/-- The free central algebraic count is `2N+1` for each boundary condition. -/
theorem sum_central_multiplicity_zero (hp : p ≠ ⊤) (N : ℕ) :
    (∑ z ∈ centralPeriodicSpectrum (p := p) hp 0 N, algebraicMultiplicity b hp 0 (by simp) z) =
      2 * N + 1 := by
  classical
  rw [centralPeriodicSpectrum_zero, Finset.sum_image]
  · simp only [algebraicMultiplicity_zero, Finset.sum_const, smul_eq_mul, mul_one, Int.card_Icc]
    omega
  · intro a _ c _ h
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact_mod_cast mul_left_cancel₀ hπ h

end NLS.ZakharovShabat.BoundaryCondition
