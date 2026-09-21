import NLS.ZakharovShabat.CentralBoundaryPolynomials

/-!
# Intrinsic Dirichlet and Neumann characteristic functions
The potential and boundary condition alone determine the function, as the
limit of normalized central polynomials. Every complete boundary labeling
has this same entire product, independently of its cutoff and central ordering.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Section 9 characteristic function constructed directly from the actual central spectra. -/
def BoundaryCondition.characteristic (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (z : ℂ) : ℂ :=
  limUnder atTop (fun N => b.normalizedCentralPolynomial hp φ hφ N z)

namespace BoundaryRootLabeling
variable {b : BoundaryCondition} {hp : p ≠ ⊤} {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- Intrinsic polynomials converge locally uniformly to the product of any complete labeling. -/
theorem tendsto_normalizedCentral (h : BoundaryRootLabeling b hp φ hφ N ξ) :
    TendstoLocallyUniformlyOn (b.normalizedCentralPolynomial hp φ hφ)
      (boundaryCharacteristicProduct ξ) atTop univ := by
  apply (tendstoLocallyUniformlyOn_boundaryCharacteristicProduct hp ξ h.displacement).congr_inseparable
  filter_upwards [eventually_ge_atTop N] with K hK z _
  exact .of_eq (h.cutoff_eq_normalizedCentral K hK z)

/-- Every complete spectral product equals the characteristic function of the original operator. -/
theorem product_eq_characteristic (h : BoundaryRootLabeling b hp φ hφ N ξ) :
    boundaryCharacteristicProduct ξ = b.characteristic hp φ hφ := by
  funext z
  exact ((h.tendsto_normalizedCentral.tendsto_at (mem_univ z)).limUnder_eq).symm

/-- Neither central ordering nor cutoff choices affect the full boundary product. -/
theorem product_eq {M : ℕ} {η : ℤ → ℂ} (h : BoundaryRootLabeling b hp φ hφ N ξ)
    (hη : BoundaryRootLabeling b hp φ hφ M η) : boundaryCharacteristicProduct ξ = boundaryCharacteristicProduct η :=
  h.product_eq_characteristic.trans hη.product_eq_characteristic.symm

end BoundaryRootLabeling

namespace BoundaryCondition

/-- Every actual finite-p boundary characteristic is entire, is the local uniform polynomial limit,
and has exactly the original spectrum as zero set. -/
theorem characteristic_spec (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    AnalyticOnNhd ℂ (b.characteristic hp φ hφ) univ ∧
      TendstoLocallyUniformlyOn (b.normalizedCentralPolynomial hp φ hφ)
        (b.characteristic hp φ hφ) atTop univ ∧
      ∀ z : ℂ, b.characteristic hp φ hφ z = 0 ↔ z ∈ b.spectrum hp φ hφ := by
  obtain ⟨N,_,ξ,h⟩ := exists_complete_boundaryRootLabeling hp hp1 ⟨φ,hφ⟩ b
  rw [← h.product_eq_characteristic]
  exact ⟨analyticOnNhd_boundaryCharacteristicProduct hp ξ h.displacement,
    h.tendsto_normalizedCentral,h.characteristic_eq_zero_iff⟩

/-- The intrinsic boundary characteristic is entire in the spectral parameter. -/
theorem analyticOnNhd_characteristic (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) : AnalyticOnNhd ℂ (b.characteristic hp φ hφ) univ :=
  (b.characteristic_spec hp hp1 φ hφ).1

/-- The intrinsic central approximants converge locally uniformly to the boundary characteristic. -/
theorem tendstoLocallyUniformlyOn_characteristic (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    TendstoLocallyUniformlyOn (b.normalizedCentralPolynomial hp φ hφ)
      (b.characteristic hp φ hφ) atTop univ :=
  (b.characteristic_spec hp hp1 φ hφ).2.1

/-- First spectral derivatives are also limits of the intrinsic finite approximants. -/
theorem tendstoLocallyUniformlyOn_deriv_characteristic (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) :
    TendstoLocallyUniformlyOn (fun N => deriv (b.normalizedCentralPolynomial hp φ hφ N))
      (deriv (b.characteristic hp φ hφ)) atTop univ :=
  (b.tendstoLocallyUniformlyOn_characteristic hp hp1 φ hφ).deriv
    (Filter.Eventually.of_forall (fun N =>
      (b.analyticOnNhd_normalizedCentralPolynomial hp φ hφ N).differentiableOn)) isOpen_univ

/-- The intrinsic function vanishes precisely at actual boundary eigenvalues. -/
theorem characteristic_eq_zero_iff (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    b.characteristic hp φ hφ z = 0 ↔ z ∈ b.spectrum hp φ hφ :=
  (b.characteristic_spec hp hp1 φ hφ).2.2 z

end BoundaryCondition
end NLS.ZakharovShabat
