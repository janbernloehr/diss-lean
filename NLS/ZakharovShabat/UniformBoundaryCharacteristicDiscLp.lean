import NLS.ZakharovShabat.BoundaryCharacteristicDiscLp
import NLS.ZakharovShabat.UniformBoundaryDisplacementBounds
import NLS.ZakharovShabat.CanonicalBoundaryCharacteristic

/-!
# Locally uniform intrinsic boundary characteristic bounds

Uniform complete root-displacement bounds transfer the generic product
majorant to both intrinsic separated characteristics on one potential
neighborhood. The estimates do not depend on a continuous choice of labels.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both intrinsic boundary characteristics share a local ℓᵖ norm bound for
their sine and derivative errors throughout every free disc. -/
theorem exists_uniform_boundaryCharacteristic_disc_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : dirichletSubspace (p := p)) :
    ∃ U : Set (dirichletSubspace (p := p)),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ ψ ∈ U, ∀ b : BoundaryCondition,
        ∃ A : Coeff p, ‖A‖ ≤ K ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/2 →
            ‖b.characteristic hp ψ.val ψ.property z-sin z‖ ≤ ‖A n‖) ∧
          (∀ (n : ℤ) (z : ℂ), ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 →
            ‖deriv (b.characteristic hp ψ.val ψ.property) z-cos z‖ ≤
              (4/Real.pi)*‖A n‖) := by
  obtain ⟨N, _, U, ho, hc, hφ, h0, R, hR, hlabels⟩ :=
    exists_uniform_bounded_boundaryRootLabeling hp hp1 φ
  obtain ⟨K, hK, hproducts⟩ := exists_uniform_displacedBoundaryProduct_majorants hp1 hp hR
  refine ⟨U, ho, hc, hφ, h0, K, hK, fun ψ hψ b => ?_⟩
  obtain ⟨ξ, hξ, hnorm⟩ := hlabels ψ hψ b
  let a : Coeff p := ⟨_, hξ.displacement⟩
  obtain ⟨A, hA, hv, hd⟩ := hproducts a hnorm
  have hroots : ξ = fun n => (Real.pi : ℂ)*n+a n := by
    funext n
    change ξ n = (Real.pi : ℂ)*n+(ξ n-(Real.pi : ℂ)*n)
    ring
  have hproduct : b.characteristic hp ψ.val ψ.property = displacedBoundaryProduct a := by
    rw [← hξ.product_eq_characteristic, displacedBoundaryProduct, hroots]
  refine ⟨A, hA, ?_, ?_⟩
  · intro n z hz
    rw [hproduct]
    exact hv n z hz
  · intro n z hz
    rw [hproduct]
    exact hd n z hz

end NLS.ZakharovShabat
