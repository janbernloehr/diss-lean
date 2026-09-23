import NLS.ZakharovShabat.SingleSpectralProductsExterior
import NLS.ZakharovShabat.CanonicalBoundaryCharacteristic
import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ZakharovShabat.CanonicalExteriorLowerBounds

/-! # Exterior normalization of the actual boundary characteristics

The complete signed boundary roots have summable displacements, so their
source-normalized entire product approaches the free sine away from fixed
free-root discs. This applies to each intrinsic boundary characteristic,
the original period-one source, and both actual starred source problems.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full source-normalized single-root product has free sine ratio one on every escaping separated path. -/
theorem tendsto_boundaryCharacteristicProduct_div_sin_of_separated
    {α : Type*} {l : Filter α} (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n - (Real.pi : ℂ) * n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => boundaryCharacteristicProduct ξ (z i) / sin (z i)) l (𝓝 1) := by
  have h := tendsto_entireSingleSpectralProduct_div_free_of_separated hp ξ hξ
    z hescape hr hrπ hsep
  have he (i : α) : boundaryCharacteristicProduct ξ (z i) / sin (z i) =
      entireSingleSpectralProduct ξ (z i) / (-2 * sin (z i)) := by
    have hs : sin (z i) ≠ 0 := sin_ne_zero_of_notMem_freeLattice
      (notMem_freeLattice_of_separated hr (hsep i))
    unfold boundaryCharacteristicProduct
    field_simp
  simpa only [he] using h

/-- Every intrinsic Dirichlet or Neumann characteristic has the exact free sine exterior normalization. -/
theorem BoundaryCondition.tendsto_characteristic_div_sin_of_separated
    {α : Type*} {l : Filter α} (b : BoundaryCondition) (hp : p ≠ ⊤)
    (hp1 : 1 < p) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => b.characteristic hp φ hφ (z i) / sin (z i)) l (𝓝 1) := by
  obtain ⟨N, _, ξ, hξ⟩ := exists_complete_boundaryRootLabeling hp hp1 ⟨φ, hφ⟩ b
  rw [← hξ.product_eq_characteristic]
  exact tendsto_boundaryCharacteristicProduct_div_sin_of_separated hp ξ hξ.displacement
    z hescape hr hrπ hsep

/-- Far enough outside fixed free-root discs, every intrinsic boundary characteristic has at least half the free sine magnitude. -/
theorem BoundaryCondition.exists_threshold_half_le_norm_characteristic_div_sin
    (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ →
      (∀ n : ℤ, r ≤ ‖z - (Real.pi : ℂ) * n‖) →
        (1 : ℝ) / 2 ≤ ‖b.characteristic hp φ hφ z / sin z‖ := by
  let S := {z : ℂ // ∀ n : ℤ, r ≤ ‖z - (Real.pi : ℂ) * n‖}
  obtain ⟨R, hR⟩ := exists_threshold_half_le_norm (fun z : S => ‖z.val‖)
    (fun z : S => b.characteristic hp φ hφ z.val / sin z.val)
    (b.tendsto_characteristic_div_sin_of_separated hp hp1 φ hφ
      (fun z : S => z.val) tendsto_comap hr hrπ (fun z => z.property))
  exact ⟨R, fun z hz hsep => hR ⟨z, hsep⟩ hz⟩

/-- Both ordinary source boundary products have free sine exterior normalization. -/
theorem tendsto_periodOneBoundaryCharacteristic_div_sin_of_separated
    {α : Type*} {l : Filter α} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => periodOneBoundaryCharacteristic hp hp1 b φ (z i) / sin (z i))
      l (𝓝 1) :=
  b.tendsto_characteristic_div_sin_of_separated hp hp1 _ _ z hescape hr hrπ hsep

/-- Both actual starred source products have free sine exterior normalization. -/
theorem tendsto_auxiliaryPeriodOneCharacteristic_div_sin_of_separated
    {α : Type*} {l : Filter α} (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi / 4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i - (Real.pi : ℂ) * n‖) :
    Tendsto (fun i => auxiliaryPeriodOneCharacteristic hp hp1 b φ (z i) / sin (z i))
      l (𝓝 1) := by
  rw [auxiliaryPeriodOneCharacteristic_eq_sourcePhase]
  exact tendsto_periodOneBoundaryCharacteristic_div_sin_of_separated hp hp1 b
    (sourcePhase φ) z hescape hr hrπ hsep

end NLS.ZakharovShabat
