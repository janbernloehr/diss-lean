import NLS.ZakharovShabat.UniformBoundaryRootLabeling
import NLS.ZakharovShabat.CriticalPointProducts

/-!
# Entire characteristic products for complete boundary sequences
Section 9 uses prefactor minus one. Its free value is sin(z), whereas the
existing derivative product has prefactor two and free value -2 sin(z).
Complete actual boundary sequences yield entire products with exactly the
boundary spectrum as zero set. Parameter analyticity and independence
from central label choices are separate steps.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal Section 9 cutoff, with prefactor minus one. -/
def boundaryCharacteristicPartialProduct (ξ : ℤ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  -(∏ n ∈ Finset.Icc (-(N : ℤ)) N, singleSpectralFactor ξ z n)

/-- The entire characteristic product with the source's boundary normalization. -/
def boundaryCharacteristicProduct (ξ : ℤ → ℂ) (z : ℂ) : ℂ :=
  (-1/2 : ℂ)*entireSingleSpectralProduct ξ z

/-- The boundary and derivative product cutoffs differ by exactly the normalization factor. -/
theorem boundaryCharacteristicPartialProduct_eq (ξ : ℤ → ℂ) (z : ℂ) (N : ℕ) :
    boundaryCharacteristicPartialProduct ξ z N = (-1/2 : ℂ)*singleSpectralPartialProduct ξ z N := by
  unfold boundaryCharacteristicPartialProduct singleSpectralPartialProduct
  ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite-exponent displacements give an entire boundary characteristic product. -/
theorem analyticOnNhd_boundaryCharacteristicProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (boundaryCharacteristicProduct ξ) univ :=
  analyticOnNhd_const.mul (analyticOnNhd_entireSingleSpectralProduct hp ξ hξ)

/-- The source-normalized cutoffs converge locally uniformly on the whole spectral plane. -/
theorem tendstoLocallyUniformlyOn_boundaryCharacteristicProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => boundaryCharacteristicPartialProduct ξ z N)
      (boundaryCharacteristicProduct ξ) atTop univ := by
  have hc : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => (-1/2 : ℂ))
      (fun _ : ℂ => (-1/2 : ℂ)) atTop univ := by
    intro v hv z _
    exact ⟨univ,Filter.univ_mem,Filter.Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
  have h := hc.mul₀ (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ)
    continuous_const.continuousOn (analyticOnNhd_entireSingleSpectralProduct hp ξ hξ).continuousOn
  change TendstoLocallyUniformlyOn (fun N z => (-1/2 : ℂ)*singleSpectralPartialProduct ξ z N)
    (boundaryCharacteristicProduct ξ) atTop univ at h
  simpa only [boundaryCharacteristicPartialProduct_eq] using h

/-- At a closed root set the characteristic product has no additional zeros. -/
theorem boundaryCharacteristicProduct_eq_zero_iff (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (hc : IsClosed (range ξ)) (z : ℂ) :
    boundaryCharacteristicProduct ξ z = 0 ↔ ∃ n : ℤ, ξ n = z := by
  rw [boundaryCharacteristicProduct,mul_eq_zero]
  norm_num only [show (-1/2 : ℂ) ≠ 0 by norm_num,false_or]
  exact entireSingleSpectralProduct_eq_zero_iff hp ξ hξ hc z

/-- The free characteristic product has exactly the Section 9 sine normalization. -/
theorem boundaryCharacteristicProduct_free (z : ℂ) :
    boundaryCharacteristicProduct (fun n => (Real.pi : ℂ)*n) z = Complex.sin z := by
  rw [boundaryCharacteristicProduct,entireSingleSpectralProduct_free]
  ring

/-- A complete actual boundary labeling gives precisely the original boundary spectrum as zero set. -/
theorem BoundaryRootLabeling.characteristic_eq_zero_iff {b : BoundaryCondition} {hp : p ≠ ⊤}
    {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}
    (h : BoundaryRootLabeling b hp φ hφ N ξ) (z : ℂ) :
    boundaryCharacteristicProduct ξ z = 0 ↔ z ∈ b.spectrum hp φ hφ :=
  (boundaryCharacteristicProduct_eq_zero_iff hp ξ h.displacement h.isClosed_range z).trans (h.exhaustive z).symm

/-- Every reflected potential has an entire actual boundary product with the source normalization. -/
theorem exists_entire_boundaryCharacteristicProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : dirichletSubspace (p := p)) (b : BoundaryCondition) :
    ∃ N : ℕ, ∃ ξ : ℤ → ℂ, BoundaryRootLabeling b hp φ.val φ.property N ξ ∧
      AnalyticOnNhd ℂ (boundaryCharacteristicProduct ξ) univ ∧
      (∀ z, boundaryCharacteristicProduct ξ z = 0 ↔ z ∈ b.spectrum hp φ.val φ.property) ∧
      TendstoLocallyUniformlyOn (fun M z => boundaryCharacteristicPartialProduct ξ z M)
        (boundaryCharacteristicProduct ξ) atTop univ := by
  obtain ⟨N,_,ξ,h⟩ := exists_complete_boundaryRootLabeling hp hp1 φ b
  exact ⟨N,ξ,h,analyticOnNhd_boundaryCharacteristicProduct hp ξ h.displacement,h.characteristic_eq_zero_iff,
    tendstoLocallyUniformlyOn_boundaryCharacteristicProduct hp ξ h.displacement⟩

/-- The same entire characteristic products exist for the original period-one potential realization. -/
theorem exists_entire_periodOneBoundaryCharacteristicProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (b : BoundaryCondition) :
    ∃ N : ℕ, ∃ ξ : ℤ → ℂ, BoundaryRootLabeling b hp (periodOneBoundaryPotential hp hp1 φ).val
        (periodOneBoundaryPotential hp hp1 φ).property N ξ ∧
      AnalyticOnNhd ℂ (boundaryCharacteristicProduct ξ) univ ∧
      (∀ z, boundaryCharacteristicProduct ξ z = 0 ↔
        z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val (periodOneBoundaryPotential hp hp1 φ).property) ∧
      TendstoLocallyUniformlyOn (fun M z => boundaryCharacteristicPartialProduct ξ z M)
        (boundaryCharacteristicProduct ξ) atTop univ :=
  exists_entire_boundaryCharacteristicProduct hp hp1 (periodOneBoundaryPotential hp hp1 φ) b

end NLS.ZakharovShabat
