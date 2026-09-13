import NLS.ZakharovShabat.SpectralProductsVerticalLimit
import NLS.ZakharovShabat.CanonicalParityProducts
import NLS.Fourier.IntervalKernel

/-!
# Vertical asymptotics of the canonical spectral products

Completed actual spectral pairs transfer the vertical relative-product limit
to the intrinsic potential-only functions. This gives their exact free
normalizations at both vertical ends for every finite exponent greater than
one and every even-supported potential, without a continuous representative.
-/

noncomputable section
open Complex Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_vertical_completePairs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      CompletePeriodicParityPairs hp SpectralWeight.one (unitBaseEquiv.symm φ) N ξ η := by
  obtain ⟨N,_,U,_,_,hU,_,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 SpectralWeight.one
    (unitBaseEquiv.symm φ)
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨N,h _ hU (by rw [he]; exact hφ) N le_rfl⟩

/-- The intrinsic even product has the exact free even normalization at both vertical ends. -/
theorem tendsto_canonicalEven_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (x : ℝ) :
    Tendsto (fun a => canonicalParityProduct hp φ 0 (verticalSpectralPoint x (y a))/
      (freeDiscriminant (verticalSpectralPoint x (y a))-2)) l (𝓝 1) := by
  obtain ⟨N,ξ,η,h⟩ := exists_vertical_completePairs hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  have hc := (h.canonicalParity_eq_products hp1).1
  rw [he] at hc
  rw [hc]
  exact tendsto_evenSpectralPairProduct_div_free_vertical hy hp ξ η h.left_displacement h.right_displacement x

/-- The intrinsic odd product has the exact free odd normalization at both vertical ends. -/
theorem tendsto_canonicalOdd_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (x : ℝ) :
    Tendsto (fun a => canonicalParityProduct hp φ 1 (verticalSpectralPoint x (y a))/
      (freeDiscriminant (verticalSpectralPoint x (y a))+2)) l (𝓝 1) := by
  obtain ⟨N,ξ,η,h⟩ := exists_vertical_completePairs hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  have hc := (h.canonicalParity_eq_products hp1).2
  rw [he] at hc
  rw [hc]
  exact tendsto_oddSpectralPairProduct_div_free_vertical hy hp ξ η h.left_displacement h.right_displacement x

/-- The intrinsic full product is asymptotic to the free characteristic function on either vertical end. -/
theorem tendsto_canonicalPeriodic_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (x : ℝ) :
    Tendsto (fun a => canonicalPeriodicProduct hp φ (verticalSpectralPoint x (y a))/
      ((freeDiscriminant (verticalSpectralPoint x (y a)))^2-4)) l (𝓝 1) := by
  obtain ⟨N,ξ,η,h⟩ := exists_vertical_completePairs hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  have hc := h.fullProduct_eq_canonical
  rw [he] at hc
  rw [← hc]
  exact tendsto_entireSpectralPairProduct_div_free_vertical hy hp ξ η h.left_displacement h.right_displacement x

/-- Both canonical parity normalizations use the same signed free trace formula. -/
theorem tendsto_canonicalParity_div_free_vertical {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto (fun a => |y a|) l atTop) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (hr : r = 0 ∨ r = 1) (x : ℝ) :
    Tendsto (fun a => canonicalParityProduct hp φ r (verticalSpectralPoint x (y a))/
      (freeDiscriminant (verticalSpectralPoint x (y a))-2*wave r 1)) l (𝓝 1) := by
  rcases hr with rfl | rfl
  · simpa only [wave_zero,mul_one] using tendsto_canonicalEven_div_free_vertical hy hp hp1 φ hφ x
  · have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
    simpa only [hw,mul_neg_one,sub_neg_eq_add] using tendsto_canonicalOdd_div_free_vertical hy hp hp1 φ hφ x

end NLS.ZakharovShabat
