import NLS.ZakharovShabat.SpectralProductsExteriorLimit
import NLS.ZakharovShabat.CanonicalParityProducts
import NLS.Fourier.IntervalKernel

/-!
# Canonical product normalization outside fixed free spectral discs

Completed actual pairs transfer the exterior product limits to the intrinsic
potential-only functions for every finite exponent greater than one. Both
spectral coordinates may vary; only escape and fixed lattice separation are
required.
-/

noncomputable section
open Complex Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem exists_exterior_completePairs (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) :
    ∃ N : ℕ, ∃ ξ η : ℤ → ℂ,
      CompletePeriodicParityPairs hp SpectralWeight.one (unitBaseEquiv.symm φ) N ξ η := by
  obtain ⟨N,_,U,_,_,hU,_,h⟩ := exists_uniform_completePeriodicParityPairs hp hp1 SpectralWeight.one
    (unitBaseEquiv.symm φ)
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  exact ⟨N,h _ hU (by rw [he]; exact hφ) N le_rfl⟩

/-- The intrinsic even product has the exact free even normalization outside the fixed discs. -/
theorem tendsto_canonicalEven_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : α → ℂ)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hrπ : r₀ ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r₀ ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun a => canonicalParityProduct hp φ 0 (z a)/
      (freeDiscriminant (z a)-2)) l (𝓝 1) := by
  obtain ⟨N,ξ,η,h⟩ := exists_exterior_completePairs hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  have hc := (h.canonicalParity_eq_products hp1).1
  rw [he] at hc
  rw [hc]
  exact tendsto_evenSpectralPairProduct_div_free_of_separated hp ξ η h.left_displacement h.right_displacement z hescape hr₀ hrπ hsep

/-- The intrinsic odd product has the exact free odd normalization outside the fixed discs. -/
theorem tendsto_canonicalOdd_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : α → ℂ)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hrπ : r₀ ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r₀ ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun a => canonicalParityProduct hp φ 1 (z a)/
      (freeDiscriminant (z a)+2)) l (𝓝 1) := by
  obtain ⟨N,ξ,η,h⟩ := exists_exterior_completePairs hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  have hc := (h.canonicalParity_eq_products hp1).2
  rw [he] at hc
  rw [hc]
  exact tendsto_oddSpectralPairProduct_div_free_of_separated hp ξ η h.left_displacement h.right_displacement z hescape hr₀ hrπ hsep

/-- The intrinsic full product is asymptotic to the free characteristic function outside the fixed discs. -/
theorem tendsto_canonicalPeriodic_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : α → ℂ)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hrπ : r₀ ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r₀ ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun a => canonicalPeriodicProduct hp φ (z a)/
      ((freeDiscriminant (z a))^2-4)) l (𝓝 1) := by
  obtain ⟨N,ξ,η,h⟩ := exists_exterior_completePairs hp hp1 φ hφ
  have he : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm φ) = φ := by
    rw [← unitBaseEquiv_eq,ContinuousLinearEquiv.apply_symm_apply]
  have hc := h.fullProduct_eq_canonical
  rw [he] at hc
  rw [← hc]
  exact tendsto_entireSpectralPairProduct_div_free_of_separated hp ξ η h.left_displacement h.right_displacement z hescape hr₀ hrπ hsep

/-- Both canonical parity normalizations use the same signed free trace formula. -/
theorem tendsto_canonicalParity_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (r : ℤ) (hr : r = 0 ∨ r = 1) (z : α → ℂ)
    (hescape : Tendsto (fun i => ‖z i‖) l atTop) {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hrπ : r₀ ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r₀ ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun a => canonicalParityProduct hp φ r (z a)/
      (freeDiscriminant (z a)-2*wave r 1)) l (𝓝 1) := by
  rcases hr with rfl | rfl
  · simpa only [wave_zero,mul_one] using tendsto_canonicalEven_div_free_of_separated hp hp1 φ hφ z hescape hr₀ hrπ hsep
  · have hw : wave 1 1 = -1 := by simpa using wave_odd_at_one 0
    simpa only [hw,mul_neg_one,sub_neg_eq_add] using tendsto_canonicalOdd_div_free_of_separated hp hp1 φ hφ z hescape hr₀ hrπ hsep

end NLS.ZakharovShabat
