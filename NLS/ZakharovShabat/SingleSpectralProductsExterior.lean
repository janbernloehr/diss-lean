import NLS.ZakharovShabat.EntireSingleSpectralProducts
import NLS.ZakharovShabat.RelativeProductsExteriorLimit
import NLS.ZakharovShabat.FreeSineExteriorBounds

/-!
# Single-product zeros and exterior normalization

Off the free lattice, absolute convergence prevents extra zeros. The quotient
by the free derivative tends to one along every separated escaping path.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A convergent single relative product cannot vanish unless a root factor does. -/
theorem spectralRelativeProduct_ne_zero (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice)
    (hroot : ∀ n, ξ n ≠ z) : (∏' n, spectralRelativeFactor ξ z n) ≠ 0 := by
  rw [show spectralRelativeFactor ξ z =
    (fun n => 1 + -((ξ n-(Real.pi : ℂ)*n)/(z-(Real.pi : ℂ)*n)))
      from funext (spectralRelativeFactor_eq ξ z hz)]
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    rw [← spectralRelativeFactor_eq ξ z hz]
    exact (spectralRelativeFactor_ne_zero_iff ξ z hz n).mpr (hroot n)
  · simpa only [norm_neg] using summable_norm_spectralRelativeDisplacement hp ξ hξ z hz

/-- Away from the free lattice, the entire single product has exactly its selected roots. -/
theorem entireSingleSpectralProduct_eq_zero_iff_offLattice (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSingleSpectralProduct ξ z = 0 ↔ ∃ n, ξ n = z := by
  constructor
  · intro he
    by_contra hn
    push Not at hn
    rw [entireSingleSpectralProduct_eq_offLattice hp ξ hξ z hz, singleSpectralProductFormula] at he
    exact mul_ne_zero (mul_ne_zero (by norm_num) (sin_ne_zero_of_notMem_freeLattice hz))
      (spectralRelativeProduct_ne_zero hp ξ hξ z hz hn) he
  · rintro ⟨n, rfl⟩
    exact entireSingleSpectralProduct_root hp ξ hξ n

/-- The free-normalized entire single product equals the relative product off the lattice. -/
theorem entireSingleSpectralProduct_div_free (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSingleSpectralProduct ξ z / (-2*Complex.sin z) = ∏' n, spectralRelativeFactor ξ z n := by
  rw [entireSingleSpectralProduct_eq_offLattice hp ξ hξ z hz, singleSpectralProductFormula]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) (sin_ne_zero_of_notMem_freeLattice hz))

/-- The normalized product tends to one in every direction outside fixed free discs. -/
theorem tendsto_entireSingleSpectralProduct_div_free_of_separated {α : Type*} {l : Filter α}
    (hp : p ≠ ⊤) (ξ : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (z : α → ℂ) (hescape : Tendsto (fun i => ‖z i‖) l atTop)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4)
    (hsep : ∀ i (n : ℤ), r ≤ ‖z i-(Real.pi : ℂ)*n‖) :
    Tendsto (fun i => entireSingleSpectralProduct ξ (z i) / (-2*Complex.sin (z i)))
      l (𝓝 1) := by
  simpa only [entireSingleSpectralProduct_div_free hp ξ hξ _
    (notMem_freeLattice_of_separated hr (hsep _))] using
      tendsto_spectralRelativeProduct_of_separated hp ξ hξ z hescape hr hrπ hsep

end NLS.ZakharovShabat
