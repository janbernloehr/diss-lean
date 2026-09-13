import NLS.ZakharovShabat.RelativeSpectralProductsUniform
import NLS.ZakharovShabat.FreeSpectralProductsUniform
import NLS.ZakharovShabat.PerturbedSpectralProducts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Holomorphic limits of the original perturbed cutoffs

Local uniform convergence of the free and relative factors yields local
uniform convergence of the literal normalized symmetric products.
The ambient formula below is used only off the free lattice; extension
across that lattice remains a separate construction.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An ambient formula for the previously constructed off-lattice product. -/
def spectralPairProductFormula (ξ η : ℤ → ℂ) (z : ℂ) : ℂ :=
  ((freeDiscriminant z)^2-4)*spectralRelativePairProduct ξ η z

theorem spectralPairProductFormula_eq (ξ η : ℤ → ℂ) (z : {z : ℂ // z ∉ freeLattice}) :
    spectralPairProductFormula ξ η z.val = spectralPairProductOffLattice ξ η z := rfl

/-- Holomorphy of the product in the spectral parameter, for every fixed displacement pair. -/
theorem analyticOnNhd_spectralPairProductFormula (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (spectralPairProductFormula ξ η) freeLatticeᶜ := by
  have hf : AnalyticOnNhd ℂ (fun z => (freeDiscriminant z)^2-4) freeLatticeᶜ := by
    apply DifferentiableOn.analyticOnNhd _ isClosed_freeLattice.isOpen_compl
    unfold freeDiscriminant
    fun_prop
  exact hf.mul ((differentiableOn_spectralRelativePairProduct hp ξ η hξ hη).analyticOnNhd
    isClosed_freeLattice.isOpen_compl)

/-- The correctly normalized free full product converges locally uniformly on the whole plane. -/
theorem tendstoLocallyUniformlyOn_freePeriodicFullProduct :
    TendstoLocallyUniformlyOn (fun N z => -4*freeSpectralPartialProduct (Real.pi : ℂ) z N)
      (fun z => (freeDiscriminant z)^2-4) atTop Set.univ := by
  have hc : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => (-4 : ℂ))
      (fun _ => (-4 : ℂ)) atTop Set.univ := by
    intro v hv z _
    exact ⟨Set.univ,Filter.univ_mem,Filter.Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
  have h := hc.mul₀ (tendstoLocallyUniformlyOn_freeSpectralPartialProduct (Real.pi : ℂ)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) continuousOn_const (by fun_prop)
  exact h.congr_right (fun z _ => tendsto_nhds_unique (h.tendsto_at (Set.mem_univ z))
    (tendsto_freePeriodicFullProduct z))

/-- The original normalized symmetric products converge locally uniformly off the free lattice. -/
theorem tendstoLocallyUniformlyOn_spectralPairPartialProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => spectralPairPartialProduct ξ η z N)
      (spectralPairProductFormula ξ η) atTop freeLatticeᶜ := by
  have hf : ContinuousOn (fun z => (freeDiscriminant z)^2-4) freeLatticeᶜ := by
    unfold freeDiscriminant
    fun_prop
  have h := (tendstoLocallyUniformlyOn_freePeriodicFullProduct.mono (Set.subset_univ _)).mul₀
    (tendstoLocallyUniformlyOn_spectralRelativePairProduct hp ξ η hξ hη) hf
    (differentiableOn_spectralRelativePairProduct hp ξ η hξ hη).continuousOn
  exact h.congr (fun N z hz => (spectralPairPartialProduct_eq ξ η z hz N).symm)

/-- Uniform convergence on any compact subset, allowing compact sets containing perturbed zeros. -/
theorem tendstoUniformlyOn_spectralPairPartialProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (K : Set ℂ) (hK : IsCompact K) (hKL : K ⊆ freeLatticeᶜ) :
    TendstoUniformlyOn (fun N z => spectralPairPartialProduct ξ η z N)
      (spectralPairProductFormula ξ η) atTop K :=
  ((tendstoLocallyUniformlyOn_iff_forall_isCompact isClosed_freeLattice.isOpen_compl).mp
    (tendstoLocallyUniformlyOn_spectralPairPartialProduct hp ξ η hξ hη)) K hKL hK

end NLS.ZakharovShabat
