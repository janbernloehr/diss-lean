import NLS.ZakharovShabat.SingleSpectralProducts
import NLS.ZakharovShabat.FreeSpectralProductsUniform
import NLS.ZakharovShabat.RelativeSpectralProductsUniform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Locally uniform single products

The free Euler limit and the absolutely convergent relative product give
locally uniform convergence of the literal symmetric cutoffs off the lattice.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The free single product converges locally uniformly, including all free roots. -/
theorem tendstoLocallyUniformlyOn_singleSpectralPartialProduct_free :
    TendstoLocallyUniformlyOn
      (fun N z => singleSpectralPartialProduct (fun n => (Real.pi : ℂ)*n) z N)
      (fun z => -2*Complex.sin z) atTop Set.univ := by
  have he := (hasProdLocallyUniformlyOn_eulerFactors.comp (t := Set.univ)
    (fun z : ℂ => z/(Real.pi : ℂ)) (fun _ _ => Set.mem_univ _) (by fun_prop)).tendstoLocallyUniformlyOn_finsetRange
  have hc : ContinuousOn (fun z : ℂ => ∏' j : ℕ,
      (1-(z/(Real.pi : ℂ))^2/((j : ℂ)+1)^2)) Set.univ :=
    (continuous_eulerProduct.comp (by fun_prop)).continuousOn
  have hz : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z : ℂ => -2*z)
      (fun z => -2*z) atTop Set.univ := by
    intro v hv z _
    exact ⟨Set.univ,Filter.univ_mem,Filter.Eventually.of_forall
      (fun _ _ _ => refl_mem_uniformity hv)⟩
  have hm := hz.mul₀ he (by fun_prop) hc
  have hp : TendstoLocallyUniformlyOn
      (fun N z => singleSpectralPartialProduct (fun n => (Real.pi : ℂ)*n) z N)
      (fun z => -2*z * ∏' j : ℕ, (1-(z/(Real.pi : ℂ))^2/((j : ℂ)+1)^2))
      atTop Set.univ := by
    apply hm.congr
    intro N z _
    dsimp only [Pi.mul_apply]
    rw [singleSpectralPartialProduct_free_eq]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [div_pow, mul_pow, div_div]
  exact hp.congr_right (fun z _ => tendsto_nhds_unique
    (hp.tendsto_at (Set.mem_univ z)) (tendsto_singleSpectralPartialProduct_free z))

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Literal symmetric cutoffs inherit locally uniform convergence from the unordered relative product. -/
theorem tendstoLocallyUniformlyOn_spectralRelativeProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N : ℕ => fun z =>
      ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralRelativeFactor ξ z n)
      (fun z => ∏' n, spectralRelativeFactor ξ z n) atTop freeLatticeᶜ := by
  intro v hv z hz
  obtain ⟨t,ht,he⟩ := hasProdLocallyUniformlyOn_spectralRelativeFactor hp ξ hξ v hv z hz
  exact ⟨t,ht,Finset.tendsto_Icc_neg.eventually he⟩

/-- The single product formula on the complement of the free lattice. -/
def singleSpectralProductFormula (ξ : ℤ → ℂ) (z : ℂ) : ℂ :=
  -2*Complex.sin z * ∏' n, spectralRelativeFactor ξ z n

/-- Finite-exponent displacements give a locally uniform normalized single product off the lattice. -/
theorem tendstoLocallyUniformlyOn_singleSpectralPartialProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => singleSpectralPartialProduct ξ z N)
      (singleSpectralProductFormula ξ) atTop freeLatticeᶜ := by
  have h := (tendstoLocallyUniformlyOn_singleSpectralPartialProduct_free.mono
    (Set.subset_univ _)).mul₀ (tendstoLocallyUniformlyOn_spectralRelativeProduct hp ξ hξ)
      (by fun_prop) (differentiableOn_spectralRelativeProduct hp ξ hξ).continuousOn
  exact h.congr (fun N z hz => (singleSpectralPartialProduct_eq ξ z hz N).symm)

end NLS.ZakharovShabat
