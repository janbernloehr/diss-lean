import NLS.ZakharovShabat.PeriodicSpectralProductsUniform
import NLS.ComplexAnalysis.EntireLimit

/-!
# Entire periodic spectral products

The actual polynomial cutoffs define a limit at every complex parameter.
The countable-exceptional-set theorem proves that convergence is locally
uniform on the whole plane and that the limit is the entire extension of
the previously constructed off-lattice product.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem countable_freeLattice : freeLattice.Countable := Set.countable_range _

/-- The full periodic spectral product, including its values at the free lattice. -/
def entirePeriodicProduct (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) (ξ η : ℤ → ℂ) : ℂ → ℂ :=
  NLS.ComplexAnalysis.entireSequenceLimit (periodicSpectralPolynomialCutoff hp φ N ξ η)

/-- Literal actual spectral polynomials converge locally uniformly on the whole plane. -/
theorem tendstoLocallyUniformlyOn_entirePeriodicProduct (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff hp φ N ξ η)
      (entirePeriodicProduct hp φ N ξ η) atTop Set.univ :=
  NLS.ComplexAnalysis.tendstoLocallyUniformlyOn_entireSequenceLimit _
    (fun M => differentiableOn_univ.mp (analyticOnNhd_periodicSpectralPolynomialCutoff hp φ N ξ η M).differentiableOn)
    freeLattice countable_freeLattice _
    (tendstoLocallyUniformlyOn_periodicSpectralPolynomialCutoff hp φ N ξ η hξ hη)

/-- The new product is entire in the spectral parameter. -/
theorem analyticOnNhd_entirePeriodicProduct (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (entirePeriodicProduct hp φ N ξ η) Set.univ :=
  ((tendstoLocallyUniformlyOn_entirePeriodicProduct hp φ N ξ η hξ hη).differentiableOn
    (Filter.Eventually.of_forall (fun M =>
      (analyticOnNhd_periodicSpectralPolynomialCutoff hp φ N ξ η M).differentiableOn)) isOpen_univ).analyticOnNhd isOpen_univ

/-- The entire product retains the previously constructed values off the free lattice. -/
theorem entirePeriodicProduct_eq_offLattice (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entirePeriodicProduct hp φ N ξ η z = periodicSpectralProductFormula hp φ N ξ η z :=
  tendsto_nhds_unique ((tendstoLocallyUniformlyOn_entirePeriodicProduct hp φ N ξ η hξ hη).tendsto_at
    (Set.mem_univ z)) ((tendstoLocallyUniformlyOn_periodicSpectralPolynomialCutoff hp φ N ξ η hξ hη).tendsto_at hz)

/-- Derivatives also converge locally uniformly across every free lattice point. -/
theorem tendstoLocallyUniformlyOn_deriv_entirePeriodicProduct (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun M => deriv (periodicSpectralPolynomialCutoff hp φ N ξ η M))
      (deriv (entirePeriodicProduct hp φ N ξ η)) atTop Set.univ :=
  (tendstoLocallyUniformlyOn_entirePeriodicProduct hp φ N ξ η hξ hη).deriv
    (Filter.Eventually.of_forall (fun M =>
      (analyticOnNhd_periodicSpectralPolynomialCutoff hp φ N ξ η M).differentiableOn)) isOpen_univ

/-- Continuity and the old off-lattice values uniquely determine the extension. -/
theorem entirePeriodicProduct_unique (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (f : ℂ → ℂ) (hf : Continuous f)
    (he : freeLatticeᶜ.EqOn f (periodicSpectralProductFormula hp φ N ξ η)) :
    f = entirePeriodicProduct hp φ N ξ η := by
  have hc : Continuous (entirePeriodicProduct hp φ N ξ η) :=
    continuousOn_univ.mp (analyticOnNhd_entirePeriodicProduct hp φ N ξ η hξ hη).continuousOn
  have hs : freeLatticeᶜ ⊆ {z | f z = entirePeriodicProduct hp φ N ξ η z} := fun z hz =>
    (he hz).trans (entirePeriodicProduct_eq_offLattice hp φ N ξ η hξ hη z hz).symm
  have hh := closure_minimal hs (isClosed_eq hf hc)
  funext z
  apply hh
  rw [(countable_freeLattice.dense_compl ℂ).closure_eq]
  exact Set.mem_univ z

end NLS.ZakharovShabat
