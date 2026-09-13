import NLS.ZakharovShabat.EntirePeriodicProducts

/-!
# Entire products for complete perturbed root sequences

Any pair of sequences with summable-power displacements from the free lattice
has a normalized entire product. This supplies a reusable construction for
reindexed parity sequences; no actual spectral counting data are assumed here.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The entire product determined by a complete pair of perturbed root sequences. -/
def entireSpectralPairProduct (ξ η : ℤ → ℂ) : ℂ → ℂ :=
  NLS.ComplexAnalysis.entireSequenceLimit (fun N z => spectralPairPartialProduct ξ η z N)

/-- Every finite normalized product is entire, including at its spectral zeros. -/
theorem analyticOnNhd_spectralPairPartialProduct (ξ η : ℤ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (fun z => spectralPairPartialProduct ξ η z N) Set.univ := by
  intro z _
  unfold spectralPairPartialProduct
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun n _ =>
    analyticOnNhd_spectralPairFactor ξ η n Set.univ z (Set.mem_univ _)))

/-- Complete displaced pairs give locally uniform product convergence on the whole spectral plane. -/
theorem tendstoLocallyUniformlyOn_entireSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => spectralPairPartialProduct ξ η z N)
      (entireSpectralPairProduct ξ η) atTop Set.univ :=
  NLS.ComplexAnalysis.tendstoLocallyUniformlyOn_entireSequenceLimit _
    (fun N => differentiableOn_univ.mp (analyticOnNhd_spectralPairPartialProduct ξ η N).differentiableOn)
    freeLattice countable_freeLattice _ (tendstoLocallyUniformlyOn_spectralPairPartialProduct hp ξ η hξ hη)

/-- The product of complete displaced pairs is entire. -/
theorem analyticOnNhd_entireSpectralPairProduct (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (entireSpectralPairProduct ξ η) Set.univ :=
  ((tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η hξ hη).differentiableOn
    (Filter.Eventually.of_forall (fun N => (analyticOnNhd_spectralPairPartialProduct ξ η N).differentiableOn))
    isOpen_univ).analyticOnNhd isOpen_univ

/-- Away from the free lattice, the entire product retains the normalized free-relative formula. -/
theorem entireSpectralPairProduct_eq_offLattice (hp : p ≠ ⊤) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSpectralPairProduct ξ η z = spectralPairProductFormula ξ η z :=
  tendsto_nhds_unique ((tendstoLocallyUniformlyOn_entireSpectralPairProduct hp ξ η hξ hη).tendsto_at
    (Set.mem_univ _)) ((tendstoLocallyUniformlyOn_spectralPairPartialProduct hp ξ η hξ hη).tendsto_at hz)

end NLS.ZakharovShabat
