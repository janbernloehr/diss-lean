import NLS.ZakharovShabat.SingleSpectralProductsUniform
import NLS.ZakharovShabat.EntireSpectralPairProducts

/-!
# Entire single spectral products

Locally uniform convergence off the countable free lattice extends across it.
The construction retains the literal symmetric cutoffs and their derivatives.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The normalized entire product for one complete displaced root sequence. -/
def entireSingleSpectralProduct (ξ : ℤ → ℂ) : ℂ → ℂ :=
  NLS.ComplexAnalysis.entireSequenceLimit (fun N z => singleSpectralPartialProduct ξ z N)

/-- Each finite single product is entire. -/
theorem analyticOnNhd_singleSpectralPartialProduct (ξ : ℤ → ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (fun z => singleSpectralPartialProduct ξ z N) Set.univ := by
  intro z _
  unfold singleSpectralPartialProduct
  exact analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun n _ =>
    (analyticAt_const.sub analyticAt_id).div analyticAt_const (singleSpectralDenominator_ne_zero n)))

/-- The literal cutoffs converge locally uniformly everywhere, including at free centers. -/
theorem tendstoLocallyUniformlyOn_entireSingleSpectralProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N z => singleSpectralPartialProduct ξ z N)
      (entireSingleSpectralProduct ξ) atTop Set.univ :=
  NLS.ComplexAnalysis.tendstoLocallyUniformlyOn_entireSequenceLimit _
    (fun N => differentiableOn_univ.mp (analyticOnNhd_singleSpectralPartialProduct ξ N).differentiableOn)
    freeLattice countable_freeLattice _ (tendstoLocallyUniformlyOn_singleSpectralPartialProduct hp ξ hξ)

/-- The limit is an entire function of the spectral parameter. -/
theorem analyticOnNhd_entireSingleSpectralProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (entireSingleSpectralProduct ξ) Set.univ :=
  ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ).differentiableOn
    (Filter.Eventually.of_forall (fun N => (analyticOnNhd_singleSpectralPartialProduct ξ N).differentiableOn))
    isOpen_univ).analyticOnNhd isOpen_univ

/-- The filled product agrees with its free-relative formula off the lattice. -/
theorem entireSingleSpectralProduct_eq_offLattice (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (z : ℂ) (hz : z ∉ freeLattice) :
    entireSingleSpectralProduct ξ z = singleSpectralProductFormula ξ z :=
  tendsto_nhds_unique ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ).tendsto_at
    (Set.mem_univ _)) ((tendstoLocallyUniformlyOn_singleSpectralPartialProduct hp ξ hξ).tendsto_at hz)

/-- Derivatives of the cutoffs also converge locally uniformly on the whole plane. -/
theorem tendstoLocallyUniformlyOn_deriv_entireSingleSpectralProduct (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun N => deriv (fun z => singleSpectralPartialProduct ξ z N))
      (deriv (entireSingleSpectralProduct ξ)) atTop Set.univ :=
  (tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ).deriv
    (Filter.Eventually.of_forall (fun N => (analyticOnNhd_singleSpectralPartialProduct ξ N).differentiableOn))
    isOpen_univ

/-- At zero displacement the entire product is exactly the free discriminant derivative. -/
theorem entireSingleSpectralProduct_free (z : ℂ) :
    entireSingleSpectralProduct (fun n => (Real.pi : ℂ)*n) z = -2*Complex.sin z := by
  have hd : Memℓp (fun n : ℤ => (Real.pi : ℂ)*n-(Real.pi : ℂ)*n) (2 : ℝ≥0∞) := by
    simpa only [sub_self] using (zero_mem_ℓp' (E := fun _ : ℤ => ℂ) (p := (2 : ℝ≥0∞)))
  exact tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct (by norm_num) _ hd).tendsto_at (Set.mem_univ z))
    (tendsto_singleSpectralPartialProduct_free z)

/-- Every selected root makes all sufficiently large cutoffs vanish. -/
theorem eventually_singleSpectralPartialProduct_eq_zero (ξ : ℤ → ℂ) (n : ℤ) :
    ∀ᶠ N : ℕ in atTop, singleSpectralPartialProduct ξ (ξ n) N = 0 := by
  filter_upwards [eventually_ge_atTop n.natAbs] with N hN
  unfold singleSpectralPartialProduct
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero (show n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) by
    simp only [Finset.mem_Icc]; constructor <;> omega)
  simp [singleSpectralFactor]

/-- Every selected root is a zero of the entire single product, including repeated roots. -/
theorem entireSingleSpectralProduct_root (hp : p ≠ ⊤) (ξ : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p) (n : ℤ) :
    entireSingleSpectralProduct ξ (ξ n) = 0 :=
  tendsto_nhds_unique
    ((tendstoLocallyUniformlyOn_entireSingleSpectralProduct hp ξ hξ).tendsto_at (Set.mem_univ _))
    (tendsto_const_nhds.congr' ((eventually_singleSpectralPartialProduct_eq_zero ξ n).mono
      (fun _ h => h.symm)))

end NLS.ZakharovShabat
