import NLS.ZakharovShabat.PerturbedSpectralProductsUniform
import NLS.ZakharovShabat.PeriodicSpectralProductExistence
import NLS.ZakharovShabat.PeriodicSpectralProductCutoffs

/-!
# Holomorphic products for the actual periodic spectrum

The central cluster retains its original algebraic multiplicities. The literal
finite products are polynomials on the whole plane, and converge locally
uniformly off the free lattice to the previously constructed spectral product.
All analyticity in this module concerns the spectral parameter at a fixed
potential; analytic dependence on the potential is not asserted.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Ambient relative formula for the actual product; its analytic domain is off the free lattice. -/
def periodicSpectralProductFormula (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (z : ℂ) : ℂ :=
  (centralPeriodicPolynomial hp φ N z / centralFreePolynomial N z) *
    spectralPairProductFormula (centralFreeCompletion N ξ) (centralFreeCompletion N η) z

theorem periodicSpectralProductFormula_eq (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (z : {z : ℂ // z ∉ freeLattice}) :
    periodicSpectralProductFormula hp φ N ξ η z.val = periodicSpectralProductOffLattice hp φ N ξ η z := rfl

/-- Literal finite spectral products, with only constant normalizations, defined on the entire plane. -/
def periodicSpectralPolynomialCutoff (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (M : ℕ) (z : ℂ) : ℂ :=
  (-4*centralPeriodicPolynomial hp φ N z / centralSpectralNormalization N) *
    ∏ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), spectralPairFactor ξ η z n

/-- The polynomial cutoff equals the earlier relative construction as soon as the center is included. -/
theorem periodicSpectralPolynomialCutoff_eq (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (M : ℕ) (hM : N ≤ M) (z : {z : ℂ // z ∉ freeLattice}) :
    periodicSpectralPolynomialCutoff hp φ N ξ η M z.val = periodicSpectralProductCutoff hp φ N ξ η z M :=
  (periodicSpectralProductCutoff_eq hp φ N ξ η z M hM).symm

/-- Each original normalized factor is entire, even when it has a spectral zero. -/
theorem analyticOnNhd_spectralPairFactor (ξ η : ℤ → ℂ) (n : ℤ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun z => spectralPairFactor ξ η z n) s := by
  have hd : Differentiable ℂ (fun z => spectralPairFactor ξ η z n) := by
    unfold spectralPairFactor
    split_ifs <;> fun_prop
  exact (hd.differentiableOn.analyticOnNhd isOpen_univ).mono (Set.subset_univ _)

/-- Every finite actual spectral cutoff is entire in the spectral parameter. -/
theorem analyticOnNhd_periodicSpectralPolynomialCutoff (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (M : ℕ) :
    AnalyticOnNhd ℂ (periodicSpectralPolynomialCutoff hp φ N ξ η M) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  unfold periodicSpectralPolynomialCutoff centralPeriodicPolynomial
  have hf (n : ℤ) : DifferentiableOn ℂ (fun z => spectralPairFactor ξ η z n) Set.univ :=
    (analyticOnNhd_spectralPairFactor ξ η n Set.univ).differentiableOn
  fun_prop

/-- The actual central correction is holomorphic away from its free normalization zeros. -/
theorem analyticOnNhd_centralPeriodicQuotient (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ) :
    AnalyticOnNhd ℂ (fun z => centralPeriodicPolynomial hp φ N z / centralFreePolynomial N z)
      freeLatticeᶜ := by
  have hc : AnalyticOnNhd ℂ (centralPeriodicPolynomial hp φ N) freeLatticeᶜ := by
    apply DifferentiableOn.analyticOnNhd _ isClosed_freeLattice.isOpen_compl
    unfold centralPeriodicPolynomial
    fun_prop
  have hf : AnalyticOnNhd ℂ (centralFreePolynomial N) freeLatticeᶜ := by
    apply DifferentiableOn.analyticOnNhd _ isClosed_freeLattice.isOpen_compl
    unfold centralFreePolynomial
    fun_prop
  exact hc.div hf (fun z hz => centralFreePolynomial_ne_zero N z hz)

/-- Holomorphy of the actual product for each fixed potential and admissible root pair. -/
theorem analyticOnNhd_periodicSpectralProductFormula (hp : p ≠ ⊤) (φ : PairSpace p) (N : ℕ)
    (ξ η : ℤ → ℂ) (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    AnalyticOnNhd ℂ (periodicSpectralProductFormula hp φ N ξ η) freeLatticeᶜ :=
  (analyticOnNhd_centralPeriodicQuotient hp φ N).mul
    (analyticOnNhd_spectralPairProductFormula hp _ _ (memℓp_centralFreeCompletion N ξ hξ)
      (memℓp_centralFreeCompletion N η hη))

/-- The entire polynomial cutoffs converge locally uniformly off the free lattice. -/
theorem tendstoLocallyUniformlyOn_periodicSpectralPolynomialCutoff (hp : p ≠ ⊤)
    (φ : PairSpace p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff hp φ N ξ η)
      (periodicSpectralProductFormula hp φ N ξ η) atTop freeLatticeᶜ := by
  have hc : TendstoLocallyUniformlyOn (fun _ : ℕ => fun z =>
      centralPeriodicPolynomial hp φ N z / centralFreePolynomial N z)
      (fun z => centralPeriodicPolynomial hp φ N z / centralFreePolynomial N z) atTop freeLatticeᶜ := by
    intro v hv z _
    exact ⟨Set.univ,Filter.univ_mem,Filter.Eventually.of_forall (fun _ _ _ => refl_mem_uniformity hv)⟩
  have h := hc.mul₀ (tendstoLocallyUniformlyOn_spectralPairPartialProduct hp _ _
    (memℓp_centralFreeCompletion N ξ hξ) (memℓp_centralFreeCompletion N η hη))
    (analyticOnNhd_centralPeriodicQuotient hp φ N).continuousOn
    (analyticOnNhd_spectralPairProductFormula hp _ _ (memℓp_centralFreeCompletion N ξ hξ)
      (memℓp_centralFreeCompletion N η hη)).continuousOn
  apply h.congr_inseparable
  filter_upwards [eventually_ge_atTop N] with M hM z hz
  exact .of_eq (periodicSpectralProductCutoff_eq hp φ N ξ η ⟨z,hz⟩ M hM)

/-- Differentiating the actual polynomial cutoffs preserves locally uniform convergence off the lattice. -/
theorem tendstoLocallyUniformlyOn_deriv_periodicSpectralPolynomialCutoff (hp : p ≠ ⊤)
    (φ : PairSpace p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p) :
    TendstoLocallyUniformlyOn (fun M => deriv (periodicSpectralPolynomialCutoff hp φ N ξ η M))
      (deriv (periodicSpectralProductFormula hp φ N ξ η)) atTop freeLatticeᶜ :=
  (tendstoLocallyUniformlyOn_periodicSpectralPolynomialCutoff hp φ N ξ η hξ hη).deriv
    (Filter.Eventually.of_forall (fun M =>
      (analyticOnNhd_periodicSpectralPolynomialCutoff hp φ N ξ η M).differentiableOn.mono
        (Set.subset_univ _))) isClosed_freeLattice.isOpen_compl

/-- The proved spectral data give locally uniform holomorphic products for every finite `p>1` potential.
The neighborhood and central threshold are common; convergence is locally uniform in the spectral
parameter separately for each potential, not uniformly over potentials. -/
theorem exists_uniform_holomorphicPeriodicSpectralProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        ∀ N : ℕ, N₀ ≤ N →
          AnalyticOnNhd ℂ (periodicSpectralProductFormula hp (weightedBaseToPair w ψ) N ξ η) freeLatticeᶜ ∧
          TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w ψ) N ξ η)
            (periodicSpectralProductFormula hp (weightedBaseToPair w ψ) N ξ η) atTop freeLatticeᶜ ∧
          ∀ z : ℂ, z ∉ freeLattice →
            (periodicSpectralProductFormula hp (weightedBaseToPair w ψ) N ξ η z = 0 ↔
              z ∈ periodicSpectrum hp (weightedBaseToPair w ψ)) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hprod⟩ := exists_uniform_periodicSpectralProducts hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hξ,hη,_,h⟩ := hprod ψ hψ
  refine ⟨ξ,η,fun N hN => ⟨analyticOnNhd_periodicSpectralProductFormula hp _ N ξ η hξ hη,
    tendstoLocallyUniformlyOn_periodicSpectralPolynomialCutoff hp _ N ξ η hξ hη,?_⟩⟩
  intro z hz
  exact ((h N hN).2 ⟨z,hz⟩).2

end NLS.ZakharovShabat
