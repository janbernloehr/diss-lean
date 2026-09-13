import NLS.ZakharovShabat.CentralPolynomialAnalytic
import NLS.ZakharovShabat.EntirePeriodicProductOrders

/-!
# The intrinsic full periodic product

The normalized central polynomials define a product from the actual potential
alone. They are eventually identical to every admissible spectral-pair cutoff,
so their limit is the entire product already constructed. Joint analyticity of
the finite approximants is proved; joint locally uniform convergence remains
separate from the fixed-potential convergence established here.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The full periodic product defined directly from the actual central spectra. -/
def canonicalPeriodicProduct (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) : ℂ :=
  limUnder atTop (fun N => normalizedCentralPeriodicPolynomial hp φ N z)

/-- The intrinsic approximants converge to every admissible entire-product construction. -/
theorem tendstoLocallyUniformlyOn_normalizedCentralPolynomials (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    TendstoLocallyUniformlyOn (normalizedCentralPeriodicPolynomial hp (weightedBaseToPair w φ))
      (entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η) atTop Set.univ := by
  apply (tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ N ξ η hξ hη).congr_inseparable
  filter_upwards [eventually_ge_atTop N] with M hM z _
  exact .of_eq (congrFun (periodicSpectralPolynomialCutoff_eq_normalizedCentral hp w φ N M hM ξ η hc hr) z)

/-- The intrinsic product equals every admissible weighted spectral construction. -/
theorem canonicalPeriodicProduct_eq_entire (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    canonicalPeriodicProduct hp (weightedBaseToPair w φ) =
      entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η := by
  funext z
  exact ((tendstoLocallyUniformlyOn_normalizedCentralPolynomials hp w φ N ξ η hξ hη hc hr).tendsto_at
    (Set.mem_univ z)).limUnder_eq

/-- Every actual finite `p>1` potential has the intrinsic entire product with exact original orders.
The intrinsic normalized polynomials converge locally uniformly in the spectral parameter. -/
theorem canonicalPeriodicProduct_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    AnalyticOnNhd ℂ (canonicalPeriodicProduct hp φ) Set.univ ∧
      TendstoLocallyUniformlyOn (normalizedCentralPeriodicPolynomial hp φ)
        (canonicalPeriodicProduct hp φ) atTop Set.univ ∧
      ∀ z : ℂ, analyticOrderAt (canonicalPeriodicProduct hp φ) z =
        (periodicAlgebraicMultiplicity hp φ z : ℕ∞) ∧
        (canonicalPeriodicProduct hp φ z = 0 ↔ z ∈ periodicSpectrum hp φ) := by
  let ψ := unitBaseEquiv.symm φ
  have he : weightedBaseToPair SpectralWeight.one ψ = φ := by
    rw [← unitBaseEquiv_eq]
    exact unitBaseEquiv.apply_symm_apply φ
  obtain ⟨N,_,U,_,_,hψ,_,hdata⟩ := exists_uniform_periodicSpectralProducts hp hp1 SpectralWeight.one ψ
  obtain ⟨ξ,η,hξ,hη,hr,h⟩ := hdata ψ hψ
  have hc := (h N le_rfl).1
  have hcan := canonicalPeriodicProduct_eq_entire hp SpectralWeight.one ψ N ξ η hξ hη hc hr
  have ha := analyticOnNhd_entirePeriodicProduct hp (weightedBaseToPair SpectralWeight.one ψ) N ξ η hξ hη
  have ht := tendstoLocallyUniformlyOn_normalizedCentralPolynomials hp SpectralWeight.one ψ N ξ η hξ hη hc hr
  rw [← hcan, he] at ha ht
  refine ⟨ha,ht,?_⟩
  intro z
  have ho := analyticOrderAt_entirePeriodicProduct hp SpectralWeight.one ψ N ξ η hξ hη hc hr z
  have hz := entirePeriodicProduct_eq_zero_iff hp SpectralWeight.one ψ N ξ η hξ hη hc hr z
  rw [← hcan, he] at ho hz
  exact ⟨ho,hz⟩

/-- The potential-only construction is entire in the spectral parameter. -/
theorem analyticOnNhd_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    AnalyticOnNhd ℂ (canonicalPeriodicProduct hp φ) Set.univ :=
  (canonicalPeriodicProduct_spec hp hp1 φ).1

/-- The intrinsic finite polynomials converge locally uniformly on the whole spectral plane. -/
theorem tendstoLocallyUniformlyOn_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    TendstoLocallyUniformlyOn (normalizedCentralPeriodicPolynomial hp φ)
      (canonicalPeriodicProduct hp φ) atTop Set.univ :=
  (canonicalPeriodicProduct_spec hp hp1 φ).2.1

/-- Spectral derivatives of the intrinsic approximants converge to the canonical derivative. -/
theorem tendstoLocallyUniformlyOn_deriv_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) :
    TendstoLocallyUniformlyOn (fun N => deriv (normalizedCentralPeriodicPolynomial hp φ N))
      (deriv (canonicalPeriodicProduct hp φ)) atTop Set.univ :=
  (tendstoLocallyUniformlyOn_canonicalPeriodicProduct hp hp1 φ).deriv
    (Filter.Eventually.of_forall (fun N =>
      (analyticOnNhd_normalizedCentralPeriodicPolynomial hp φ N).differentiableOn)) isOpen_univ

/-- The canonical product retains the original finite analytic orders at every parameter. -/
theorem analyticOrderAt_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (z : ℂ) :
    analyticOrderAt (canonicalPeriodicProduct hp φ) z = (periodicAlgebraicMultiplicity hp φ z : ℕ∞) :=
  ((canonicalPeriodicProduct_spec hp hp1 φ).2.2 z).1

/-- The canonical product's zero set is exactly the original periodic spectrum. -/
theorem canonicalPeriodicProduct_eq_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p) (z : ℂ) :
    canonicalPeriodicProduct hp φ z = 0 ↔ z ∈ periodicSpectrum hp φ :=
  ((canonicalPeriodicProduct_spec hp hp1 φ).2.2 z).2

end NLS.ZakharovShabat
