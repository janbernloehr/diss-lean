import NLS.ZakharovShabat.PeriodicPolynomialMultiplicity
import NLS.ComplexAnalysis.IsolatedOrderStability

/-!
# The entire product's original spectral multiplicities

Each point has a disc containing no other spectral value. Rouché stability
passes the exact finite-cutoff orders to the entire limit. The order is finite
and equals the original generalized-eigenspace algebraic multiplicity.
-/

noncomputable section
open Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every parameter admits a closed disc with no other original spectral value. -/
theorem exists_periodicSpectrum_isolating_closedBall (hp : p ≠ ⊤) (φ : PairSpace p) (z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ closedBall z r, a ∈ periodicSpectrum hp φ → a = z := by
  by_cases hz : z ∈ periodicSpectrum hp φ
  · obtain ⟨U,hU,hUz⟩ := (discreteTopology_subtype_iff'.mp (discreteTopology_periodicSpectrum hp φ)) z hz
    have hzU : z ∈ U := by
      have hm : z ∈ U ∩ periodicSpectrum hp φ := by rw [hUz]; exact Set.mem_singleton z
      exact hm.1
    obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hzU)
    refine ⟨r,hr,fun a ha hspec => ?_⟩
    have hmem : a ∈ U ∩ periodicSpectrum hp φ := ⟨hball ha,hspec⟩
    rw [hUz] at hmem
    exact hmem
  · obtain ⟨r,hr,hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      ((isClosed_periodicSpectrum hp φ).isOpen_compl.mem_nhds hz)
    exact ⟨r,hr,fun a ha hspec => (hball ha hspec).elim⟩

/-- Natural analytic orders of the entire product are the actual spectral algebraic multiplicities. -/
theorem analyticOrderNatAt_entirePeriodicProduct (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ) :
    analyticOrderNatAt (entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η) z =
      periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z := by
  obtain ⟨r,hr0,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp (weightedBaseToPair w φ) z
  have hFz (M : ℕ) (a : ℂ) (ha : a ∈ closedBall z r)
      (ha0 : periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M a = 0) : a = z := by
    apply hiso a ha
    by_contra hnot
    exact periodicSpectralPolynomialCutoff_ne_zero hp w φ N ξ η hr M a hnot ha0
  have hgz (a : ℂ) (ha : a ∈ closedBall z r)
      (ha0 : entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η a = 0) : a = z :=
    hiso a ha ((entirePeriodicProduct_eq_zero_iff hp w φ N ξ η hξ hη hc hr a).mp ha0)
  have hconv := tendstoLocallyUniformlyOn_entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η hξ hη
  have hstab := NLS.ComplexAnalysis.eventually_analyticOrderNatAt_eq_of_isolated _ _ z r hr0
    (fun M => (analyticOnNhd_periodicSpectralPolynomialCutoff hp _ N ξ η M).mono (Set.subset_univ _))
    ((analyticOnNhd_entirePeriodicProduct hp _ N ξ η hξ hη).mono (Set.subset_univ _)) hFz hgz
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (Set.subset_univ _)))
  have hpoly := eventually_polynomialCutoff_order_eq_multiplicity hp w φ N ξ η hc hr z
  obtain ⟨M,hM,hpM⟩ := (hstab.and hpoly).exists
  have hn := congrArg ENat.toNat hpM
  have hn' : analyticOrderNatAt (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M) z =
      periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z := by
    simpa only [analyticOrderNatAt, ENat.toNat_natCast] using hn
  exact hM.symm.trans hn'

/-- Extended analytic order is finite and equals the original multiplicity, including at free lattice points. -/
theorem analyticOrderAt_entirePeriodicProduct (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) (z : ℂ) :
    analyticOrderAt (entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η) z =
      (periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z : ℕ∞) := by
  obtain ⟨r,hr0,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp (weightedBaseToPair w φ) z
  have hfin := NLS.ComplexAnalysis.analyticOrderAt_ne_top_of_isolated _ z r hr0
    ((analyticOnNhd_entirePeriodicProduct hp _ N ξ η hξ hη).mono (Set.subset_univ _))
    (fun a ha ha0 => hiso a ha ((entirePeriodicProduct_eq_zero_iff hp w φ N ξ η hξ hη hc hr a).mp ha0))
  rw [← Nat.cast_analyticOrderNatAt hfin, analyticOrderNatAt_entirePeriodicProduct hp w φ N ξ η hξ hη hc hr z]

/-- Actual spectral data give entire products with exactly the original multiplicities for every finite `p>1` potential. -/
theorem exists_uniform_entirePeriodicProducts_with_orders (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        ∀ N : ℕ, N₀ ≤ N →
          AnalyticOnNhd ℂ (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η) Set.univ ∧
          TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w ψ) N ξ η)
            (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η) atTop Set.univ ∧
          ∀ z : ℂ,
            analyticOrderAt (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η) z =
              (periodicAlgebraicMultiplicity hp (weightedBaseToPair w ψ) z : ℕ∞) ∧
            (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η z = 0 ↔
              z ∈ periodicSpectrum hp (weightedBaseToPair w ψ)) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hprod⟩ := exists_uniform_periodicSpectralProducts hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hξ,hη,hr,h⟩ := hprod ψ hψ
  refine ⟨ξ,η,fun N hN => ⟨analyticOnNhd_entirePeriodicProduct hp _ N ξ η hξ hη,
    tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ N ξ η hξ hη,?_⟩⟩
  intro z
  have hpairs : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w ψ n (ξ n) (η n) :=
    fun n hn => hr n (by omega)
  exact ⟨analyticOrderAt_entirePeriodicProduct hp w ψ N ξ η hξ hη (h N hN).1 hpairs z,
    entirePeriodicProduct_eq_zero_iff hp w ψ N ξ η hξ hη (h N hN).1 hpairs z⟩

end NLS.ZakharovShabat
