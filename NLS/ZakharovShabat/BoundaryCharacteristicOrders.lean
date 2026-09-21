import NLS.ZakharovShabat.CanonicalBoundaryCharacteristic
import NLS.ComplexAnalysis.FiniteProductOrders
import NLS.ComplexAnalysis.IsolatedOrderStability

/-!
# Original algebraic multiplicities of the boundary characteristic
Every fixed point eventually lies in the central box. The corresponding
finite polynomial orders are the actual operator multiplicities, and Rouché
stability passes these orders to the intrinsic entire characteristic.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Every fixed spectral parameter eventually lies in every central box. -/
theorem eventually_mem_centralSpectralBox (z : ℂ) : ∀ᶠ N : ℕ in atTop, z ∈ centralSpectralBox N := by
  obtain ⟨K,hK⟩ := exists_nat_gt (max (|z.re|/Real.pi) |z.im|)
  have hre : |z.re| < (K : ℝ)*Real.pi :=
    (div_lt_iff₀ Real.pi_pos).mp (lt_of_le_of_lt (le_max_left _ _) hK)
  have him : |z.im| ≤ (K : ℝ) := (lt_of_le_of_lt (le_max_right _ _) hK).le
  have hz : z ∈ centralSpectralBox K := ⟨by linarith [Real.pi_pos],him⟩
  filter_upwards [eventually_ge_atTop K] with N hN
  exact centralSpectralBox_mono hN hz

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace BoundaryCondition

/-- The central intrinsic approximant has precisely the original orders of its enclosed roots. -/
theorem analyticOrderAt_normalizedCentralPolynomial (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ) :
    analyticOrderAt (b.normalizedCentralPolynomial hp φ hφ N) z =
      if z ∈ b.centralSpectrum hp φ hφ N then (b.algebraicMultiplicity hp φ hφ z : ℕ∞) else 0 := by
  unfold normalizedCentralPolynomial
  rw [NLS.ComplexAnalysis.analyticOrderAt_div_const (fun t => -b.centralPolynomial hp φ hφ N t) z
    (∏ n ∈ Finset.Icc (-(N : ℤ)) N, singleSpectralDenominator n)
    (Finset.prod_ne_zero_iff.mpr (fun n _ => singleSpectralDenominator_ne_zero n))
    ((b.analyticOnNhd_centralPolynomial hp φ hφ N z (mem_univ z)).neg)]
  change analyticOrderAt (-(b.centralPolynomial hp φ hφ N)) z = _
  rw [analyticOrderAt_neg]
  exact NLS.ComplexAnalysis.analyticOrderAt_rootPolynomial _ _ z

/-- Normalized central polynomials introduce no zeros outside the actual boundary spectrum. -/
theorem normalizedCentralPolynomial_ne_zero (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ)
    (hz : z ∉ b.spectrum hp φ hφ) : b.normalizedCentralPolynomial hp φ hφ N z ≠ 0 := by
  apply div_ne_zero
  · apply neg_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    apply pow_ne_zero
    intro he
    have he' := sub_eq_zero.mp he
    subst a
    exact hz ((b.mem_centralSpectrum hp φ hφ N z).mp ha).1
  · exact Finset.prod_ne_zero_iff.mpr (fun n _ => singleSpectralDenominator_ne_zero n)

/-- At every parameter, sufficiently large intrinsic cutoffs have exactly its original multiplicity. -/
theorem eventually_normalizedCentralPolynomial_order (b : BoundaryCondition) (hp : p ≠ ⊤)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) : ∀ᶠ N : ℕ in atTop,
    analyticOrderAt (b.normalizedCentralPolynomial hp φ hφ N) z =
      (b.algebraicMultiplicity hp φ hφ z : ℕ∞) := by
  filter_upwards [eventually_mem_centralSpectralBox z] with N hN
  rw [b.analyticOrderAt_normalizedCentralPolynomial]
  by_cases hz : z ∈ b.spectrum hp φ hφ
  · rw [if_pos ((b.mem_centralSpectrum hp φ hφ N z).mpr ⟨hz,hN⟩)]
  · have hn : z ∉ b.centralSpectrum hp φ hφ N := fun hn => hz ((b.mem_centralSpectrum hp φ hφ N z).mp hn).1
    rw [if_neg hn,(b.algebraicMultiplicity_eq_zero_iff hp φ hφ z).mpr (by simpa [spectrum] using hz),Nat.cast_zero]

/-- The natural analytic order is exactly the original boundary algebraic multiplicity. -/
theorem analyticOrderNatAt_characteristic (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    analyticOrderNatAt (b.characteristic hp φ hφ) z = b.algebraicMultiplicity hp φ hφ z := by
  obtain ⟨r,hr,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp φ z
  have hFz (N : ℕ) (a : ℂ) (ha : a ∈ closedBall z r)
      (ha0 : b.normalizedCentralPolynomial hp φ hφ N a = 0) : a = z := by
    apply hiso a ha
    by_contra hnot
    exact b.normalizedCentralPolynomial_ne_zero hp φ hφ N a
      (fun hspec => hnot (b.spectrum_subset_periodic hp φ hφ hspec)) ha0
  have hgz (a : ℂ) (ha : a ∈ closedBall z r) (ha0 : b.characteristic hp φ hφ a = 0) : a = z :=
    hiso a ha (b.spectrum_subset_periodic hp φ hφ ((b.characteristic_eq_zero_iff hp hp1 φ hφ a).mp ha0))
  have hconv := b.tendstoLocallyUniformlyOn_characteristic hp hp1 φ hφ
  have hstab := NLS.ComplexAnalysis.eventually_analyticOrderNatAt_eq_of_isolated _ _ z r hr
    (fun N => (b.analyticOnNhd_normalizedCentralPolynomial hp φ hφ N).mono (subset_univ _))
    ((b.analyticOnNhd_characteristic hp hp1 φ hφ).mono (subset_univ _)) hFz hgz
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_sphere z r)).mp
      (hconv.mono (subset_univ _)))
  obtain ⟨N,hN,hpoly⟩ := (hstab.and (b.eventually_normalizedCentralPolynomial_order hp φ hφ z)).exists
  have hn := congrArg ENat.toNat hpoly
  have hn' : analyticOrderNatAt (b.normalizedCentralPolynomial hp φ hφ N) z =
      b.algebraicMultiplicity hp φ hφ z := by
    simpa only [analyticOrderNatAt,ENat.toNat_natCast] using hn
  exact hN.symm.trans hn'

/-- Extended order is finite and equals the original multiplicity, including at repeated central roots. -/
theorem analyticOrderAt_characteristic (b : BoundaryCondition) (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace) (z : ℂ) :
    analyticOrderAt (b.characteristic hp φ hφ) z = (b.algebraicMultiplicity hp φ hφ z : ℕ∞) := by
  obtain ⟨r,hr,hiso⟩ := exists_periodicSpectrum_isolating_closedBall hp φ z
  have hfin := NLS.ComplexAnalysis.analyticOrderAt_ne_top_of_isolated _ z r hr
    ((b.analyticOnNhd_characteristic hp hp1 φ hφ).mono (subset_univ _))
    (fun a ha ha0 => hiso a ha (b.spectrum_subset_periodic hp φ hφ
      ((b.characteristic_eq_zero_iff hp hp1 φ hφ a).mp ha0)))
  rw [← Nat.cast_analyticOrderNatAt hfin,b.analyticOrderNatAt_characteristic hp hp1 φ hφ z]

end BoundaryCondition

/-- Every complete boundary sequence gives the same exact original analytic orders. -/
theorem BoundaryRootLabeling.product_analyticOrderAt {b : BoundaryCondition} {hp : p ≠ ⊤}
    {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}
    (h : BoundaryRootLabeling b hp φ hφ N ξ) (hp1 : 1 < p) (z : ℂ) :
    analyticOrderAt (boundaryCharacteristicProduct ξ) z = (b.algebraicMultiplicity hp φ hφ z : ℕ∞) := by
  rw [h.product_eq_characteristic]
  exact b.analyticOrderAt_characteristic hp hp1 φ hφ z

end NLS.ZakharovShabat
