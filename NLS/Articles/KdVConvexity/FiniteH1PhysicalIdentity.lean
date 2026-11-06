import NLS.Articles.KdVConvexity.PhysicalHilbertActions
import NLS.Articles.KdVConvexity.SmoothPhysicalHamiltonianIdentity

/-! # The checked smooth physical identity on every native H1 Fourier approximant -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.Articles.KdVConvexity
open NLS.KdV

theorem contourHamiltonian_eq_native_physical_finite_H1
    (R : ℕ+ → BaseActionSpace → ℂ)
    (hR : ∀ q : RealHillWeightedPotential hillH1SpectralWeight, q.val.val 0=0 → ∀ n : ℕ+,
      R n (baseActionInclusion (physicalHilbertActions hillH1SpectralWeight q)) =
        hillHminusRealGapCubicContourMoment (hillWeightedNativeHminusSource hillH1SpectralWeight q.val)
          (hillWeightedNativeHminusSource_real hillH1SpectralWeight q) n)
    (hsum : ∀ a ∈ positiveQuadrant, Summable (fun n => ‖weightedContourTerm R n (baseActionInclusion a)‖))
    (q : RealHillWeightedPotential hillH1SpectralWeight) (hm : q.val.val 0=0)
    (a : ℤ →₀ ℂ) (hq : q.val=WeightedCoeff.ofFinsupp hillH1SpectralWeight.doubleIndex.toWeight 2 a) :
    contourHamiltonian R (physicalHilbertActions hillH1SpectralWeight q) =
      hillNativeH1Hamiltonian q.val-hillH1LinearActionEnergy q := by
  have ha (k : ℤ) : a (-k)=conj (a k) := by
    simpa only [SpectralWeight.toCoeff_apply,hq,WeightedCoeff.ofFinsupp_apply] using q.property k
  have ha0 : a 0=0 := by simpa only [hq,WeightedCoeff.ofFinsupp_apply] using hm
  let Q := hillFinitePhysicalPotential a
  have hreal := real_hillFinitePhysicalPotential a ha
  have hp := periodic_hillFinitePhysicalPotential a
  have hf := contDiff_hillFinitePhysicalPotential a
  have hmean : (∫ x in (0 : ℝ)..1, Q (x : AddCircle (2 : ℝ)))=0 :=
    (mean_hillFinitePhysicalPotential a).trans ha0
  have hQ : hillNativeH1Continuous q.val=Q := by rw [hq,hillNativeH1Continuous_ofFinsupp]
  have hcoeff : hillContinuousCoefficients Q=hillPeriodOneUnitPotential hillH1SpectralWeight q.val := by
    rw [←hQ,hillContinuousCoefficients_hillNativeH1Continuous]
  have hsource : hillWeightedNativeHminusSource hillH1SpectralWeight q.val=
      hillOriginalHminusSource (hillContinuousCoefficients Q) := by
    rw [hcoeff]
    exact hillWeightedNativeHminusSource_eq_original _ _
  have hqQ := hillContinuousCoefficients_mem_even Q hp
  have hrQ := isRealHillPotential_hillContinuousCoefficients_of_conjugate_fourier Q hreal
  have hacts (n : ℕ+) : physicalHilbertActions hillH1SpectralWeight q n=
      hillHminusRealGapContourMoment (hillOriginalHminusSource (hillContinuousCoefficients Q))
        (hillOriginalHminusSource_real _ hrQ) n 0 := by
    simpa only [hsource] using! physicalHilbertActions_intrinsic_Arnold hillH1SpectralWeight q n
  have hcubic (n : ℕ+) : R n (baseActionInclusion (physicalHilbertActions hillH1SpectralWeight q))=
      hillHminusRealGapCubicContourMoment (hillOriginalHminusSource (hillContinuousCoefficients Q))
        (hillOriginalHminusSource_real _ hrQ) n := by
    simpa only [hsource] using! hR q hm n
  have ht := contourHamiltonian_eq_physical_renormalized_smooth Q hqQ hrQ hreal hf hp hmean
    (physicalHilbertActions hillH1SpectralWeight q) R hacts hcubic
    (summable_norm_linear_physicalHilbertActions_H1 q)
    (hsum _ (physicalHilbertActions_mem_positiveQuadrant _ q))
  have henergy : classicalHamiltonian (fun x : ℝ => Q (x : AddCircle (2 : ℝ)))=hillNativeH1Hamiltonian q.val := by
    simpa only [hQ] using (hillNativeH1Hamiltonian_eq_physical_integral q.val).symm
  rw [henergy,←hillH1LinearActionEnergy_eq_physicalHilbertActions] at ht
  exact ht

end NLS.Articles.KdVConvexity
