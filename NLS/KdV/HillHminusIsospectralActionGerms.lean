import NLS.KdV.HillHminusRelativeActionMatching
import NLS.KdV.HillIsospectralData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV

/-- The canonical energy product, including its physical sign, depends
only on the actual entire discriminant. -/
theorem hillEnergyCanonicalRootProduct_eq_of_discriminant_eq
    (q p : RealPeriodOneHillPotential)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) :
    hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 =
      hillEnergyCanonicalRootProduct p.val p.property.1 p.property.2 := by
  funext z
  simp only [hillEnergyCanonicalRootProduct,hillEnergyRootProduct,hillEnergyRootFactor,
    hillRealLabels_eq_of_discriminant_eq q p hΔ]

/-- Changing the original reference along a true isospectral set leaves
the entire relative-root function unchanged, not merely its square. -/
theorem hillHminusRelativeRoot_eq_of_discriminant_eq
    (q p : RealPeriodOneHillPotential)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) :
    hillHminusRelativeRoot q.val q.property.1 q.property.2 =
      hillHminusRelativeRoot p.val p.property.1 p.property.2 := by
  funext t
  simp only [hillHminusRelativeRoot,hillHminusRelativeRootRatio,
    hillEnergyCanonicalRootProduct_eq_of_discriminant_eq q p hΔ,hillL2Radicand,hΔ]

/-- The same literal fixed-circle action function is obtained from every
original isospectral reference, even when those references are not L2-close. -/
theorem hillHminusRelativeAction_eq_of_discriminant_eq
    (q p : RealPeriodOneHillPotential)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
      hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) (n : ℕ) :
    hillHminusRelativeAction q.val q.property.1 q.property.2 n =
      hillHminusRelativeAction p.val p.property.1 p.property.2 n := by
  funext a
  simp only [hillHminusRelativeAction,hillRealGapCenter,hillRealGapHalfLength,hillRealGapCollar,
    hillHminusRelativeActionIntegrand,hillHminusRelativeRoot_eq_of_discriminant_eq q p hΔ,
    hillRealLabels_eq_of_discriminant_eq q p hΔ]

/-- One H-minus-one analytic action germ retains the ORIGINAL physical L2
germ at EVERY original isospectral point in its domain. No assumption of
L2 closeness to the reference is required at those points. -/
theorem exists_hillHminusRelativeAction_isospectral_physical_germs
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ hillOriginalHminusSource q.val ∈ U ∧
      AnalyticOnNhd ℂ (hillHminusRelativeAction q.val q.property.1 q.property.2 n) U ∧
      ∀ p : RealPeriodOneHillPotential,
        (∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
          hillL2Discriminant (SpectralWeight.one.toCoeff p.val) E) →
        ∃ V : Set RealPeriodOneHillPotential, IsOpen V ∧ p ∈ V ∧
          ∀ r ∈ V, hillHminusRelativeAction q.val q.property.1 q.property.2 n
              (hillOriginalHminusSource r.val) =
            (hillRealGapIntegral r.val r.property.1 r.property.2 n 0 : ℂ) := by
  obtain ⟨U,hU,hqU,hA,_⟩ := exists_hillHminusRelativeAction_analytic_neighborhood
    q.val q.property.1 q.property.2 n hn
  refine ⟨U,hU,hqU,hA,?_⟩
  intro p hΔ
  obtain ⟨V,hV,hpV,hmatch⟩ := exists_hillHminusRelativeAction_original_matching p n hn
  refine ⟨V,hV,hpV,?_⟩
  intro r hr
  rw [hillHminusRelativeAction_eq_of_discriminant_eq q p hΔ n]
  exact hmatch r hr

end NLS.KdV
