import NLS.Articles.KdVPseudomeasures.OriginalHminusOneCharacteristic
import NLS.KdV.HminusOneCharacteristicOrder

/-!
# The full original physical characteristic divisor

These statements retain the article's entire real, mean-zero, physically
period-one H-minus-one domain, including potentials with no endpoint
membership. Every original full-domain algebraic multiplicity is identified
with the analytic order of the physical characteristic at the same energy.
-/
noncomputable section
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

/-- Full physical algebraic multiplicity is the characteristic order on the
article's entire original H-minus-one domain, at every complex energy. -/
theorem analyticOrderAt_originalHillDiscriminant (q : OriginalHminusOnePotential) (z : ℂ) :
    analyticOrderAt (fun w => originalHillDiscriminant q w ^ 2-4) z =
      (singularHillAlgebraicMultiplicity q.val z : ℕ∞) := by
  have he := analyticOrderAt_hillHminusDiscriminant_eq_physicalMultiplicity
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) z
  simpa only [originalHillDiscriminant,periodOneOriginal_originalPeriodOneCoefficients] using he

/-- The physical divisor identity with natural-number analytic orders. -/
theorem analyticOrderNatAt_originalHillDiscriminant (q : OriginalHminusOnePotential) (z : ℂ) :
    analyticOrderNatAt (fun w => originalHillDiscriminant q w ^ 2-4) z =
      singularHillAlgebraicMultiplicity q.val z := by
  have he := congrArg ENat.toNat (analyticOrderAt_originalHillDiscriminant q z)
  simpa only [analyticOrderNatAt,ENat.toNat_natCast] using he

/-- Equality of the entire physical characteristic divisors is exactly
membership in the original full-domain isospectral set. -/
theorem mem_originalIsospectralSet_iff_discriminant_orders
    (q p : OriginalHminusOnePotential) :
    p ∈ originalIsospectralSet q ↔ ∀ z : ℂ,
      analyticOrderAt (fun w => originalHillDiscriminant p w ^ 2-4) z =
        analyticOrderAt (fun w => originalHillDiscriminant q w ^ 2-4) z := by
  change (∀ z : ℂ, singularHillAlgebraicMultiplicity p.val z =
    singularHillAlgebraicMultiplicity q.val z) ↔ _
  simp only [analyticOrderAt_originalHillDiscriminant,Nat.cast_inj]

end NLS.Articles.KdVPseudomeasures
