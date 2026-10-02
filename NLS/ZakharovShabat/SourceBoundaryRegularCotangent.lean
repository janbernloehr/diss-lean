import NLS.Poisson.RegularSourceCotangentIntegral
import NLS.ZakharovShabat.SourceBoundaryExponentDifferential

/-! # Regular moving boundary cotangents at every finite exponent

Below two the full moving root and multiplier differentials restrict
from the Hilbert exponent. Above two their continuous cotangents
already have Hilbert coefficients. The normalized actual local Floquet
logarithm inherits regularity from its nonzero multiplier.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBoundaryRootRegularCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) : RegularSourceCotangent p :=
  if h2p : (2 : ℝ≥0∞) ≤ p then
    RegularSourceCotangent.ofCotangent h2p
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ.val)
  else
    (RegularSourceCotangent.ofCotangent (le_refl (2 : ℝ≥0∞))
      (fderiv ℂ (fun ψ : CoeffPair 2 => canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) b ψ n)
        (CoeffPair.exponentInclusion (le_of_not_ge h2p) φ.val))).restrict (le_of_not_ge h2p)

@[simp] theorem sourceBoundaryRootRegularCotangent_toCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).toCotangent =
      fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ.val := by
  unfold sourceBoundaryRootRegularCotangent
  split
  · rfl
  · exact (fderiv_canonicalPeriodOneBoundaryRoots_exponent hp (by simp) hp1 (by norm_num) _ b n φ).symm

def sourceBoundaryFloquetRegularCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) : RegularSourceCotangent p :=
  if h2p : (2 : ℝ≥0∞) ≤ p then
    RegularSourceCotangent.ofCotangent h2p (fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ.val)
  else
    (RegularSourceCotangent.ofCotangent (le_refl (2 : ℝ≥0∞))
      (fderiv ℂ (sourceBoundaryFloquetMultiplier (by simp) (by norm_num) b n)
        (CoeffPair.exponentInclusion (le_of_not_ge h2p) φ.val))).restrict (le_of_not_ge h2p)

@[simp] theorem sourceBoundaryFloquetRegularCotangent_toCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryFloquetRegularCotangent hp hp1 b n φ).toCotangent =
      fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ.val := by
  unfold sourceBoundaryFloquetRegularCotangent
  split
  · rfl
  · exact (fderiv_sourceBoundaryFloquetMultiplier_exponent hp (by simp) hp1 (by norm_num) _ b n φ).symm

def sourceBoundaryFloquetLogRegularCotangent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) : RegularSourceCotangent p :=
  (sourceBoundaryFloquetRegularCotangent hp hp1 b n φ).smul
    (sourceBoundaryFloquetMultiplier hp hp1 b n φ.val)⁻¹

/-- This is the derivative of the actual locally analytic logarithm,
including at collapsed gaps; no logarithm branch is supplied. -/
@[simp] theorem sourceBoundaryFloquetLogRegularCotangent_toCotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryFloquetLogRegularCotangent hp hp1 b n φ).toCotangent =
      fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ.val) φ.val := by
  rw [fderiv_sourceBoundaryFloquetLogAt hp hp1 b n φ.val φ.property]
  simp only [sourceBoundaryFloquetLogRegularCotangent, RegularSourceCotangent.smul,
    sourceBoundaryFloquetRegularCotangent_toCotangent]

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- The entire Hilbert root coefficient pair is exponent independent. -/
theorem sourceBoundaryRootRegularCotangent_coefficients_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ).coefficients =
      (sourceBoundaryRootRegularCotangent hq hq1 b n (realTypeSourceExponentInclusion hpq φ)).coefficients := by
  apply RegularSourceCotangent.coefficients_eq_of_toCotangent_eq
    (sourceBoundaryRootRegularCotangent hp hp1 b n φ)
    ((sourceBoundaryRootRegularCotangent hq hq1 b n (realTypeSourceExponentInclusion hpq φ)).restrict hpq)
  simp only [RegularSourceCotangent.restrict, sourceBoundaryRootRegularCotangent_toCotangent]
  exact fderiv_canonicalPeriodOneBoundaryRoots_exponent hp hq hp1 hq1 hpq b n φ

/-- The full moving multiplier coefficients are exponent independent. -/
theorem sourceBoundaryFloquetRegularCotangent_coefficients_exponent
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p) (hq1 : 1 < q) (hpq : p ≤ q)
    (b : BoundaryCondition) (n : ℤ) (φ : realTypeSourceLocus p) :
    (sourceBoundaryFloquetRegularCotangent hp hp1 b n φ).coefficients =
      (sourceBoundaryFloquetRegularCotangent hq hq1 b n (realTypeSourceExponentInclusion hpq φ)).coefficients := by
  apply RegularSourceCotangent.coefficients_eq_of_toCotangent_eq
    (sourceBoundaryFloquetRegularCotangent hp hp1 b n φ)
    ((sourceBoundaryFloquetRegularCotangent hq hq1 b n (realTypeSourceExponentInclusion hpq φ)).restrict hpq)
  simp only [RegularSourceCotangent.restrict, sourceBoundaryFloquetRegularCotangent_toCotangent]
  exact fderiv_sourceBoundaryFloquetMultiplier_exponent hp hq hp1 hq1 hpq b n φ

end NLS.ZakharovShabat
