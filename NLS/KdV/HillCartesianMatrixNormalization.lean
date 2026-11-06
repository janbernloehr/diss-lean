import NLS.KdV.HillHminusEndpointCartesianMatrix
import NLS.KdV.HillIsospectralData

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate
namespace NLS.KdV

/-- Opposite ORIGINAL signed coordinates have the actual twice-action
product, in either order and without any gap-openness hypothesis. -/
theorem hillSignedSpectralCartesian_opposite_product
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool) :
    hillSignedSpectralCartesian σ n q * hillSignedSpectralCartesian (!σ) n q =
      2 * (hillRealGapIntegral q.val q.property.1 q.property.2 n 0 : ℂ) := by
  cases σ
  · change conj (hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos) *
      hillSpectralCartesian q.val q.property.1 q.property.2 n n.pos = _
    rw [mul_comm]
    exact hillSpectralCartesian_mul_conj q n
  · exact hillSpectralCartesian_mul_conj q n

/-- The endpoint matrix times its coordinate denominator is exactly
isospectral. Its only nonzero entries use the actual twice-action product. -/
theorem hillOriginalComplexGardnerMatrixEntry_mul_product_isospectral
    (q r : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (hΔ : ∀ E : ℂ, hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E =
      hillL2Discriminant (SpectralWeight.one.toCoeff r.val) E) :
    hillOriginalComplexGardnerMatrixEntry σ τ n m *
        (hillSignedSpectralCartesian σ n q * hillSignedSpectralCartesian τ m q) =
      hillOriginalComplexGardnerMatrixEntry σ τ n m *
        (hillSignedSpectralCartesian σ n r * hillSignedSpectralCartesian τ m r) := by
  by_cases hnm : (n:ℕ) = (m:ℕ)
  · have he : n = m := Subtype.ext hnm
    subst m
    have hI := hillRealGapIntegral_eq_of_discriminant_eq q r hΔ n 0
    have hp (b : Bool) : hillSignedSpectralCartesian b n q * hillSignedSpectralCartesian (!b) n q =
        hillSignedSpectralCartesian b n r * hillSignedSpectralCartesian (!b) n r := by
      rw [hillSignedSpectralCartesian_opposite_product,hillSignedSpectralCartesian_opposite_product,hI]
    cases σ <;> cases τ
    · simp [hillOriginalComplexGardnerMatrixEntry]
    · rw [show hillSignedSpectralCartesian false n q * hillSignedSpectralCartesian true n q =
        hillSignedSpectralCartesian false n r * hillSignedSpectralCartesian true n r from hp false]
    · rw [show hillSignedSpectralCartesian true n q * hillSignedSpectralCartesian false n q =
        hillSignedSpectralCartesian true n r * hillSignedSpectralCartesian false n r from hp true]
    · simp [hillOriginalComplexGardnerMatrixEntry]
  · simp [hillOriginalComplexGardnerMatrixEntry,hnm]

end NLS.KdV
