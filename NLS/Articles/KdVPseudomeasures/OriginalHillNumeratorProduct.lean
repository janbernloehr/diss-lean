import NLS.Articles.KdVPseudomeasures.OriginalAnalyticHillZeroCoefficients
import NLS.KdV.HminusOneCanonicalHillPsiProduct

/-! The literal retained-zero product for every original real physical
H-minus-one source converges, after a unique nonzero scalar multiplier,
to the intrinsic Hill numerator on the WHOLE energy plane. Derivatives
also converge locally uniformly. The universal 2/(pi*n) normalization,
common complex all-index coefficient domain and fine estimate remain
open; no angle, Birkhoff-map or main-theorem conclusion is claimed. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV
open scoped ENNReal Classical
namespace NLS.Articles.KdVPseudomeasures

def originalHillPsiProductScalar (n : ℕ+) (q : OriginalHminusOnePotential) : ℂ :=
  hillHminusPsiProductScalar n (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)

theorem originalHillPsiProductScalar_ne_zero (n : ℕ+) (q : OriginalHminusOnePotential) :
    originalHillPsiProductScalar n q ≠ 0 :=
  hillHminusPsiProductScalar_ne_zero n _ (originalPeriodOneCoefficients_real q)

theorem original_Hill_numerator_product_convergence (n : ℕ+) (q : OriginalHminusOnePotential) :
    TendstoLocallyUniformlyOn
      (fun N E => originalHillPsiProductScalar n q*hillEnergyDeletedPartialProduct
        (fun m => originalHillPsiRealZero n m q) n E N)
      (fun E => hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q)) atTop univ :=
  hillHminusCanonicalPsi_product_convergence n _ (originalPeriodOneCoefficients_real q)

theorem originalHillPsiProductScalar_unique (n : ℕ+) (q : OriginalHminusOnePotential) (A : ℂ)
    (hA : TendstoLocallyUniformlyOn
      (fun N E => A*hillEnergyDeletedPartialProduct (fun m => originalHillPsiRealZero n m q) n E N)
      (fun E => hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q)) atTop univ) :
    A = originalHillPsiProductScalar n q :=
  hillHminusPsiProductScalar_unique n _ (originalPeriodOneCoefficients_real q) A hA

theorem original_Hill_numerator_product_deriv_convergence (n : ℕ+) (q : OriginalHminusOnePotential) :
    TendstoLocallyUniformlyOn
      (fun N => deriv (fun E => originalHillPsiProductScalar n q*hillEnergyDeletedPartialProduct
        (fun m => originalHillPsiRealZero n m q) n E N))
      (deriv (fun E => hillHminusCanonicalPsi n (E,originalPeriodOneCoefficients q))) atTop univ :=
  hillHminusCanonicalPsi_product_deriv_convergence n _ (originalPeriodOneCoefficients_real q)

end NLS.Articles.KdVPseudomeasures
