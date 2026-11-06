import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeGerms
import NLS.KdV.HillRoughAbelianGardnerOn
import NLS.KdV.HillBirkhoffAbelianNormalization

/-! # The ONE global rough forward map has the actual Gardner matrix

Canonicality holds at EVERY real mean-zero rough source, including
non-L2 sources and closed gaps. The physical comparison is to the fixed
GLOBAL ORIGINAL L2 Birkhoff map with its exact Abelian normalization.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
namespace GlobalRoughAbelianForwardData

/-- Full original Gardner matrix at EVERY real mean-zero HminusOne
source, without smallness, nonclosed-gap or L2 assumptions. -/
theorem gardner_matrix_real_meanZero (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (hm : q.val 0 = 0)
    (σ τ : Bool) (n m : ℕ+) :
    NLS.Poisson.hminusGardnerBracket (hillRoughSignedAbelianComponent D.signed σ n)
      (hillRoughSignedAbelianComponent D.signed τ m) q =
        hillOriginalComplexGardnerMatrixEntry σ τ n m/2 := by
  exact hillRoughAbelian_Gardner_matrix_on_real_domain D.signed D.domain D.domain_open
    D.signed_analytic (fun p _ j => D.signed_physical p j)
    q (D.real_mem_domain q hr) hr hm σ τ n m

/-- Exact agreement with the fixed GLOBAL ORIGINAL L2 Birkhoff map,
with its literal action/Cartesian/Abelian normalization. -/
theorem original_global_birkhoff_agreement (D : GlobalRoughAbelianForwardData)
    (q : hillRealMeanZeroSourceSubmodule) (n : ℕ+) :
    (D.signed (hillOriginalHminusSource q.val.val)).val (n : ℤ) =
      hillOriginalBirkhoffAbelianCoordinate q n := by
  exact hillBirkhoffAbelian_rough_map_agreement D.signed D.domain
    (fun p _ j => D.signed_physical p j) q
    (D.real_mem_domain _ (hillOriginalHminusSource_real q.val.val q.val.property.2)) n

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
