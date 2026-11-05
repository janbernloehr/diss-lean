import NLS.MKdV.MiuraHillPrimitiveComparison

/-! # Canonical root and primitive identification on a real C¹ domain

These are qualified versions of the paper's Lemmas 4 and 5. The frequency
lies in the nonreal right half-plane. No full H¹ extension, gap labeling,
or action identity is asserted by these declarations.
-/
noncomputable section
open NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.Articles.MKdVNLSHierarchies

theorem lemma4_root_real_C1_right_halfPlane
    (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hr : ∀ x, (u x).im = 0)
    (hp : Function.Periodic u 1) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    classicalHillContinuedRoot (z^2,miuraHillProfileCurve u hu) =
      sourceCanonicalRoot (by simp) (by norm_num) (realDiagonalProfileSource u hu.continuous hr).val z :=
  (miuraHill_sheets_eq_NLS u hu hr hp z hzr hzi).1

theorem lemma5_primitive_real_C1_right_halfPlane
    (u : ℝ → ℂ) (hu : ContDiff ℝ 1 u) (hr : ∀ x, (u x).im = 0)
    (hp : Function.Periodic u 1) (z : ℂ) (hzr : 0 < z.re) (hzi : z.im ≠ 0) :
    classicalHillContinuedPrimitive (z^2,miuraHillProfileCurve u hu) =
      sourceAbelianPrimitive (by simp) (by norm_num) (realDiagonalProfileSource u hu.continuous hr).val
        (realDiagonalProfileSource u hu.continuous hr).property z :=
  (miuraHill_sheets_eq_NLS u hu hr hp z hzr hzi).2

end NLS.Articles.MKdVNLSHierarchies
