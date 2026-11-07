import NLS.KdV.HillCanonicalEnergyMidpoints
import NLS.KdV.HminusOneCanonicalDirichlet

/-! The intrinsic ORIGINAL Hill energy weight for Cartesian estimates.
The gap magnitude is independent of any ordering of complex endpoints.
At real sources this is exactly the original gap width plus the actual
Dirichlet energy's distance from the original periodic energy midpoint. -/
noncomputable section
open Set Complex
open scoped Classical
namespace NLS.KdV

def hillHminusCanonicalCartesianWeight (n : ℕ+) (q : PeriodOneHminusOne) : ℝ :=
  Real.sqrt ‖hillHminusCanonicalGapSquare n q‖+
    ‖hillHminusCanonicalDirichlet n q-hillHminusCanonicalEnergyMidpoint n q‖

theorem hillHminusCanonicalCartesianWeight_nonneg (n : ℕ+) (q : PeriodOneHminusOne) :
    0 ≤ hillHminusCanonicalCartesianWeight n q :=
  add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)

theorem hillHminusCanonicalCartesianWeight_eq_real (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    hillHminusCanonicalCartesianWeight n q =
      (hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1))+
      |hillHminusDirichletLabels q hr n-
        (hillHminusLabels q hr (2*(n:ℕ)-1)+hillHminusLabels q hr (2*(n:ℕ)))/2| := by
  have hgap : 0 ≤ hillHminusLabels q hr (2*(n:ℕ))-hillHminusLabels q hr (2*(n:ℕ)-1) :=
    sub_nonneg.mpr (monotone_hillHminusLabels q hr (by omega))
  rw [hillHminusCanonicalCartesianWeight,hillHminusCanonicalGapSquare_eq_real q hr n,
    hillHminusCanonicalDirichlet_eq_real q hr n,hillHminusCanonicalEnergyMidpoint_real n q hr,
    ← Complex.ofReal_sub,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hgap,
    Real.sqrt_sq hgap]
  congr 1
  rw [show (hillHminusDirichletLabels q hr n:ℂ)-
    ((hillHminusLabels q hr (2*(n:ℕ)-1):ℂ)+(hillHminusLabels q hr (2*(n:ℕ)):ℂ))/2 =
      ((hillHminusDirichletLabels q hr n-
        (hillHminusLabels q hr (2*(n:ℕ)-1)+hillHminusLabels q hr (2*(n:ℕ)))/2:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_real,Real.norm_eq_abs]

end NLS.KdV
