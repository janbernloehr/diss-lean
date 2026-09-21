import NLS.ZakharovShabat.FreeSineQuotient
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Holomorphy of the filled free sine quotient

The divided difference of the entire sine function is entire, including
at the filled center. This allows Cauchy estimates for errors measured
against the squared free quotient.
-/

open Set Complex Topology
namespace NLS.ZakharovShabat

/-- Filling the sine quotient gives an entire function at every signed free center. -/
theorem differentiable_freeSineQuotient (n : ℤ) : Differentiable ℂ (freeSineQuotient n) := by
  have hd : Differentiable ℂ (dslope sin 0) :=
    differentiableOn_univ.mp ((Complex.differentiableOn_dslope (Filter.univ_mem : (univ : Set ℂ) ∈ 𝓝 0)).mpr
      differentiable_sin.differentiableOn)
  have hi : Differentiable ℂ (fun z : ℂ => z-(Real.pi : ℂ)*n) := by fun_prop
  exact (hd.comp hi).const_mul _

/-- The free quotient is analytic also at its removable singularity. -/
theorem analyticOnNhd_freeSineQuotient (n : ℤ) : AnalyticOnNhd ℂ (freeSineQuotient n) univ :=
  (differentiable_freeSineQuotient n).differentiableOn.analyticOnNhd isOpen_univ

end NLS.ZakharovShabat
