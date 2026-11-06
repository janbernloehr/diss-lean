import NLS.KdV.HillOriginalMeanZeroSpectralDerivative
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
set_option autoImplicit false
namespace NLS.KdV

/-- The actual ORIGINAL mean-zero Banach norm already is Hilbertian.
Use the proved isometric derivative only to supply its inner product;
the original norm, topology, scalar action and source are unchanged. -/
instance hillRealMeanZeroSourceInnerProductSpace : InnerProductSpace ℝ hillRealMeanZeroSourceSubmodule where
  toNormedSpace := inferInstance
  inner x y := inner ℝ (hillOriginalMeanZeroDerivativeAtZero x) (hillOriginalMeanZeroDerivativeAtZero y)
  add_left x y z := by rw [map_add,inner_add_left]
  smul_left x y r := by rw [map_smul,inner_smul_left]
  norm_sq_eq_re_inner x := by
    rw [←norm_hillOriginalMeanZeroDerivativeAtZero x]
    exact norm_sq_eq_re_inner (hillOriginalMeanZeroDerivativeAtZero x)
  conj_inner_symm x y := inner_conj_symm _ _

/-- This is the original L2 inner product, represented by the exact actual
zero-source Fourier isometry, with no changed source norm. -/
theorem hillRealMeanZeroSource_inner (x y : hillRealMeanZeroSourceSubmodule) :
    inner ℝ x y = inner ℝ (hillOriginalMeanZeroDerivativeAtZero x) (hillOriginalMeanZeroDerivativeAtZero y) := rfl

end NLS.KdV
