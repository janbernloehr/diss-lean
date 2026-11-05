import NLS.KdV.HillHminusOneDirichlet
import NLS.KdV.ClassicalHillFreeDirichlet
import NLS.KdV.HillHminusOneCanonicalFreeLabels

/-! # Exact free normalization of the original H^-1 Dirichlet characteristic -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusDirichlet_zero_eq_classical (lambda : ℂ) :
    hillHminusDirichlet 0 lambda = classicalHillDirichlet 0 lambda := by
  have he : SpectralWeight.one.toCoeff
      (hillContinuousCoefficients (0 : C(AddCircle (2 : ℝ),ℂ))) = (0 : Coeff 2) := by
    ext k
    simpa only [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply,
      Fourier.continuousFourierCLM_apply] using
        congrArg (fun f : Coeff 2 => f k) (map_zero Fourier.continuousFourierCLM)
  have h := hillHminusDirichlet_eq_hillL2 (0 : Coeff 2) lambda
  rw [map_zero,map_zero] at h
  rw [h,← he,hillL2Dirichlet_eq_classical]
  rfl

theorem hillHminusDirichlet_free_sq (z : ℂ) (hz : z ≠ 0) :
    hillHminusDirichlet 0 (z^2) = sin z/z := by
  rw [hillHminusDirichlet_zero_eq_classical,classicalHillDirichlet,
    classicalHillFlow_free_sine z hz ⟨1,by constructor <;> norm_num⟩]
  simp only [ofReal_one,mul_one]

theorem hillHminusDirichlet_free_nat_root (n : ℕ) (hn : 1 ≤ n) :
    hillHminusDirichlet 0 (freeHillValue n) = 0 := by
  have he : (freeHillValue n : ℂ) = ((n : ℂ)*(Real.pi : ℂ))^2 := by
    unfold freeHillValue
    push_cast
    ring
  rw [he,hillHminusDirichlet_free_sq _
    (mul_ne_zero (by exact_mod_cast (show n ≠ 0 by omega)) (by exact_mod_cast Real.pi_ne_zero))]
  rw [← ofReal_natCast,← ofReal_mul,← ofReal_sin,Real.sin_nat_mul_pi,ofReal_zero,zero_div]

end NLS.KdV
