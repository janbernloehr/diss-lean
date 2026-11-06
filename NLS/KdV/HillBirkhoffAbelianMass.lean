import NLS.KdV.HillBirkhoffAbelianNormalization

/-! # Exact physical L2 mass in the original complex Abelian normalization

The fixed global physical map has canonical real pairs (X,Y). Its complex
coordinate is (X-iY)/sqrt(2), so Parseval gives the exact factor 4*pi*n.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem norm_sq_hillOriginalBirkhoffAbelianCoordinates
    (p : hillRealMeanZeroSourceSubmodule) :
    ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
      ‖hillOriginalBirkhoffAbelianCoordinate p ⟨k+1,by omega⟩‖^2 := by
  rw [←norm_hillOriginalBirkhoffMap p,norm_HillBirkhoffSpace_sq]
  apply tsum_congr
  intro k
  have hn : (k+1 : ℕ)-1=k := by omega
  have hs : ‖hillOriginalBirkhoffAbelianCoordinate p ⟨k+1,by omega⟩‖^2=
      (((hillOriginalBirkhoffMap p).val k).1^2+((hillOriginalBirkhoffMap p).val k).2^2)/2 := by
    change ‖((((hillOriginalBirkhoffMap p).val ((k+1)-1)).1 : ℂ)-
      I*(((hillOriginalBirkhoffMap p).val ((k+1)-1)).2 : ℂ))/(Real.sqrt 2 : ℂ)‖^2=_
    rw [hn,norm_div,div_pow,norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (by norm_num),
      Complex.sq_norm,Complex.normSq_apply]
    simp only [sub_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,
      sub_im,mul_im,zero_add,zero_sub]
    ring
  rw [hs]
  ring

end NLS.KdV
