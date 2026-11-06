import NLS.KdV.HillBirkhoffAbelianNormalization

/-! # Exact original Abelian coordinates determine the global physical L2 source -/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.KdV

theorem hillOriginalBirkhoffAbelianCoordinate_injective
    (p q : hillRealMeanZeroSourceSubmodule)
    (he : ∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n = hillOriginalBirkhoffAbelianCoordinate q n) :
    p = q := by
  apply hillOriginalBirkhoffHomeomorph.injective
  change hillOriginalBirkhoffMap p = hillOriginalBirkhoffMap q
  apply Subtype.ext
  funext k
  let n : ℕ+ := ⟨k+1,by omega⟩
  have hh := he n
  dsimp only [hillOriginalBirkhoffAbelianCoordinate] at hh
  have hn : (n : ℕ)-1 = k := by change (k+1)-1 = k; omega
  rw [hn] at hh
  have hc := congrArg (fun z : ℂ => z*(Real.sqrt 2 : ℂ)) hh
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [div_mul_cancel₀ _ hs,div_mul_cancel₀ _ hs] at hc
  apply Prod.ext
  · have h := congrArg Complex.re hc
    simpa only [sub_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,zero_mul,mul_zero,sub_zero] using h
  · have h := congrArg Complex.im hc
    simp only [sub_im,ofReal_im,mul_im,I_re,I_im,zero_mul,one_mul,zero_add,zero_sub] at h
    exact neg_injective h

end NLS.KdV
