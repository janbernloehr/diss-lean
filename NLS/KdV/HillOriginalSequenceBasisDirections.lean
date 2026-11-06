import NLS.KdV.HillOriginalCartesianBasisDirections
import NLS.KdV.HillMeanZeroSequencePhysicalDifferential

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.KdV

/-- At EVERY original source, the ACTUAL sequence derivative attains each
real and imaginary coordinate basis vector with its physical normalization.
All low and collapsed gaps are included. -/
theorem exists_hillOriginalMeanZeroDerivative_basis_directions
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) :
    ∃ a b : hillRealMeanZeroSourceSubmodule,
      fderiv ℝ hillOriginalMeanZeroRealSpectralMap q a =
        lp.single 2 k ((Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ)*I) ∧
      fderiv ℝ hillOriginalMeanZeroRealSpectralMap q b =
        lp.single 2 k (Real.sqrt (2*Real.pi*(k+1 : ℕ)) : ℂ) := by
  let Q : RealPeriodOneHillPotential := ⟨q.val.val,q.val.property⟩
  have hmean : Q.val.val 0 = 0 := (mem_hillRealMeanZeroSourceSubmodule q.val).mp q.property
  obtain ⟨Z,hZ,_⟩ := exists_hillOriginal_signedCartesian_hminus_Gardner_matrix_all_gaps Q hmean
  let m : ℕ+ := ⟨k+1,by omega⟩
  obtain ⟨a,b,hab⟩ := exists_hillOriginalCartesian_basis_directions q Z hZ m
  refine ⟨a,b,?_,?_⟩
  · ext j
    let n : ℕ+ := ⟨j+1,by omega⟩
    rw [hillOriginalMeanZeroRealSpectralMap_coordinate_fderiv q j (Z true n)
      (hZ true n).1 (hZ true n).2 a,(hab n).1]
    have he : (n : ℕ) = (m : ℕ) ↔ j = k := by change j+1 = k+1 ↔ j=k; omega
    simp only [he,lp.single_apply,Pi.single_apply]
    by_cases hj : j = k
    · subst j
      rw [if_pos rfl,mul_one,if_pos rfl]
    · rw [if_neg hj,if_neg hj,mul_zero,mul_zero]
  · ext j
    let n : ℕ+ := ⟨j+1,by omega⟩
    rw [hillOriginalMeanZeroRealSpectralMap_coordinate_fderiv q j (Z true n)
      (hZ true n).1 (hZ true n).2 b,(hab n).2]
    have he : (n : ℕ) = (m : ℕ) ↔ j = k := by change j+1 = k+1 ↔ j=k; omega
    simp only [he,lp.single_apply,Pi.single_apply]
    by_cases hj : j = k
    · subst j
      rw [if_pos rfl,mul_one,if_pos rfl]
    · rw [if_neg hj,if_neg hj,mul_zero]

/-- EVERY complex single is in the range of the ACTUAL original derivative
at EVERY original real mean-zero source. No inverse or completeness of
spectral gradients is supplied as a premise. -/
theorem exists_hillOriginalMeanZeroDerivative_single_preimage
    (q : hillRealMeanZeroSourceSubmodule) (k : ℕ) (z : ℂ) :
    ∃ h : hillRealMeanZeroSourceSubmodule,
      fderiv ℝ hillOriginalMeanZeroRealSpectralMap q h = lp.single 2 k z := by
  obtain ⟨a,b,ha,hb⟩ := exists_hillOriginalMeanZeroDerivative_basis_directions q k
  let C := Real.sqrt (2*Real.pi*(k+1 : ℕ))
  have hC : C ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  refine ⟨(z.im/C) • a+(z.re/C) • b,?_⟩
  rw [map_add,map_smul,map_smul,ha,hb]
  ext j
  simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,Complex.real_smul,
    lp.single_apply,Pi.single_apply]
  by_cases hj : j = k
  · rw [if_pos hj,if_pos hj,if_pos hj]
    change ((z.im/C : ℝ) : ℂ)*((C : ℂ)*I)+((z.re/C : ℝ) : ℂ)*(C : ℂ) = z
    apply Complex.ext <;> simp only [add_re,add_im,mul_re,mul_im,ofReal_re,ofReal_im,
      I_re,I_im,zero_mul,mul_zero,mul_one,sub_zero,add_zero,zero_add]
    · field_simp [hC]
    · field_simp [hC]
  · rw [if_neg hj,if_neg hj,if_neg hj,mul_zero,mul_zero,add_zero]

end NLS.KdV
