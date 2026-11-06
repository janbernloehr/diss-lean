import NLS.KdV.MiuraHillPsiNumerators
import NLS.KdV.HillMiuraPositiveGaps
import NLS.ZakharovShabat.SourcePsiOddGrowth

/-! Actual retained-gap energy zeros, including collapsed gaps. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV
namespace MiuraHillPsiFamily

theorem exists_retained_energy_zero (A : MiuraHillPsiFamily) (u : PeriodOneRealL2) (n m : ℕ+)
    (hmn : m ≠ n) :
    ∃ x : ℝ, x ∈ Icc (hillMiuraDiracLeft u.val ((m:ℕ):ℤ)).re
      (hillMiuraDiracRight u.val ((m:ℕ):ℤ)).re ∧ A.numerator n ((x:ℂ)^2,u.val) = 0 := by
  obtain ⟨D⟩ := A.nonempty_periodCircle u.val (A.real_mem_source u) m
  let a : Coeff 2 := A.roots ((n:ℕ):ℤ) (hillMiuraDiagonal u.val)
  have hperiod : (∮ z in C((D.center:ℂ),D.radius),
      sourceOddPsiCandidate ((n:ℕ):ℤ) (z,a)/
        sourceCanonicalRoot (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) z) = 0 := by
    have h := A.numerator_pullback_period n m u.val (A.real_mem_source u) D
    rw [if_neg hmn] at h
    have hraw := (mul_eq_zero.mp h).resolve_left (inv_ne_zero
      (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)))
    have he (z : ℂ) : sourceOddPsiCandidate ((n:ℕ):ℤ) (z,a) = 2*z*A.numerator n (z^2,u.val) :=
      (A.numerator_frequency_identity n u.val z).symm
    simp_rw [he]
    exact hraw
  obtain ⟨z,hz,hzero⟩ := exists_sourceOddPsiCandidate_zero_in_gap (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((n:ℕ):ℤ) a
    (by
      intro k
      change (displacedRoots (A.roots ((n:ℕ):ℤ) (hillMiuraRealSource u).val : Coeff 2) k).im=0
      rw [A.verified.real_agreement ((n:ℕ):ℤ) (hillMiuraRealSource u)]
      have hr := sourcePsiGapRoot_mem_realDeletedCoeffSubmodule (by norm_num) (by norm_num)
        ((n:ℕ):ℤ) (hillMiuraRealSource u) k
      simpa only [displacedRoots,Complex.add_im,Complex.mul_im,Complex.ofReal_im,
        Complex.intCast_im,mul_zero,zero_mul,zero_add] using hr)
    ((m:ℕ):ℤ) D hperiod
  have hI := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) ((m:ℕ):ℤ) z hz
  have him := sourcePeriodicSegment_im_eq_zero_of_realType (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ) z hz
  have hzreal : (z.re:ℂ) = z := Complex.ext rfl him.symm
  have hpos := hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos)
  have hzne : z ≠ 0 := by
    intro he
    have hre : z.re = 0 := by rw [he]; rfl
    linarith [hI.1]
  have hmul : 2*z*A.numerator n (z^2,u.val) = 0 :=
    (A.numerator_frequency_identity n u.val z).trans hzero
  have hnum := (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hzne)
  exact ⟨z.re,hI,by simpa only [hzreal] using hnum⟩

end MiuraHillPsiFamily
end NLS.KdV
