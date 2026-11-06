import NLS.Fourier.UnitIntervalHillBoundaryForcing
import NLS.Fourier.HalfIntervalL2Identification
import NLS.SequenceSpaces.SobolevEmbedding
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal Classical

namespace NLS.Fourier



/-- Zero endpoint values remove the jump in the first derivative formula;
the original half coefficients then have one full Hilbert derivative. -/
theorem memlp_sobolev_halfCoefficient_of_ac_zero_boundary
    (f g : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hf2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hfg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (h0 : f 0=0) (h1 : f 1=0) :
    Memℓp (fun n : ℤ => (Weight.sobolev 1 n : ℂ)*halfCoefficient f n) 2 := by
  let F := halfIntervalCoeffs (by norm_num : (1 : ℝ≥0∞) < 2) (by simp)
    (unitIntervalMemLpCoefficients f hf2)
  let G := halfIntervalCoeffs (by norm_num : (1 : ℝ≥0∞) < 2) (by simp)
    (unitIntervalMemLpCoefficients g hg2)
  have hF (n : ℤ) : F n = halfCoefficient f n := halfIntervalCoeffs_two_ofFunction f hf2 n
  have hG (n : ℤ) : G n = halfCoefficient g n := halfIntervalCoeffs_two_ofFunction g hg2 n
  have hgi : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hg2.integrable (by norm_num))
  have hder (n : ℤ) : G n = I*(Real.pi : ℂ)*n*F n := by
    rw [hF,hG]
    simpa only [h0,h1,zero_mul,sub_self,zero_div,add_zero] using
      halfCoefficient_of_ac_hasDerivAt hf hgi hfg n
  have hsum := (lp.memℓp F).norm.add (lp.memℓp G).norm
  apply hsum.mono
  intro n
  have hn : ‖G n‖ = Real.pi*|(n : ℝ)| *‖F n‖ := by
    rw [hder,norm_mul,norm_mul,norm_mul,norm_I,one_mul,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_intCast]
  change ‖(Weight.sobolev 1 n : ℂ)*halfCoefficient f n‖ ≤ ‖F n‖+‖G n‖
  rw [norm_mul,Complex.norm_real,
    Real.norm_of_nonneg (Weight.positive _ _).le,Weight.sobolev_apply,Real.rpow_one,← hF]
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  nlinarith [mul_nonneg (sub_nonneg.mpr hpi) (mul_nonneg (abs_nonneg (n : ℝ)) (norm_nonneg (F n)))]

/-- The actual half-interval coefficients are absolutely summable for a
zero-boundary H1 function, without any periodic derivative hypothesis. -/
theorem exists_halfCoefficient_l1_of_ac_zero_boundary
    (f g : ℝ → ℂ) (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hf2 : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg2 : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hfg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt f (g x) x)
    (h0 : f 0=0) (h1 : f 1=0) :
    ∃ a : Coeff 1, ∀ n : ℤ, a n = halfCoefficient f n := by
  let a : WeightedCoeff (Weight.sobolev 1) 2 :=
    ⟨halfCoefficient f,memlp_sobolev_halfCoefficient_of_ac_zero_boundary f g hf hf2 hg2 hfg h0 h1⟩
  exact ⟨WeightedCoeff.sobolevToL1CLM 2 (by simp) a,fun n =>
    WeightedCoeff.sobolevToL1CLM_apply 2 (by simp) a n⟩

end NLS.Fourier
