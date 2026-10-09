import NLS.ZakharovShabat.ClassicalSobolevPotential
import NLS.ComplexAnalysis.IntervalH1Variation
import NLS.ZakharovShabat.IntervalHermitianFirstBornBound
import NLS.ZakharovShabat.L2HermitianUniformRemainderBound

/-! # The unit-interval G.2 estimates in the integral Hilbert H1 norm

The norm convention is explicit: sum the L2 energies of both potential
components and both derivatives. The first Born and actual fundamental
solution remainder have the printed coefficient 3/(2|z|), without a
supremum norm premise or a periodic endpoint condition.
-/
noncomputable section
open Set MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- The Hilbert product of the two unnormalized integral H1 norms. -/
def intervalPairH1Norm (φ : ℝ → ℂ × ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (intervalH1Norm (fun s => (φ s).1) t ^ 2+
    intervalH1Norm (fun s => (φ s).2) t ^ 2)

theorem intervalPairH1Norm_nonneg (φ : ℝ → ℂ × ℂ) (t : ℝ) :
    0 ≤ intervalPairH1Norm φ t := Real.sqrt_nonneg _

theorem intervalH1Norm_fst_le_pair (φ : ℝ → ℂ × ℂ) (t : ℝ) :
    intervalH1Norm (fun s => (φ s).1) t ≤ intervalPairH1Norm φ t := by
  unfold intervalPairH1Norm
  exact (Real.sqrt_sq (intervalH1Norm_nonneg _ _)).symm.le.trans
    (Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _)))

theorem intervalH1Norm_snd_le_pair (φ : ℝ → ℂ × ℂ) (t : ℝ) :
    intervalH1Norm (fun s => (φ s).2) t ≤ intervalPairH1Norm φ t := by
  unfold intervalPairH1Norm
  exact (Real.sqrt_sq (intervalH1Norm_nonneg _ _)).symm.le.trans
    (Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg _)))

/-- Identification with the literal integral of both component energies
and both derivative energies, rather than an equivalent norm. -/
theorem intervalPairH1Norm_eq_integral (φ : ℝ → ℂ × ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 t)))
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 t)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 t))) :
    intervalPairH1Norm φ t = Real.sqrt (∫ s in 0..t,
      ‖(φ s).1‖^2+‖(φ s).2‖^2+‖deriv (fun r => (φ r).1) s‖^2+
        ‖deriv (fun r => (φ r).2) s‖^2) := by
  rw [intervalPairH1Norm,intervalH1Norm_sq _ _ ht,intervalH1Norm_sq _ _ ht,
    ← intervalIntegral.integral_add (intervalIntegrable_H1_integrand _ t ht hφ.fst hdf)
      (intervalIntegrable_H1_integrand _ t ht hφ.snd hdg)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  dsimp
  ring

private theorem scalar_weighted_le_unit_H1
    (c : ℂ) (hc : c ≠ 0) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hL2 : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hdL2 : MemLp (deriv f) 2 (volume.restrict (Ioc 0 1)))
    (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|c.re| * t.val))*‖oscillatoryIntegral c t f‖ ≤
      3/(2*‖c‖)*intervalH1Norm f 1 := by
  have hsub : uIcc 0 t.val ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le t.property.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2
  have hi : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hdL2.integrable (by norm_num))
  apply (norm_oscillatoryIntegral_weighted_le c hc t t.property.1 f (hf.mono hsub)
    (hi.mono_set hsub)).trans
  exact (div_le_div_of_nonneg_right (endpoint_variation_le_three_H1 f hf hL2 hdL2 t)
    (by positivity)).trans_eq (by ring)

/-- The uniform Born estimate for genuine interval H1 inputs. The constant
comes from the combined trace estimate, not a constant-one trace embedding. -/
theorem intervalHermitianFirstBornOperator_weighted_le_unit_H1
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)))
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 1)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 1)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    Real.exp (-(|z.im| * t.val))*‖intervalHermitianFirstBornOperator φ z t‖ ≤
      3/(2*‖z‖)*intervalPairH1Norm φ 1 := by
  have hminus := scalar_weighted_le_unit_H1 (-Complex.I*z)
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hz) _ hf hφ.fst hdf t
  have hplus := scalar_weighted_le_unit_H1 (Complex.I*z)
    (mul_ne_zero Complex.I_ne_zero hz) _ hg hφ.snd hdg t
  simp only [Complex.mul_re,Complex.neg_re,Complex.I_re,neg_zero,zero_mul,
    Complex.neg_im,Complex.I_im,neg_one_mul,zero_sub,neg_neg,one_mul,
    abs_neg,norm_mul,norm_neg,Complex.norm_I] at hminus hplus
  rw [norm_intervalHermitianFirstBornOperator,mul_max_of_nonneg _ _ (Real.exp_nonneg _)]
  exact max_le (hminus.trans (mul_le_mul_of_nonneg_left (intervalH1Norm_fst_le_pair φ 1)
    (by positivity))) (hplus.trans (mul_le_mul_of_nonneg_left (intervalH1Norm_snd_le_pair φ 1)
    (by positivity)))

/-- The actual physical L2 solution satisfies the unit-interval G.2
remainder estimate in the explicit integral Hilbert H1 norm. -/
theorem l2HermitianRemainder_le_unit_H1
    (φ : ℝ → ℂ × ℂ) (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1)))
    (hf : AbsolutelyContinuousOnInterval (fun s => (φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (φ s).2) 0 1)
    (hdf : MemLp (deriv (fun s => (φ s).1)) 2 (volume.restrict (Ioc 0 1)))
    (hdg : MemLp (deriv (fun s => (φ s).2)) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    l2NormalizedHermitianRemainder (intervalL2OfFunction φ hφ) z t ≤
      3/(2*‖z‖)*(1+‖intervalL2OfFunction φ hφ‖*Real.exp ‖intervalL2OfFunction φ hφ‖)*
        intervalPairH1Norm φ 1 := by
  let B := 3/(2*‖z‖)*intervalPairH1Norm φ 1
  have hB : 0 ≤ B := mul_nonneg (by positivity) (intervalPairH1Norm_nonneg φ 1)
  have hF (s : Icc (0 : ℝ) 1) :
      l2NormalizedHermitianFirstBorn (intervalL2OfFunction φ hφ) z s ≤ B := by
    change Real.exp (-(|z.im| * s.val))*
      ‖l2HermitianFirstBornOperatorCurve (intervalL2OfFunction φ hφ) z s‖ ≤ B
    rw [← intervalHermitianFirstBornOperator_eq_l2 φ hφ z s]
    exact intervalHermitianFirstBornOperator_weighted_le_unit_H1 φ hφ hf hg hdf hdg z hz s
  exact (l2HermitianRemainder_le_of_firstBorn_uniform_unit (intervalL2OfFunction φ hφ)
    z B hB hF t).trans_eq (by dsimp [B]; ring)

/-- All physical H1 Fourier pairs instantiate the integral-norm estimate. -/
theorem classicalHermitianRemainder_sobolev_le_unit_H1
    (a : ScalarDomain 2 × ScalarDomain 2)
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedHermitianRemainder (classicalSobolevPotential a) z t ≤
      3/(2*‖z‖)*(1+classicalPotentialL2Norm (classicalSobolevPotential a)*
        Real.exp (classicalPotentialL2Norm (classicalSobolevPotential a)))*
        intervalPairH1Norm (extend (classicalSobolevPotential a)) 1 := by
  obtain ⟨hf,hg,_,_⟩ := classicalSobolevPotential_regular a
  have h := l2HermitianRemainder_le_unit_H1 (extend (classicalSobolevPotential a))
    (memLp_extend_continuousPotential _) hf hg
    (NLS.Fourier.memLp_deriv_extend_sobolevUnitCurve a.1)
    (NLS.Fourier.memLp_deriv_extend_sobolevUnitCurve a.2) z hz t
  change l2NormalizedHermitianRemainder (continuousPotentialL2Class _) z t ≤
    3/(2*‖z‖)*(1+‖continuousPotentialL2Class _‖*Real.exp ‖continuousPotentialL2Class _‖)*
      intervalPairH1Norm (extend (classicalSobolevPotential a)) 1 at h
  simpa only [l2NormalizedHermitianRemainder_of_continuous,norm_continuousPotentialL2Class] using h

end NLS.ZakharovShabat
