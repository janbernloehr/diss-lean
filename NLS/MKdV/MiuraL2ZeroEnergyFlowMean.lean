import NLS.MKdV.MiuraCartesianActionFlow
import NLS.MKdV.MiuraZeroEnergy
import NLS.ZakharovShabat.ScalarRealL2Density

/-! # The original L² zero-energy trace and signed mean on every action orbit

Finite Fourier sums extend the literal diagonal trace to all complex L²
profiles. Actual isospectrality fixes the physical real mean squared;
continuity of the complete action orbit fixes its signed mean, including
zero mean, at every native integer Sobolev order.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The literal zero-energy formula holds on the whole original complex
L² space, with the actual original Fourier mean. -/
theorem canonicalDiscriminant_scalarL2_zero (a : Coeff 2) :
    canonicalDiscriminant (by simp) (periodOnePotential (scalarL2Diagonal a)) 0 = 2*cosh (a 0) := by
  let F := fun b : Coeff 2 => canonicalDiscriminant (by simp) (periodOnePotential (scalarL2Diagonal b)) 0
  let G := fun b : Coeff 2 => (2 : ℂ)*cosh (b 0)
  have hF : ContinuousAt F a := by
    have hD := ((analyticOnNhd_canonicalDiscriminant_periodOne (by simp) (by norm_num))
      (0,scalarL2Diagonal a) (mem_univ _)).continuousAt
    exact hD.comp (f := fun b : Coeff 2 => ((0 : ℂ),scalarL2Diagonal b))
      (continuous_const.prodMk scalarL2Diagonal.continuous).continuousAt
  have hG : ContinuousAt G a := continuousAt_const.mul
    (Complex.continuous_cosh.continuousAt.comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.continuousAt)
  have ht := tendsto_scalarInclusion_scalarL2H1Approx a
  have he (N : ℕ) : F (scalarInclusion (scalarL2H1Approx a N)) = G (scalarInclusion (scalarL2H1Approx a N)) := by
    dsimp only [F,G]
    rw [scalarL2Diagonal_scalarInclusion,canonicalDiscriminant_miura_zero,scalarInclusion_apply]
  exact tendsto_nhds_unique (hF.tendsto.comp ht) ((hG.tendsto.comp ht).congr (fun N => (he N).symm))

theorem miuraActionFlow_mean_square_allSobolev (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    ((miuraActionFlow s a ha n t).val 0)^2 = (a.val 0)^2 := by
  let b := miuraActionFlow s a ha n t
  have hb := miuraActionFlow_real s a ha n t
  have hs := congrArg Subtype.val (miuraActionFlow_source s a ha n t)
  have hD := congrArg (fun f : ℂ → ℂ => f 0)
    (miuraActionFlowFamily.data.discriminant_hilbertPairedActionFlow (miuraActionInitialSource s a ha) n (-(n : ℤ)) t)
  rw [← hs,miuraActionInitialSource_L2_diagonal,miuraActionInitialSource_L2_diagonal,
    canonicalDiscriminant_scalarL2_zero,canonicalDiscriminant_scalarL2_zero] at hD
  simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul] at hD
  have haim : (a.val 0).im = 0 := by
    have h := congrArg Complex.im (ha 0)
    simp only [neg_zero,Complex.conj_im] at h
    linarith
  have hbim : (b.val 0).im = 0 := by
    have h := congrArg Complex.im (hb 0)
    simp only [neg_zero,Complex.conj_im] at h
    linarith
  have har : a.val 0 = ((a.val 0).re : ℂ) := Complex.ext rfl (by simp [haim])
  have hbr : b.val 0 = ((b.val 0).re : ℂ) := Complex.ext rfl (by simp [hbim])
  change 2*cosh (b.val 0) = 2*cosh (a.val 0) at hD
  have hcos := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hD
  rw [har,hbr] at hcos
  have hreal : Real.cosh (b.val 0).re = Real.cosh (a.val 0).re := by
    simpa only [← Complex.ofReal_cosh,Complex.ofReal_re] using congrArg Complex.re hcos
  have habs : |(b.val 0).re| = |(a.val 0).re| := by
    have he := congrArg Real.arcosh
      (show Real.cosh |(b.val 0).re| = Real.cosh |(a.val 0).re| from by simpa only [Real.cosh_abs] using hreal)
    simpa only [Real.arcosh_cosh (abs_nonneg _)] using he
  have hsq : (b.val 0).re^2 = (a.val 0).re^2 := by
    have he := congrArg (fun r : ℝ => r^2) habs
    change |(b.val 0).re|^2 = |(a.val 0).re|^2 at he
    simpa only [sq_abs] using he
  change (b.val 0)^2 = (a.val 0)^2
  rw [har,hbr,← Complex.ofReal_pow,← Complex.ofReal_pow,hsq]

/-- The signed original mean is fixed on the entire connected orbit,
without using a globally single-valued signed recovery from NLS actions. -/
theorem miuraActionFlow_mean_allSobolev (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (t : ℝ) :
    (miuraActionFlow s a ha n t).val 0 = a.val 0 := by
  by_cases hz : a.val 0 = 0
  · have hs := miuraActionFlow_mean_square_allSobolev s a ha n t
    rw [hz,zero_pow (by norm_num : 2 ≠ 0)] at hs
    exact (sq_eq_zero_iff.mp hs).trans hz.symm
  have hc : Continuous (fun r => (miuraActionFlow s a ha n r).val 0) :=
    (WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).continuous.comp (continuous_miuraActionFlow s a ha n)
  have he := isPreconnected_univ.eq_of_sq_eq hc.continuousOn continuousOn_const
    (fun r _ => miuraActionFlow_mean_square_allSobolev s a ha n r) (fun _ => hz) (mem_univ (0 : ℝ))
    (by rw [miuraActionFlow_zero])
  exact he (mem_univ t)

end NLS.MKdV
