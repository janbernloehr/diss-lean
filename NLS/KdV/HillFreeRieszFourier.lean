import NLS.KdV.HillPhysicalResolventFactorization

/-! Exact identification of the ACTUAL zero-potential contour projection
with the two literal free Fourier modes in the source Haar normalization. -/
noncomputable section
open Set Metric Complex
namespace NLS.KdV
open NLS.Fourier

/-- Every free physical resolvent coefficient is the exact untruncated reciprocal. -/
theorem hillContinuousResolvent_zero_coefficient (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (z : ℂ) (hz : z ∈ sphere (freeHillValue n:ℂ) (n:ℝ))
    (F : CircleL2) (k : ℤ) :
    fourierCoeff (singularHillContinuousResolvent 0 z F) k =
      (z-(freeHillValue k:ℂ))⁻¹*fourierCoeff F k := by
  rw [singularHillContinuousResolvent_zero_eq_half 0 (by norm_num) (by norm_num) n hn hlog z hz]
  change fourierCoeff (hillHalfDenominatorToContinuous z
    (l2Synthesis (hillNormalizedPhaseInverse z (l2Synthesis.symm (hillHalfDenominatorL2 z F))))) k = _
  rw [hillHalfDenominatorToContinuous_coefficient,LinearIsometryEquiv.symm_apply_apply,
    hillHalfDenominatorSymbol_apply n hn z hz]
  change (hillPhaseInverseSymbol z k*l2Synthesis.symm (hillHalfDenominatorL2 z F) k)*hillHalfDenominatorRaw z k = _
  rw [hillPhaseInverseSymbol_apply]
  change (hillPhaseInverseRaw z k*fourierBasis.repr (hillHalfDenominatorL2 z F) k)*hillHalfDenominatorRaw z k = _
  rw [fourierBasis_repr,hillHalfDenominatorL2_coefficient,hillHalfDenominatorBoundedSymbol_apply n hn z hz,
    hillPhaseInverseRaw]
  have hd : (‖z-(freeHillValue k:ℂ)‖:ℂ) ≠ 0 := by
    have hpos := (by exact_mod_cast hn : (0:ℝ) < n).trans_le (freeHillSourceCircle_denominator_ge n hn z hz k)
    exact_mod_cast hpos.ne'
  calc
    _ = ((‖z-(freeHillValue k:ℂ)‖:ℂ)*(hillHalfDenominatorRaw z k*hillHalfDenominatorRaw z k))*
        (z-(freeHillValue k:ℂ))⁻¹*l2Synthesis.symm F k := by ring
    _ = _ := by
      rw [hillHalfDenominatorRaw_mul_self,mul_inv_cancel₀ hd,one_mul]
      change (z-(freeHillValue k:ℂ))⁻¹*fourierBasis.repr F k = _
      rw [fourierBasis_repr]

/-- The ACTUAL free source contour keeps exactly the two signed resonant
Fourier coefficients on EVERY periodic physical L2 input. -/
theorem hillContinuousRieszProjection_zero_coefficient (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (F : CircleL2) (k : ℤ) :
    fourierCoeff (singularHillContinuousRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ) F) k =
      if k.natAbs=n then fourierCoeff F k else 0 := by
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hc : sphere (freeHillValue n:ℂ) (n:ℝ) ⊆ singularHillResolventSet 0 := by
    intro z hz
    have h := mem_singularHillResolventSet_of_halfSandwich_small 0 (by norm_num) (by norm_num) 0 n hn hlog z hz
      (by rw [hillHalfSandwich_zero 0 (by norm_num) (by norm_num) n hn hlog z hz];norm_num)
    simpa only [map_zero] using h
  let L : C(AddCircle (2:ℝ),ℂ) →L[ℂ] ℂ := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).comp continuousFourierCLM
  have hL (f : C(AddCircle (2:ℝ),ℂ)) : L f = fourierCoeff f k := continuousFourierCLM_apply f k
  have hint : CircleIntegrable (fun z => singularHillContinuousResolvent 0 z F) (freeHillValue n:ℂ) (n:ℝ) :=
    ((show ContinuousOn (singularHillContinuousResolvent 0) (sphere (freeHillValue n:ℂ) (n:ℝ)) from
      fun z hz => (analyticAt_singularHillContinuousResolvent 0 z (hc hz)).continuousAt.continuousWithinAt).clm_apply
        continuousOn_const).circleIntegrable hnpos.le
  rw [← hL,singularHillContinuousRieszProjection_integral 0 _ _ hnpos.le hc,map_smul,CircleIntegral.map L hint]
  have he : (∮ z in C((freeHillValue n:ℂ),(n:ℝ)), L (singularHillContinuousResolvent 0 z F)) =
      ∮ z in C((freeHillValue n:ℂ),(n:ℝ)), (z-(freeHillValue k:ℂ))⁻¹ • fourierCoeff F k := by
    apply circleIntegral.integral_congr hnpos.le
    intro z hz
    dsimp only
    rw [hL,hillContinuousResolvent_zero_coefficient n hn hlog z hz]
    rfl
  rw [he,circleIntegral.integral_smul_const]
  by_cases hres : k.natAbs=n
  · have hv : freeHillValue k=freeHillValue n := by
      rcases (hill_resonance_iff n k).mp hres with h | h <;> simp [h]
    rw [hv,circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hnpos),smul_smul,
      inv_mul_cancel₀ (by simp [Real.pi_ne_zero]),one_smul,if_pos hres]
  · have hout : (freeHillValue k:ℂ) ∉ closedBall (freeHillValue n:ℂ) (n:ℝ) := by
      intro hb
      have hd := freeHill_denominator_ge_index hn (freeHillSourceDisk_subset_strip n hn hb) hres
      simp only [sub_self,norm_zero] at hd
      exact hnpos.not_ge hd
    rw [CircleIntegral.integral_sub_inv_eq_zero hnpos.le hout,zero_smul,smul_zero,if_neg hres]

/-- The ACTUAL zero-potential source contour is exactly the source free
projector onto exp(i*pi*n*x) and exp(-i*pi*n*x), on ALL physical L2 data. -/
theorem hillContinuousRieszProjection_zero_fourier_kernel (n : ℕ) (hn : 1 ≤ n)
    (hlog : 1 < Real.log (n:ℝ)) (F : CircleL2) :
    singularHillContinuousRieszProjection 0 (freeHillValue n:ℂ) (n:ℝ) F =
      fourierCoeff F (n:ℤ) • (fourier (n:ℤ) : C(AddCircle (2:ℝ),ℂ))+
        fourierCoeff F (-(n:ℤ)) • (fourier (-(n:ℤ)) : C(AddCircle (2:ℝ),ℂ)) := by
  apply continuousFourierCLM_injective
  ext k
  rw [map_add,map_smul,map_smul]
  simp only [continuousFourierCLM_apply,lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,
    hillContinuousRieszProjection_zero_coefficient n hn hlog,fourierCoeff_fourier,Pi.single_apply,smul_eq_mul]
  by_cases hp : k=(n:ℤ)
  · subst k
    simp [show (n:ℤ) ≠ -(n:ℤ) by omega]
  · by_cases hm : k=-(n:ℤ)
    · subst k
      simp [show -(n:ℤ) ≠ (n:ℤ) by omega]
    · have hres : k.natAbs ≠ n := mt (hill_resonance_iff n k).mp (not_or.mpr ⟨hp,hm⟩)
      simp [hp,hm,hres]

end NLS.KdV
