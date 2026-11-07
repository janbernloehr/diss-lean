import NLS.SequenceSpaces.PositiveCartesianComplexification
import NLS.SequenceSpaces.FourierRealZeroSpatialGenerator
import NLS.SequenceSpaces.FourierRealZeroDecomposition
import NLS.SequenceSpaces.RealPairComplexification
import NLS.SequenceSpaces.RealActionReduction
import NLS.SequenceSpaces.QuadraticActionsExponent

/-! Unweighted real Cartesian parameters for the literal signed real
Sobolev space. Their quadratic actions are exactly n^(2s) times the
original signed products. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff

def signedCartesianDecoder (s : ℝ) :
    (Coeff 2 × Coeff 2) →L[ℂ] WeightedCoeff (Weight.signedSobolev s) 2 :=
  (WeightedCoeffPair.signedCartesianCLM s).comp
    ((WeightedCoeffPair.toMax (Weight.positiveSobolev s) 2).symm.toContinuousLinearMap.comp
      (((weightIsometry (Weight.positiveSobolev s) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap).prodMap
        (weightIsometry (Weight.positiveSobolev s) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap))

theorem signedCartesianDecoder_positive (s : ℝ) (x : Coeff 2 × Coeff 2) (k : ℤ) (hk : 0 < k) :
    (signedCartesianDecoder s x).val k =
      (x.1 k-I*x.2 k)/((Real.sqrt 2:ℂ)*(Weight.positiveSobolev s k:ℂ)) := by
  change (WeightedCoeffPair.signedCartesianCLM s _).val k = _
  rw [WeightedCoeffPair.signedCartesianCLM_positive s _ k hk]
  change (x.1 k/(Weight.positiveSobolev s k:ℂ)-I*(x.2 k/(Weight.positiveSobolev s k:ℂ)))/(Real.sqrt 2:ℂ)=_
  ring

theorem signedCartesianDecoder_negative (s : ℝ) (x : Coeff 2 × Coeff 2) (k : ℤ) (hk : 0 < k) :
    (signedCartesianDecoder s x).val (-k) =
      (x.1 k+I*x.2 k)/((Real.sqrt 2:ℂ)*(Weight.positiveSobolev s k:ℂ)) := by
  change (WeightedCoeffPair.signedCartesianCLM s _).val (-k) = _
  rw [WeightedCoeffPair.signedCartesianCLM_negative s _ k hk]
  change (x.1 k/(Weight.positiveSobolev s k:ℂ)+I*(x.2 k/(Weight.positiveSobolev s k:ℂ)))/(Real.sqrt 2:ℂ)=_
  ring

theorem signedCartesianDecoder_zero (s : ℝ) (x : Coeff 2 × Coeff 2) :
    (signedCartesianDecoder s x).val 0=0 := WeightedCoeffPair.signedCartesianCLM_zero s _

theorem signedCartesianDecoder_real (s : ℝ) (x : RealCoeff 2 × RealCoeff 2) (k : ℤ) :
    (signedCartesianDecoder s (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x)).val (-k) =
      (starRingEnd ℂ) ((signedCartesianDecoder s (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x)).val k) := by
  let J := (RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)
  have hpos (j : ℤ) (hj : 0 < j) :
      (signedCartesianDecoder s (J x)).val (-j) = (starRingEnd ℂ) ((signedCartesianDecoder s (J x)).val j) := by
    rw [signedCartesianDecoder_negative s _ j hj,signedCartesianDecoder_positive s _ j hj]
    change ((x.1 j:ℂ)+I*(x.2 j:ℂ))/_ = (starRingEnd ℂ) (((x.1 j:ℂ)-I*(x.2 j:ℂ))/_)
    simp only [map_div₀,map_sub,map_mul,conj_ofReal,conj_I,neg_mul,sub_neg_eq_add]
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have h := congrArg (starRingEnd ℂ) (hpos (-k) (by omega))
    simpa only [neg_neg,Complex.conj_conj] using h.symm
  · subst k
    simp only [neg_zero,signedCartesianDecoder_zero,map_zero]
  · exact hpos k hk

def signedRealCartesianDecoder (s : ℝ) :
    (RealCoeff 2 × RealCoeff 2) →L[ℝ] fourierRealZeroSubmodule (Weight.signedSobolev s) 2 :=
  (fourierRealZeroFullProjection (Weight.signedSobolev s) (Weight.signedSobolev_neg s)).comp
    ((signedCartesianDecoder s).restrictScalars ℝ |>.comp
      ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)))

theorem signedRealCartesianDecoder_coe (s : ℝ) (x : RealCoeff 2 × RealCoeff 2) :
    (signedRealCartesianDecoder s x).val.val =
      signedCartesianDecoder s (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x) := by
  let a := signedCartesianDecoder s (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) x)
  have he := fourierRealZeroFullProjection_inclusion (Weight.signedSobolev s) (Weight.signedSobolev_neg s)
    (⟨⟨a,signedCartesianDecoder_zero s _⟩,signedCartesianDecoder_real s x⟩ :
      fourierRealZeroSubmodule (Weight.signedSobolev s) 2)
  exact congrArg (fun y : fourierRealZeroSubmodule (Weight.signedSobolev s) 2 => y.val.val) he

theorem signedRealCartesianDecoder_products (s : ℝ) (x : RealCoeff 2 × RealCoeff 2)
    (k : ℤ) (hk : 0 < k) :
    (signedRealCartesianDecoder s x).val.val.val k * (signedRealCartesianDecoder s x).val.val.val (-k) =
      (RealCoeff.pairAction x k:ℂ)/(Weight.positiveSobolev s k:ℂ)^2 := by
  rw [signedRealCartesianDecoder_coe,signedCartesianDecoder_positive s _ k hk,
    signedCartesianDecoder_negative s _ k hk]
  change (((x.1 k:ℂ)-I*(x.2 k:ℂ))/_)*(((x.1 k:ℂ)+I*(x.2 k:ℂ))/_)=_
  have hsq : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  simp only [RealCoeff.pairAction,ofReal_div,ofReal_add,ofReal_pow,ofReal_ofNat]
  field_simp
  ring_nf
  simp only [hsq,I_sq]
  ring

def signedRealCartesianParameters (s : ℝ) :
    fourierRealZeroSubmodule (Weight.signedSobolev s) 2 →L[ℝ] (RealCoeff 2 × RealCoeff 2) :=
  (((Real.sqrt 2:ℝ) • Coeff.reCLM 2).prod ((-Real.sqrt 2:ℝ) • Coeff.imCLM 2)).comp
    (((weightIsometry (Weight.signedSobolev s) 2).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
      (((zeroModeSubmodule (Weight.signedSobolev s) 2).subtypeL.restrictScalars ℝ).comp
        (fourierRealZeroSubmodule (Weight.signedSobolev s) 2).subtypeL))

theorem signedRealCartesianParameters_fst (s : ℝ)
    (z : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) (k : ℤ) :
    (signedRealCartesianParameters s z).1 k = Real.sqrt 2*Weight.signedSobolev s k*(z.val.val.val k).re := by
  change Real.sqrt 2*((Weight.signedSobolev s k:ℂ)*z.val.val.val k).re = _
  simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
  ring

theorem signedRealCartesianParameters_snd (s : ℝ)
    (z : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) (k : ℤ) :
    (signedRealCartesianParameters s z).2 k = -Real.sqrt 2*Weight.signedSobolev s k*(z.val.val.val k).im := by
  change -Real.sqrt 2*((Weight.signedSobolev s k:ℂ)*z.val.val.val k).im = _
  simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero]
  ring

/-- The Cartesian decoder is a split surjection onto the complete
physical real Sobolev target, preserving the original signed coefficients. -/
theorem signedRealCartesianDecoder_parameters (s : ℝ)
    (z : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) :
    signedRealCartesianDecoder s (signedRealCartesianParameters s z)=z := by
  let x := signedRealCartesianParameters s z
  have hpos (k : ℤ) (hk : 0 < k) : (signedRealCartesianDecoder s x).val.val.val k=z.val.val.val k := by
    rw [signedRealCartesianDecoder_coe,signedCartesianDecoder_positive s _ k hk]
    change ((x.1 k:ℂ)-I*(x.2 k:ℂ))/_ = _
    have hnum : (x.1 k:ℂ)-I*(x.2 k:ℂ) =
        ((Real.sqrt 2:ℂ)*(Weight.positiveSobolev s k:ℂ))*z.val.val.val k := by
      dsimp only [x]
      rw [signedRealCartesianParameters_fst,signedRealCartesianParameters_snd,
        Weight.signedSobolev_positive s k hk]
      push_cast
      calc
        _ = ((Real.sqrt 2:ℂ)*(Weight.positiveSobolev s k:ℂ))*
            (((z.val.val.val k).re:ℂ)+((z.val.val.val k).im:ℂ)*I) := by ring
        _ = _ := by rw [Complex.re_add_im]
    rw [hnum,mul_div_cancel_left₀]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
      ((Weight.positiveSobolev s).complex_ne_zero k)
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [← neg_neg k,(signedRealCartesianDecoder s x).property (-k),hpos (-k) (by omega),z.property (-k)]
  · subst k
    exact (signedRealCartesianDecoder s x).val.property.trans z.val.property.symm
  · exact hpos k hk

/-- The complete normalized action sequence has the exact physical
signed-product formula, including the zero and negative modes. -/
theorem signedRealCartesianParameters_actions (s : ℝ)
    (z : fourierRealZeroSubmodule (Weight.signedSobolev s) 2) (k : ℤ) :
    quadraticActionsExponent (q := 1)
        (((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
          (signedRealCartesianParameters s z)) k =
      (Weight.signedSobolev s k:ℂ)^2*z.val.val.val k*z.val.val.val (-k) := by
  rw [quadraticActionsExponent_apply]
  change (((signedRealCartesianParameters s z).1 k:ℂ)^2+
    ((signedRealCartesianParameters s z).2 k:ℂ)^2)/2 = _
  rw [signedRealCartesianParameters_fst,signedRealCartesianParameters_snd,z.property k]
  let u : ℂ := z.val.val.val k
  let v : ℝ := Weight.signedSobolev s k
  change (((Real.sqrt 2*v*u.re:ℝ):ℂ)^2+((-Real.sqrt 2*v*u.im:ℝ):ℂ)^2)/2 =
    (v:ℂ)^2*u*(starRingEnd ℂ) u
  have hmul : u*(starRingEnd ℂ) u = (u.re:ℂ)^2+(u.im:ℂ)^2 := by
    apply Complex.ext <;> simp only [mul_re,mul_im,conj_re,conj_im,
      add_re,add_im,ofReal_re,ofReal_im,pow_two] <;> ring
  rw [show (v:ℂ)^2*u*(starRingEnd ℂ) u=(v:ℂ)^2*(u*(starRingEnd ℂ) u) by ring,hmul]
  push_cast
  have hsq : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  ring_nf
  rw [hsq]
  ring

end NLS.WeightedCoeff
