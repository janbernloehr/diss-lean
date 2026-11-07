import NLS.SequenceSpaces.PeriodOneMassSobolevInverse
import NLS.SequenceSpaces.HilbertSobolevEmbedding
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.YoungConvolution

/-! # Explicit analytic fractional recovery from a one-third-order lift

H^(1/3) embeds into ell^(4/3), so its quadratic Fourier convolution is L2.
The massive first-order inverse then recovers the exact requested order.
-/
noncomputable section
open Complex NLS.WeightedCoeff
open scoped ENNReal
namespace NLS

def l2ToNegativeSobolev (r : ℝ) (hr : 0 ≤ r) :
    Coeff 2 →L[ℂ] WeightedCoeff (Weight.sobolev (-r)) 2 :=
  (sobolevInclusion (show -r ≤ 0 by linarith)).comp
    (weightIsometry (Weight.sobolev 0) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem l2ToNegativeSobolev_apply (r : ℝ) (hr : 0 ≤ r) (u : Coeff 2) (k : ℤ) :
    (l2ToNegativeSobolev r hr u).val k = u k := by
  change (sobolevInclusion (show -r ≤ 0 by linarith) ((weightIsometry (Weight.sobolev 0) 2).symm u)).val k = _
  rw [sobolevInclusion_apply]
  change u k/(Weight.sobolev 0 k : ℂ) = u k
  simp only [Weight.sobolev_zero_apply,ofReal_one,div_one]

private abbrev miuraThirdP43 : ℝ≥0∞ := ENNReal.ofReal (4/3 : ℝ)
private instance : Fact (1 ≤ miuraThirdP43) := ⟨by norm_num [miuraThirdP43]⟩

private theorem miuraThirdYoung : YoungRelation miuraThirdP43 miuraThirdP43 2 := by
  unfold YoungRelation
  apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by norm_num [miuraThirdP43])).mp
  rw [ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_add (by norm_num [miuraThirdP43]) (by norm_num [miuraThirdP43])]
  norm_num [miuraThirdP43]

def miuraThirdToFourThirds :
    WeightedCoeff (Weight.sobolev (1/3)) 2 →L[ℂ] Coeff (ENNReal.ofReal (4/3 : ℝ)) :=
  hilbertSobolevInclusion (1/3) (4/3) (by norm_num) (by norm_num) (by norm_num)

theorem miuraThirdToFourThirds_apply (u : WeightedCoeff (Weight.sobolev (1/3)) 2) (k : ℤ) :
    miuraThirdToFourThirds u k = u.val k :=
  hilbertSobolevInclusion_apply _ _ _ _ _ u k

def miuraThirdL2Product (u : WeightedCoeff (Weight.sobolev (1/3)) 2) : Coeff 2 :=
  Coeff.youngConvolutionCLM miuraThirdYoung (miuraThirdToFourThirds u) (miuraThirdToFourThirds u)

theorem miuraThirdL2Product_apply (u : WeightedCoeff (Weight.sobolev (1/3)) 2) (k : ℤ) :
    miuraThirdL2Product u k = ∑' j : ℤ, u.val (k-j)*u.val j := by
  simp only [miuraThirdL2Product,Coeff.youngConvolutionCLM_apply,
    Coeff.youngConvolution_apply,miuraThirdToFourThirds_apply]

theorem analyticAt_miuraThirdL2Product (u : WeightedCoeff (Weight.sobolev (1/3)) 2) :
    AnalyticAt ℂ miuraThirdL2Product u :=
  ((Coeff.youngConvolutionCLM miuraThirdYoung).analyticAt_bilinear _).comp₂
    (miuraThirdToFourThirds.analyticAt u) (miuraThirdToFourThirds.analyticAt u)

def fractionalMiuraRecovery (r : ℝ) (hr : 0 ≤ r) (c : ℂ)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (u : WeightedCoeff (Weight.sobolev (1/3)) 2) : WeightedCoeff (Weight.sobolev (1-r)) 2 :=
  sobolevInclusion (show 1-r ≤ -r+1 by linarith)
    (periodOneMassSobolevInverse (-r) 0 2
      (q+single (Weight.sobolev (-r)) 0 c+
        l2ToNegativeSobolev r hr (sobolevToL2 (by norm_num) u)-
        l2ToNegativeSobolev r hr (miuraThirdL2Product u)))

theorem fractionalMiuraRecovery_apply (r : ℝ) (hr : 0 ≤ r) (c : ℂ)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (u : WeightedCoeff (Weight.sobolev (1/3)) 2) (k : ℤ) :
    (fractionalMiuraRecovery r hr c q u).val k =
      (periodOneMassSymbol 0 k)⁻¹*(q.val k+(Pi.single (0:ℤ) c : ℤ → ℂ) k+u.val k-
        ∑' j : ℤ, u.val (k-j)*u.val j) := by
  simp only [fractionalMiuraRecovery,sobolevInclusion_apply,periodOneMassSobolevInverse_apply,
    WeightedCoeff.sub_val,WeightedCoeff.add_val,single_val,l2ToNegativeSobolev_apply,
    sobolevToL2_apply,miuraThirdL2Product_apply]

theorem analyticAt_fractionalMiuraRecovery (r : ℝ) (hr : 0 ≤ r) (c : ℂ)
    (p : WeightedCoeff (Weight.sobolev (-r)) 2 × WeightedCoeff (Weight.sobolev (1/3)) 2) :
    AnalyticAt ℂ (fun x => fractionalMiuraRecovery r hr c x.1 x.2) p := by
  have hu : AnalyticAt ℂ (fun x : WeightedCoeff (Weight.sobolev (-r)) 2 ×
      WeightedCoeff (Weight.sobolev (1/3)) 2 =>
      l2ToNegativeSobolev r hr (sobolevToL2 (by norm_num) x.2)) p := ((l2ToNegativeSobolev r hr).analyticAt _).comp
    (((sobolevToL2 (s := (1/3)) (by norm_num)).analyticAt _).comp analyticAt_snd)
  have hy : AnalyticAt ℂ (fun x : WeightedCoeff (Weight.sobolev (-r)) 2 ×
      WeightedCoeff (Weight.sobolev (1/3)) 2 =>
      l2ToNegativeSobolev r hr (miuraThirdL2Product x.2)) p := ((l2ToNegativeSobolev r hr).analyticAt _).comp
    ((analyticAt_miuraThirdL2Product p.2).comp analyticAt_snd)
  have hc : AnalyticAt ℂ (fun _ : WeightedCoeff (Weight.sobolev (-r)) 2 ×
      WeightedCoeff (Weight.sobolev (1/3)) 2 => single (p := 2) (Weight.sobolev (-r)) 0 c) p := analyticAt_const
  have hb := ((analyticAt_fst.add hc).add hu).sub hy
  exact ((sobolevInclusion (show 1-r ≤ -r+1 by linarith)).analyticAt _).comp
    (((periodOneMassSobolevInverse (-r) 0 2).analyticAt _).comp hb)

theorem fractionalMiuraRecovery_eq_of_equation (r : ℝ) (hr : 0 ≤ r) (c : ℂ)
    (q : WeightedCoeff (Weight.sobolev (-r)) 2)
    (u : WeightedCoeff (Weight.sobolev (1/3)) 2)
    (heq : ∀ k, 2*I*(Real.pi:ℂ)*k*u.val k+∑' j : ℤ, u.val (k-j)*u.val j =
      q.val k+(Pi.single (0:ℤ) c : ℤ → ℂ) k) (k : ℤ) :
    (fractionalMiuraRecovery r hr c q u).val k = u.val k := by
  rw [fractionalMiuraRecovery_apply]
  have hm : q.val k+(Pi.single (0:ℤ) c : ℤ → ℂ) k+u.val k-
      (∑' j : ℤ, u.val (k-j)*u.val j) = periodOneMassSymbol 0 k*u.val k := by
    simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,ofReal_one]
    linear_combination -(heq k)
  rw [hm,← mul_assoc,inv_mul_cancel₀ (periodOneMassSymbol_ne_zero 0 k),one_mul]

end NLS
