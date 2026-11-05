import NLS.KdV.HillL2CutPrimitiveUnit
import NLS.ZakharovShabat.SourceStandardRootRealExteriorSign

/-! # The physical sign of the analytic Hill primitive unit root

The deflated square unit is real and negative on the real diameter.
Its analytic root is therefore imaginary and never zero there. Matching
the actual shifted primitive on the right real band selects positive
imaginary part. Only the algebraic standard-root sign is reused from the
spectral library; no NLS real-type property is assumed for a Hill pair.
-/

noncomputable section
open Set Metric Complex
open scoped ComplexConjugate
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.unit_root_real_sign
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (H : ℂ → ℂ) (hH : AnalyticOnNhd ℂ H (ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)))
    (hHsq : ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8), H z ≠ 0 ∧
      H z^2 = twoZeroQuotient (hillL2CutPrimitiveSquare n p.left p.right F) p.left p.right z)
    (hmatch : ∀ z ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right,
      F z+I*(n : ℂ)*Real.pi = endpointRoot p.left p.right z*H z) :
    ∀ x : ℝ, (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) →
      (H x).re = 0 ∧ 0 < (H x).im := by
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  let Q := twoZeroQuotient X p.left p.right
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  let S := Ioo (freeHillValue n-7*(n : ℝ)/8) (freeHillValue n+7*(n : ℝ)/8)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hab : p.left < p.right := lt_of_le_of_ne p.ordered hopen
  have hloc := p.localization q hq n (by omega) (by linarith [norm_nonneg q])
  have hl := abs_le.mp hloc.1
  have hr := abs_le.mp hloc.2
  have hmem (x : ℝ) : x ∈ S ↔ (x : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_lt]
    dsimp only [S,mem_Ioo]
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  obtain ⟨hQ,hfactor,hunit⟩ := h.square_deflated_unit q hq hreal n hn hcut p hopen R F
  have hconj : ∀ z ∈ Ω, Q (conj z) = conj (Q z) :=
    real_two_zero_unit_conj X Q _ _ p.left p.right hQ.continuousOn
      (h.square_conj q hq hreal n hn hcut p hopen R F) (fun z _ => hfactor z)
  have hQim (x : ℝ) (hx : x ∈ S) : (Q x).im = 0 := by
    have he := congrArg Complex.im (hconj x ((hmem x).mp hx))
    simp only [conj_ofReal,conj_im] at he
    linarith
  have hQne (x : ℝ) (hx : x ∈ S) : (Q x).re ≠ 0 := by
    intro he
    apply hunit x ((hmem x).mp hx)
    exact Complex.ext he (hQim x hx)
  let x0 : ℝ := (p.left+p.right)/2
  have hx0gap : x0 ∈ Ioo p.left p.right := by dsimp only [x0]; constructor <;> linarith
  have hx0 : x0 ∈ S := by dsimp only [S,mem_Ioo,x0]; constructor <;> linarith
  have hXpos : 0 < (X x0).re :=
    (h.square_gap_profile q hq hreal n hn hcut p hopen R F x0 hx0gap).1
  have hf0 := congrArg Complex.re (hfactor (x0 : ℂ))
  simp only [mul_re,mul_im,sub_re,ofReal_re,sub_im,ofReal_im,sub_self,mul_zero,zero_mul,sub_zero,
    add_zero] at hf0
  change (X x0).re = (x0-p.left)*(x0-p.right)*(Q x0).re at hf0
  have hpoly : (x0-p.left)*(x0-p.right) < 0 :=
    mul_neg_of_pos_of_neg (sub_pos.mpr hx0gap.1) (sub_neg.mpr hx0gap.2)
  have hQ0 : (Q x0).re < 0 := by
    by_contra he
    have hm := mul_nonpos_of_nonpos_of_nonneg hpoly.le (not_lt.mp he)
    nlinarith
  have hQc : ContinuousOn (fun x : ℝ => (Q x).re) S :=
    continuous_re.comp_continuousOn (hQ.continuousOn.comp continuous_ofReal.continuousOn
      (fun x hx => (hmem x).mp hx))
  have hQneg (x : ℝ) (hx : x ∈ S) : (Q x).re < 0 :=
    negative_on_preconnected_of_nonzero _ S isPreconnected_Ioo hQc hQne x0 hx0 hQ0 x hx
  have hHpure (x : ℝ) (hx : x ∈ S) : (H x).re = 0 ∧ (H x).im ≠ 0 := by
    have hs := (hHsq x ((hmem x).mp hx)).2
    have hre := congrArg Complex.re hs
    have him := congrArg Complex.im hs
    change (H x^2).re = (Q x).re at hre
    change (H x^2).im = (Q x).im at him
    simp only [pow_two,mul_re,mul_im] at hre him
    rw [hQim x hx] at him
    have hIm : (H x).im ≠ 0 := by
      intro he
      rw [he,mul_zero,sub_zero] at hre
      nlinarith [hQneg x hx,sq_nonneg (H x).re]
    have hm : (H x).re*(H x).im = 0 := by nlinarith
    exact ⟨(mul_eq_zero.mp hm).resolve_right hIm,hIm⟩
  let a : ℝ := freeHillValue n+3*(n : ℝ)/4
  have ha : a ∈ S := by dsimp only [a,S,mem_Ioo]; constructor <;> linarith
  have haband : a ∈ Ioo p.right (freeHillValue n+7*(n : ℝ)/8) := by
    dsimp only [a,mem_Ioo]
    constructor <;> linarith
  have haU := (p.real_band_domain q hq n (by omega) hcut).2 a haband
  have hphase := (h.real_band_phases q hq hreal n (by omega) hcut p R F).2 a haband
  have himIndex : (I*(n : ℂ)*Real.pi).im = Real.pi*n := by
    simp only [mul_im,mul_re,I_re,I_im,natCast_re,natCast_im,ofReal_re,ofReal_im,
      mul_zero,zero_mul,sub_zero,zero_add,one_mul]
    ring
  have hFn : (F a+I*(n : ℂ)*Real.pi).im < 0 := by rw [add_im,himIndex]; linarith [hphase.2]
  have hE : (endpointRoot p.left p.right (a : ℂ)).re < 0 := by
    simpa only [endpointRoot,ofReal_div,ofReal_add,ofReal_sub,ofReal_pow,ofReal_ofNat] using
      NLS.ZakharovShabat.normalizedStandardRoot_re_neg_of_gt_rightEndpoint p.left p.right a p.ordered haband.1
  have hma := congrArg Complex.im (hmatch a haU)
  simp only [mul_im] at hma
  rw [(hHpure a ha).1,mul_zero,add_zero] at hma
  have hHa : 0 < (H a).im := by
    by_contra he
    have hm := mul_nonneg_of_nonpos_of_nonpos hE.le (not_lt.mp he)
    linarith
  have hHc : ContinuousOn (fun x : ℝ => -(H x).im) S :=
    (continuous_im.comp_continuousOn (hH.continuousOn.comp continuous_ofReal.continuousOn
      (fun x hx => (hmem x).mp hx))).neg
  intro x hx
  have hxS := (hmem x).mpr hx
  have hsign := negative_on_preconnected_of_nonzero (fun x : ℝ => -(H x).im) S
    isPreconnected_Ioo hHc (fun x hx => neg_ne_zero.mpr (hHpure x hx).2) a ha (by linarith) x hxS
  exact ⟨(hHpure x hxS).1,by linarith⟩

end NLS.KdV
