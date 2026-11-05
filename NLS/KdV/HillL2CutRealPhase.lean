import NLS.KdV.HillL2CutPrimitiveReflection
import NLS.KdV.HillL2RealSourcePhase

/-! # Indexed phases on both real bands of the actual high cut

The source-circle phase propagates to every real point on either side
of the actual gap. The strip boundaries cannot be crossed because the
cut root never vanishes there.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

private theorem real_exterior_mem_cut (c r l u x : ℝ) (hlu : l ≤ u)
    (hx : x ∈ Ioo (c-r) (c+r)) (hext : x < l ∨ u < x) :
    (x : ℂ) ∈ ball (c : ℂ) r \ segment ℝ (l : ℂ) u := by
  refine ⟨?_,?_⟩
  · rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [hx.1,hx.2]
  · intro hs
    obtain ⟨t,ht,he⟩ := by rw [segment_eq_image_lineMap] at hs; exact hs
    have h := congrArg Complex.re he
    simp only [AffineMap.lineMap_apply_module,Complex.real_smul,add_re,mul_re,
      ofReal_re,ofReal_im,mul_zero,sub_zero] at h
    have hnonneg := mul_nonneg ht.1 (sub_nonneg.mpr hlu)
    have hnonneg' := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hlu)
    rcases hext with hext | hext <;> nlinarith

theorem HillRealHighGapPair.real_band_domain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) :
    (∀ x ∈ Ioo (freeHillValue n-7*(n : ℝ)/8) p.left,
      (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right) ∧
    (∀ x ∈ Ioo p.right (freeHillValue n+7*(n : ℝ)/8),
      (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hloc := p.localization q hq n hn (by linarith [norm_nonneg q])
  have hl := abs_le.mp hloc.1
  have hr := abs_le.mp hloc.2
  constructor
  · intro x hx
    exact real_exterior_mem_cut _ _ _ _ x p.ordered ⟨hx.1,by linarith [hx.2]⟩ (Or.inl hx.2)
  · intro x hx
    exact real_exterior_mem_cut _ _ _ _ x p.ordered ⟨by linarith [hx.1],hx.2⟩ (Or.inr hx.1)

theorem HillL2NormalizedCutPrimitive.real_phase_on_connected
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (S : Set ℝ) (hS : IsPreconnected S)
    (hmem : ∀ x ∈ S, (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right)
    (k : ℤ) (a : ℝ) (ha : a ∈ S)
    (hfa : (F a).im ∈ Ioo ((k : ℝ)*Real.pi) (((k : ℝ)+1)*Real.pi)) :
    ∀ x ∈ S, (F x).im ∈ Ioo ((k : ℝ)*Real.pi) (((k : ℝ)+1)*Real.pi) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcont : ContinuousOn (fun x : ℝ => (F x).im) S :=
    continuous_im.comp_continuousOn
      (h.analytic.continuousOn.comp continuous_ofReal.continuousOn hmem)
  apply real_mem_Ioo_of_preconnected_avoids _ S hS hcont _ _ _ a ha hfa
  intro x hx
  have hre := h.re_eq_zero q hq hreal n hn hcut p R F x (hmem x hx)
  have hnx : sinh (F x) ≠ 0 := by
    intro he
    have hz := (h.trace_eq x (hmem x hx)).2
    rw [he,mul_zero] at hz
    exact (h.root_data x ⟨ball_subset_ball (by linarith) (hmem x hx).1,(hmem x hx).2⟩).1 hz.symm
  constructor
  · exact fun he => hnx (sinh_eq_zero_of_re_zero_im_int_pi _ k hre he)
  · intro he
    apply hnx (sinh_eq_zero_of_re_zero_im_int_pi _ (k+1) hre _)
    simpa only [Int.cast_add,Int.cast_one] using he

theorem HillL2NormalizedCutPrimitive.real_band_phases
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (hcut : 16*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F) :
    (∀ x ∈ Ioo (freeHillValue n-7*(n : ℝ)/8) p.left,
      (F x).im ∈ Ioo (-Real.pi*n) (-Real.pi*((n : ℝ)-1))) ∧
    (∀ x ∈ Ioo p.right (freeHillValue n+7*(n : ℝ)/8),
      (F x).im ∈ Ioo (-Real.pi*((n : ℝ)+1)) (-Real.pi*n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hloc := p.localization q hq n hn (by linarith [norm_nonneg q])
  have hl := abs_le.mp hloc.1
  have hr := abs_le.mp hloc.2
  have hsource := hillL2ContinuedPrimitive_high_real_crossing_phases q hq hreal n hn hcut
  have hsphere (x : ℝ) (hx : |x-freeHillValue n| = 3*(n : ℝ)/4) :
      (x : ℂ) ∈ sphere (freeHillValue n : ℂ) (3*(n : ℝ)/4) := by
    simpa only [mem_sphere,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs] using hx
  constructor
  · have hmem (x : ℝ) (hx : x ∈ Ioo (freeHillValue n-7*(n : ℝ)/8) p.left) :
        (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right :=
      real_exterior_mem_cut _ _ _ _ x p.ordered ⟨hx.1,by linarith [hx.2]⟩ (Or.inl hx.2)
    have ha : freeHillValue n-3*(n : ℝ)/4 ∈ Ioo (freeHillValue n-7*(n : ℝ)/8) p.left := by
      constructor <;> linarith
    have hanchor : (F (freeHillValue n-3*(n : ℝ)/4 : ℝ)).im ∈
        Ioo (((-(n : ℤ) : ℤ) : ℝ)*Real.pi) ((((-(n : ℤ) : ℤ) : ℝ)+1)*Real.pi) := by
      rw [h.source _ (hsphere _ (by
        rw [sub_sub_cancel_left,abs_neg,abs_of_pos (by positivity : 0 < 3*(n : ℝ)/4)]))]
      convert! hsource.1 using 2 <;> push_cast <;> ring
    have hp := h.real_phase_on_connected q hq hreal n hn hcut p R F _ isPreconnected_Ioo
      hmem (-(n : ℤ)) _ ha hanchor
    intro x hx
    convert! hp x hx using 2 <;> push_cast <;> ring
  · have hmem (x : ℝ) (hx : x ∈ Ioo p.right (freeHillValue n+7*(n : ℝ)/8)) :
        (x : ℂ) ∈ ball (freeHillValue n : ℂ) (7*(n : ℝ)/8) \ segment ℝ (p.left : ℂ) p.right :=
      real_exterior_mem_cut _ _ _ _ x p.ordered ⟨by linarith [hx.1],hx.2⟩ (Or.inr hx.1)
    have ha : freeHillValue n+3*(n : ℝ)/4 ∈ Ioo p.right (freeHillValue n+7*(n : ℝ)/8) := by
      constructor <;> linarith
    have hanchor : (F (freeHillValue n+3*(n : ℝ)/4 : ℝ)).im ∈
        Ioo (((-(n : ℤ)-1 : ℤ) : ℝ)*Real.pi) ((((-(n : ℤ)-1 : ℤ) : ℝ)+1)*Real.pi) := by
      rw [h.source _ (hsphere _ (by
        rw [add_sub_cancel_left,abs_of_pos (by positivity : 0 < 3*(n : ℝ)/4)]))]
      convert! hsource.2 using 2 <;> push_cast <;> ring
    have hp := h.real_phase_on_connected q hq hreal n hn hcut p R F _ isPreconnected_Ioo
      hmem (-(n : ℤ)-1) _ ha hanchor
    intro x hx
    convert! hp x hx using 2 <;> push_cast <;> ring

end NLS.KdV
