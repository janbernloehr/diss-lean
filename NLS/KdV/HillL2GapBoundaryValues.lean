import NLS.KdV.HillL2CutUnitOrientation
import NLS.ComplexAnalysis.RealEndpointRootBoundary

/-! # The actual upper and lower Hill gap boundary values

The source-normalized shifted primitive has the positive arcosh profile
as its upper boundary value and the negative profile as its lower value.
The limits allow arbitrary approaches through each nonreal half-plane,
including at the endpoints. These signs fix the orientation required
by the contour-to-real action formula.
-/

noncomputable section
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
namespace NLS.KdV

theorem HillL2NormalizedCutPrimitive.gap_boundary_values
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (x : ℝ) (hx : x ∈ Icc p.left p.right) :
    Tendsto (fun z => F z+I*(n : ℂ)*Real.pi) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ)) ∧
    Tendsto (fun z => F z+I*(n : ℂ)*Real.pi) (𝓝[{z : ℂ | z.im < 0}] (x : ℂ))
      (𝓝 (-(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hab : p.left < p.right := lt_of_le_of_ne p.ordered hopen
  let X := hillL2CutPrimitiveSquare n p.left p.right F
  let Q := twoZeroQuotient X p.left p.right
  let Ω := ball (freeHillValue n : ℂ) (7*(n : ℝ)/8)
  obtain ⟨H,hH,hHsq,hmatch⟩ := h.exists_unit_root q hq hreal n hn hcut p hopen R F
  have hHsign := h.unit_root_real_sign q hq hreal n hn hcut p hopen R F H hH hHsq hmatch
  have hloc := p.localization q hq n (by omega) hcut
  have hxΩ : (x : ℂ) ∈ Ω := by
    rw [mem_ball,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [hx.1,hx.2,(abs_le.mp hloc.1).1,(abs_le.mp hloc.2).2]
  obtain ⟨p',hl,hr⟩ := hillRealLabels_high_pair q hq hreal n hn hcut
  have hu := p.endpoints_unique _ n (by omega) p'
  have hlabelL : hillRealLabels q hq hreal (2*n-1) = p.left := hl.trans hu.1.symm
  have hlabelR : hillRealLabels q hq hreal (2*n) = p.right := hr.trans hu.2.symm
  have hxlabels : x ∈ Icc (hillRealLabels q hq hreal (2*n-1)) (hillRealLabels q hq hreal (2*n)) := by
    rwa [hlabelL,hlabelR]
  have hPnonneg := hillRealGapProfile_nonneg q hq hreal n (by omega) x hxlabels
  have hPends := hillRealGapProfile_endpoints q hq hreal n (by omega)
  rw [hlabelL,hlabelR] at hPends
  obtain ⟨_,_,hXL,hXR⟩ := h.square_extension q hq hreal n hn hcut p hopen R F
  have hXP : X x = ((hillRealGapProfile (SpectralWeight.one.toCoeff q) n x)^2 : ℝ) := by
    by_cases hxl : x = p.left
    · subst x
      simpa only [hPends.1,zero_pow (by norm_num : 2 ≠ 0),ofReal_zero] using hXL
    by_cases hxr : x = p.right
    · subst x
      simpa only [hPends.2,zero_pow (by norm_num : 2 ≠ 0),ofReal_zero] using hXR
    exact (h.square_gap_profile q hq hreal n hn hcut p hopen R F x
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl),lt_of_le_of_ne hx.2 hxr⟩).2
  obtain ⟨_,hfactor,_⟩ := h.square_deflated_unit q hq hreal n hn hcut p hopen R F
  let r : ℝ := Real.sqrt ((x-p.left)*(p.right-x))
  let B : ℂ := (-I*(r : ℂ))*H x
  have hrsq : r^2 = (x-p.left)*(p.right-x) :=
    Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
  have hePow : (-I*(r : ℂ))^2 = ((x : ℂ)-p.left)*((x : ℂ)-p.right) := by
    rw [mul_pow,neg_sq,I_sq,← ofReal_pow,hrsq]
    push_cast
    ring
  have hBsq : B^2 = (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ)^2 := by
    calc
      _ = X x := by
        dsimp only [B]
        rw [mul_pow,hePow,(hHsq x hxΩ).2]
        exact (hfactor (x : ℂ)).symm
      _ = _ := by simpa only [ofReal_pow] using hXP
  have hBre : 0 ≤ B.re := by
    have he : B.re = r*(H x).im := by
      dsimp only [B]
      simp only [mul_re,mul_im,neg_re,I_re,neg_zero,neg_im,I_im,ofReal_re,ofReal_im,
        zero_mul,mul_zero,sub_zero,zero_add,neg_one_mul]
      ring
    rw [he]
    exact mul_nonneg (Real.sqrt_nonneg _) (hHsign x hxΩ).2.le
  have hBvalue : B = (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by
    rcases eq_or_eq_neg_of_sq_eq_sq B (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) hBsq with he | he
    · exact he
    · have hr := congrArg Complex.re he
      simp only [neg_re,ofReal_re] at hr
      have hp0 : hillRealGapProfile (SpectralWeight.one.toCoeff q) n x = 0 := by linarith
      simpa only [hp0,ofReal_zero,neg_zero] using he
  have hBvalueL : (I*(r : ℂ))*H x = -(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by
    calc
      _ = -B := by dsimp only [B]; ring
      _ = _ := by rw [hBvalue]
  have heplim := endpointRoot_real_gap_limits p.left p.right x hab hx
  have hlimH : Tendsto H (𝓝 (x : ℂ)) (𝓝 (H x)) := (hH x hxΩ).continuousAt.tendsto
  have hupper : Tendsto (fun z => F z+I*(n : ℂ)*Real.pi)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 B) := by
    apply (heplim.1.mul (hlimH.mono_left nhdsWithin_le_nhds)).congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (isOpen_ball.mem_nhds hxΩ)] with z hz hzΩ
    exact (hmatch z ⟨hzΩ,not_mem_real_segment_of_im_ne_zero _ _ z (ne_of_gt hz)⟩).symm
  have hlower : Tendsto (fun z => F z+I*(n : ℂ)*Real.pi)
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) (𝓝 ((I*(r : ℂ))*H x)) := by
    apply (heplim.2.mul (hlimH.mono_left nhdsWithin_le_nhds)).congr'
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (isOpen_ball.mem_nhds hxΩ)] with z hz hzΩ
    exact (hmatch z ⟨hzΩ,not_mem_real_segment_of_im_ne_zero _ _ z (ne_of_lt hz)⟩).symm
  exact ⟨hBvalue ▸ hupper,hBvalueL ▸ hlower⟩

/-- The literal upper-minus-lower jump of the unshifted primitive is
twice the positive real gap profile. The constant index shift cancels. -/
theorem HillL2NormalizedCutPrimitive.gap_vertical_jump
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 2 ≤ n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (p : HillRealHighGapPair (SpectralWeight.one.toCoeff q) n) (hopen : p.left ≠ p.right)
    (R F : ℂ → ℂ)
    (h : HillL2NormalizedCutPrimitive (SpectralWeight.one.toCoeff q) n p R F)
    (x : ℝ) (hx : x ∈ Icc p.left p.right) :
    Tendsto (fun ε : ℝ => F ((x : ℂ)+(ε : ℂ)*I)-F ((x : ℂ)-(ε : ℂ)*I))
      (𝓝[>] 0) (𝓝 (2*(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ))) := by
  have hu : Tendsto (fun ε : ℝ => (x : ℂ)+(ε : ℂ)*I) (𝓝[>] 0)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun ε : ℝ => (x : ℂ)+(ε : ℂ)*I) 0 := by fun_prop
      simpa only [ofReal_zero,zero_mul,add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,zero_add,add_zero] using
        (show (0 : ℝ) < ε from hε)
  have hl : Tendsto (fun ε : ℝ => (x : ℂ)-(ε : ℂ)*I) (𝓝[>] 0)
      (𝓝[{z : ℂ | z.im < 0}] (x : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : ContinuousAt (fun ε : ℝ => (x : ℂ)-(ε : ℂ)*I) 0 := by fun_prop
      simpa only [ofReal_zero,zero_mul,sub_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      simpa only [sub_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_sub] using
        neg_neg_of_pos hε
  have hb := h.gap_boundary_values q hq hreal n hn hcut p hopen R F x hx
  have hd := (hb.1.comp hu).sub (hb.2.comp hl)
  dsimp only [Function.comp_def] at hd
  have he (ε : ℝ) :
      (F ((x : ℂ)+(ε : ℂ)*I)+I*(n : ℂ)*Real.pi)-
        (F ((x : ℂ)-(ε : ℂ)*I)+I*(n : ℂ)*Real.pi) =
      F ((x : ℂ)+(ε : ℂ)*I)-F ((x : ℂ)-(ε : ℂ)*I) := by ring
  simp_rw [he] at hd
  have hv : (hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ)-
      -(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) =
      2*(hillRealGapProfile (SpectralWeight.one.toCoeff q) n x : ℂ) := by ring
  rwa [hv] at hd

end NLS.KdV
