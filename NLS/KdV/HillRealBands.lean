import NLS.KdV.HillL2Conjugation
import NLS.KdV.HillRealTraceParity

/-! # The actual real Hill trace in every open spectral band

Intrinsic ordering excludes characteristic roots between consecutive
labels. The physical endpoint parity and the intermediate value theorem
then place the actual trace strictly between -2 and 2 in every open
band, including the band adjacent to the lowest energy.
-/

noncomputable section
open Set Complex
namespace NLS.KdV

theorem hillL2Radicand_ne_zero_between_labels
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (j : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hreal j) (hillRealLabels q hq hreal (j+1))) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) x ≠ 0 := by
  intro hd
  obtain ⟨k,hk⟩ := (hillRealLabels_root_iff q hq hreal (x : ℂ)).mp hd
  have he : x = hillRealLabels q hq hreal k := Complex.ofReal_inj.mp hk
  have hm := monotone_hillRealLabels q hq hreal
  rcases le_or_gt k j with hkj | hjk
  · have hh := hm hkj
    linarith [hx.1]
  · have hh := hm (show j+1 ≤ k by omega)
    linarith [hx.2]

theorem exists_hillL2Discriminant_zero_in_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) :
    ∃ x ∈ Ioo (hillRealLabels q hq hreal (2*n)) (hillRealLabels q hq hreal (2*n+1)),
      hillL2Discriminant (SpectralWeight.one.toCoeff q) x = 0 := by
  let a := hillRealLabels q hq hreal (2*n)
  let b := hillRealLabels q hq hreal (2*n+1)
  let s : ℂ := (-1)^n
  let g : ℝ → ℝ := fun x => (s*hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re
  have hs : s^2 = 1 := by
    dsimp only [s]
    rw [← pow_mul,Nat.mul_comm n 2,pow_mul]
    norm_num
  have hsne : s ≠ 0 := pow_ne_zero n (by norm_num)
  have hsreal : s = (((-1 : ℝ)^n : ℝ) : ℂ) := by simp [s]
  have haD : hillL2Discriminant (SpectralWeight.one.toCoeff q) a = 2*s := by
    simpa only [a,show (2*n+1)/2 = n by omega] using hillRealLabels_trace_parity q hq hreal (2*n)
  have hbD : hillL2Discriminant (SpectralWeight.one.toCoeff q) b = -2*s := by
    have h := hillRealLabels_trace_parity q hq hreal (2*n+1)
    rw [show (2*n+1+1)/2 = n+1 by omega,pow_succ] at h
    change hillL2Discriminant (SpectralWeight.one.toCoeff q) b = _ at h
    dsimp only [s]
    rw [h]
    ring
  have ha : g a = 2 := by
    dsimp only [g]
    rw [haD,show s*(2*s) = 2*s^2 by ring,hs]
    norm_num
  have hb : g b = -2 := by
    dsimp only [g]
    rw [hbD,show s*(-2*s) = -2*s^2 by ring,hs]
    norm_num
  have hab : a < b := hillRealLabels_band_strict q hq hreal n
  have hD : Continuous (fun x : ℝ => hillL2Discriminant (SpectralWeight.one.toCoeff q) x) :=
    (analyticOnNhd_hillL2Discriminant _).continuous.comp Complex.continuous_ofReal
  have hg : Continuous g := Complex.continuous_re.comp
    ((continuous_const : Continuous (fun _ : ℝ => s)).mul hD)
  obtain ⟨x,hx,hzero⟩ := intermediate_value_Icc' hab.le hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g b) (g a) by rw [ha,hb]; norm_num)
  have hxa : a < x := lt_of_le_of_ne hx.1 (by intro he; rw [← he,ha] at hzero; norm_num at hzero)
  have hxb : x < b := lt_of_le_of_ne hx.2 (by intro he; rw [he,hb] at hzero; norm_num at hzero)
  have hprod : s*hillL2Discriminant (SpectralWeight.one.toCoeff q) x = 0 := by
    apply Complex.ext
    · exact hzero
    · rw [hsreal]
      simp only [mul_im,hillL2Discriminant_real _ hreal,ofReal_im,
        mul_zero,zero_mul,add_zero,zero_im]
  exact ⟨x,⟨hxa,hxb⟩,(mul_eq_zero.mp hprod).resolve_left hsne⟩

theorem hillL2Discriminant_open_band_bounds
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hreal (2*n)) (hillRealLabels q hq hreal (2*n+1))) :
    -2 < (hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re ∧
      (hillL2Discriminant (SpectralWeight.one.toCoeff q) x).re < 2 := by
  let H : ℝ → ℝ := fun t => (hillL2Discriminant (SpectralWeight.one.toCoeff q) t).re^2-4
  have hD : Continuous (fun t : ℝ => hillL2Discriminant (SpectralWeight.one.toCoeff q) t) :=
    (analyticOnNhd_hillL2Discriminant _).continuous.comp Complex.continuous_ofReal
  have hH : Continuous H := ((Complex.continuous_re.comp hD).pow 2).sub continuous_const
  obtain ⟨y,hy,hyD⟩ := exists_hillL2Discriminant_zero_in_band q hq hreal n
  have hyH : H y = -4 := by simp [H,hyD]
  have hneg : H x < 0 := by
    by_contra hh
    have hc : IsPreconnected (H '' Ioo (hillRealLabels q hq hreal (2*n))
        (hillRealLabels q hq hreal (2*n+1))) := isPreconnected_Ioo.image H hH.continuousOn
    have hzmem : (0 : ℝ) ∈ H '' Ioo (hillRealLabels q hq hreal (2*n))
        (hillRealLabels q hq hreal (2*n+1)) :=
      hc.Icc_subset ⟨y,hy,rfl⟩ ⟨x,hx,rfl⟩ ⟨by rw [hyH]; norm_num,not_lt.mp hh⟩
    obtain ⟨z,hz,hzH⟩ := hzmem
    apply hillL2Radicand_ne_zero_between_labels q hq hreal (2*n) z hz
    apply Complex.ext
    · simpa [H,hillL2Radicand,pow_two,mul_re,hillL2Discriminant_real _ hreal] using hzH
    · simp [hillL2Radicand,pow_two,mul_im,hillL2Discriminant_real _ hreal]
  dsimp only [H] at hneg
  constructor <;> nlinarith

end NLS.KdV
