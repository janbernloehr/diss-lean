import NLS.Articles.KdVPseudomeasures.SourceLemmaA1Statement
import NLS.Articles.KdVPseudomeasures.SourceWideStripSpectralResults

/-! Sharp resonant rows retain one Sobolev power at each resonance.
This avoids the loss in the general matrix-row bound and yields the
piecewise epsilon_s of Lemma 2.10 through Appendix A.1. -/
noncomputable section
open NLS.KdV NLS.ReciprocalSeries
namespace NLS.Articles.KdVPseudomeasures

theorem source_resonant_weight_ratio (w : SpectralWeight) (r : ℝ) (n : ℕ) (k : ℤ) :
    w.negativeSobolev r (2*(n:ℤ))/
        (w.negativeSobolev r ((n:ℤ)-k)*w.negativeSobolev r (k+(n:ℤ))) ≤
      Weight.sobolev r ((n:ℤ)-k)*Weight.sobolev r (k+(n:ℤ))/Weight.sobolev r (2*(n:ℤ)) := by
  have hw : w (2*(n:ℤ)) ≤ w ((n:ℤ)-k)*w (k+(n:ℤ)) := by
    simpa only [show (n:ℤ)-k+(k+(n:ℤ))=2*(n:ℤ) by omega] using w.add_le ((n:ℤ)-k) (k+(n:ℤ))
  have hb : w (2*(n:ℤ))/(w ((n:ℤ)-k)*w (k+(n:ℤ))) ≤ 1 :=
    (div_le_one (mul_pos (w.positive _) (w.positive _))).mpr hw
  have he : w.negativeSobolev r (2*(n:ℤ))/
      (w.negativeSobolev r ((n:ℤ)-k)*w.negativeSobolev r (k+(n:ℤ)))=
      (w (2*(n:ℤ))/(w ((n:ℤ)-k)*w (k+(n:ℤ))))*
        (Weight.sobolev r ((n:ℤ)-k)*Weight.sobolev r (k+(n:ℤ))/Weight.sobolev r (2*(n:ℤ))) := by
    simp only [SpectralWeight.negativeSobolev_apply]
    field_simp [(w.positive ((n:ℤ)-k)).ne',(w.positive (k+(n:ℤ))).ne',
      ((Weight.sobolev r).positive ((n:ℤ)-k)).ne',((Weight.sobolev r).positive (k+(n:ℤ))).ne',
      ((Weight.sobolev r).positive (2*(n:ℤ))).ne']
  rw [he]
  exact (mul_le_mul_of_nonneg_right hb
    (div_nonneg (mul_nonneg ((Weight.sobolev r).positive _).le ((Weight.sobolev r).positive _).le)
      ((Weight.sobolev r).positive _).le)).trans_eq (one_mul _)

private theorem sobolev_factor_le_abs_power (r : ℝ) (hr : 0≤r) (j : ℤ) (hj : j≠0) :
    Weight.sobolev r j ≤ (2:ℝ)^r*|(j:ℝ)|^r := by
  have hj1 : (1:ℝ) ≤ |(j:ℝ)| := by exact_mod_cast Int.one_le_abs hj
  calc
    _ ≤ (2*|(j:ℝ)|)^r := Real.rpow_le_rpow (by positivity) (by linarith) hr
    _ = _ := Real.mul_rpow (by norm_num) (abs_nonneg _)

private theorem wide_symbol_le_product (n : ℕ) (hn : 2≤n) (z : ℂ) (hz : z ∈ wideHillStrip n)
    (k : ℤ) (hk : k.natAbs≠n) :
    ‖wideHillSymbol n z k‖ ≤ (|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹ := by
  have hd := freeHill_denominator_lower_wide hn hz hk
  have he : |(n:ℝ)^2-(k:ℝ)^2|=|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)| := by
    rw [← abs_mul]
    congr 1
    ring
  rw [he] at hd
  have hp : 0 < |(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)| := by
    have h := nat_le_abs_sq_sub_sq (by omega : 1≤n) hk
    rw [he] at h
    have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    exact hnp.trans_le h
  simp only [wideHillSymbol,if_neg hk,norm_inv]
  exact inv_anti₀ hp hd

theorem source_resonant_symbol_factor (r : ℝ) (hr : 0≤r) (n : ℕ) (hn : 2≤n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (k : ℤ) :
    (Weight.sobolev r ((n:ℤ)-k)*Weight.sobolev r (k+(n:ℤ))/Weight.sobolev r (2*(n:ℤ)))*
      ‖wideHillSymbol n z k‖ ≤
        ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*quadraticPowerKernel (1-r) n k := by
  by_cases hk : k.natAbs=n
  · have hres := (hill_resonance_iff n k).mp hk
    simp only [wideHillSymbol,if_pos hk,norm_zero,mul_zero,quadraticPowerKernel,if_pos hres]
    exact le_rfl
  have hres : ¬(k=(n:ℤ) ∨ k=-(n:ℤ)) := fun h => hk ((hill_resonance_iff n k).mpr h)
  have hm : (n:ℤ)-k≠0 := by omega
  have hp : k+(n:ℤ)≠0 := by omega
  have hmp : 0 < |(n:ℝ)-(k:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  have hpp : 0 < |(n:ℝ)+(k:ℝ)| := abs_pos.mpr (by exact_mod_cast (show (n:ℤ)+k≠0 by omega))
  have hj := sobolev_factor_le_abs_power r hr ((n:ℤ)-k) hm
  have hl := sobolev_factor_le_abs_power r hr (k+(n:ℤ)) hp
  simp only [Int.cast_sub,Int.cast_natCast] at hj
  simp only [Int.cast_add,Int.cast_natCast,add_comm (k:ℝ) (n:ℝ)] at hl
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hW : (Weight.sobolev r (2*(n:ℤ)))⁻¹ ≤ (n:ℝ)^(-r) := by
    simp only [Weight.sobolev_apply,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
      abs_of_nonneg (by positivity : 0≤2*(n:ℝ)),← Real.rpow_neg (by positivity : 0≤1+2*(n:ℝ))]
    exact Real.rpow_le_rpow_of_nonpos hnp (by linarith) (neg_nonpos.mpr hr)
  have he : |(n:ℝ)+(k:ℝ)|^r*|(n:ℝ)-(k:ℝ)|^r*
      (|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹=quadraticPowerKernel (1-r) n k := by
    rw [quadraticPowerKernel,if_neg hres]
    calc
      _ = (|(n:ℝ)+(k:ℝ)|^r*|(n:ℝ)+(k:ℝ)|^(-1:ℝ))*
          (|(n:ℝ)-(k:ℝ)|^r*|(n:ℝ)-(k:ℝ)|^(-1:ℝ)) := by
        simp only [Real.rpow_neg_one,mul_inv]
        ring
      _ = _ := by rw [← Real.rpow_add hpp,← Real.rpow_add hmp,show r+(-1:ℝ)=-(1-r) by ring]
  calc
    _ ≤ ((2:ℝ)^r*|(n:ℝ)-(k:ℝ)|^r)*((2:ℝ)^r*|(n:ℝ)+(k:ℝ)|^r)*
        (n:ℝ)^(-r)*(|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹ := by
      rw [div_eq_mul_inv]
      have hprod := mul_le_mul hj hl ((Weight.sobolev r).positive (k+(n:ℤ))).le (by positivity)
      have hleft := mul_le_mul hprod hW
        (inv_nonneg.mpr ((Weight.sobolev r).positive (2*(n:ℤ))).le) (by positivity)
      exact mul_le_mul hleft (wide_symbol_le_product n hn z hz k hk) (norm_nonneg _) (by positivity)
    _ = ((2:ℝ)^(2*r)*(n:ℝ)^(-r))*(|(n:ℝ)+(k:ℝ)|^r*|(n:ℝ)-(k:ℝ)|^r*
        (|(n:ℝ)+(k:ℝ)| * |(n:ℝ)-(k:ℝ)|)⁻¹) := by
      rw [show (2:ℝ)^(2*r)=(2:ℝ)^r*(2:ℝ)^r by rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]; congr 1; ring]
      ring
    _ = _ := by rw [he]

end NLS.Articles.KdVPseudomeasures
