import Mathlib.Analysis.Complex.Basic

/-! Weighted affine cancellation with a quadratic factor. Every
estimate remains literal when that factor vanishes. -/
set_option autoImplicit false
namespace NLS.ComplexAnalysis

theorem weighted_affine_quadratic_remainder_bound
    (w v H B M T J : ℝ) (hw : 0<w) (hv : 1≤v) (hwv : w≤v)
    (hB : 0≤B) (hT : 0≤T) (g a₀ a₁ τ c : ℂ)
    (hg : ‖g‖≤H) (hτ : ‖τ‖≤v*T) (hmid : ‖τ-c‖≤J)
    (h₁ : ‖a₁-τ*a₀‖≤‖g‖*B/2)
    (h₀ : w*‖g^2*a₀-g^2/4‖≤‖g‖^2*M) :
    (w/v)*‖g^2*a₁-c*g^2/4‖≤‖g‖^2*(H*B/2+T*M+J/4) := by
  have hv0 : 0<v := zero_lt_one.trans_le hv
  have hratio : 0≤w/v := div_nonneg hw.le hv0.le
  have hratio1 : w/v≤1 := (div_le_one hv0).mpr hwv
  have he : g^2*a₁-c*g^2/4=
      g^2*(a₁-τ*a₀)+τ*(g^2*a₀-g^2/4)+(τ-c)*g^2/4 := by ring
  have hn : ‖g^2*a₁-c*g^2/4‖≤
      ‖g‖^2*‖a₁-τ*a₀‖+‖τ‖*‖g^2*a₀-g^2/4‖+‖τ-c‖*‖g‖^2/4 := by
    rw [he]
    have h := (norm_add_le (g^2*(a₁-τ*a₀)+τ*(g^2*a₀-g^2/4)) ((τ-c)*g^2/4)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    simpa only [norm_mul,norm_div,norm_pow,Complex.norm_ofNat] using h
  have hfirst : (w/v)*(‖g‖^2*‖a₁-τ*a₀‖)≤‖g‖^2*(H*B/2) := by
    calc
      _≤‖g‖^2*‖a₁-τ*a₀‖ := by nlinarith [mul_nonneg (sq_nonneg ‖g‖) (norm_nonneg (a₁-τ*a₀))]
      _≤‖g‖^2*(H*B/2) := mul_le_mul_of_nonneg_left
        (h₁.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hg hB) (by norm_num))) (sq_nonneg _)
  have hsecond : (w/v)*(‖τ‖*‖g^2*a₀-g^2/4‖)≤‖g‖^2*(T*M) := by
    calc
      _≤(w/v)*((v*T)*‖g^2*a₀-g^2/4‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hτ (norm_nonneg _)) hratio
      _=T*(w*‖g^2*a₀-g^2/4‖) := by field_simp
      _≤T*(‖g‖^2*M) := mul_le_mul_of_nonneg_left h₀ hT
      _=‖g‖^2*(T*M) := by ring
  have hthird : (w/v)*(‖τ-c‖*‖g‖^2/4)≤‖g‖^2*(J/4) := by
    calc
      _≤‖τ-c‖*‖g‖^2/4 := by nlinarith [mul_nonneg (norm_nonneg (τ-c)) (sq_nonneg ‖g‖)]
      _≤‖g‖^2*(J/4) := by nlinarith [mul_le_mul_of_nonneg_right hmid (sq_nonneg ‖g‖)]
  calc
    _≤(w/v)*(‖g‖^2*‖a₁-τ*a₀‖+‖τ‖*‖g^2*a₀-g^2/4‖+‖τ-c‖*‖g‖^2/4) :=
      mul_le_mul_of_nonneg_left hn hratio
    _=(w/v)*(‖g‖^2*‖a₁-τ*a₀‖)+(w/v)*(‖τ‖*‖g^2*a₀-g^2/4‖)+
        (w/v)*(‖τ-c‖*‖g‖^2/4) := by ring
    _≤‖g‖^2*(H*B/2)+‖g‖^2*(T*M)+‖g‖^2*(J/4) := add_le_add (add_le_add hfirst hsecond) hthird
    _=‖g‖^2*(H*B/2+T*M+J/4) := by ring

theorem weighted_diagonal_action_cancellation_bound
    (w r H X Ma Md : ℝ) (hr : 0≤r) (hr1 : r≤1) (hX : 0≤X)
    (g n b a d x : ℂ) (hg : ‖g‖≤H) (hrw : r*‖n‖≤w)
    (ha : r*‖a-n*b*g^2/4‖≤‖g‖^2*Ma)
    (hd : w*‖d-b*g^2/4‖≤‖g‖^2*Md)
    (hx : ‖n*x‖≤‖g‖^3*X) :
    r*‖-12*n*(d-x)+12*a‖≤‖g‖^2*(12*(Ma+Md+H*X)) := by
  have he : -12*n*(d-x)+12*a=
      12*((a-n*b*g^2/4)-n*(d-b*g^2/4)+n*x) := by ring
  have hnorm : ‖(a-n*b*g^2/4)-n*(d-b*g^2/4)+n*x‖≤
      ‖a-n*b*g^2/4‖+‖n‖*‖d-b*g^2/4‖+‖n*x‖ := by
    have h := (norm_add_le ((a-n*b*g^2/4)-n*(d-b*g^2/4)) (n*x)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    simpa only [norm_mul] using h
  have hd' : r*(‖n‖*‖d-b*g^2/4‖)≤‖g‖^2*Md := by
    calc
      _=(r*‖n‖)*‖d-b*g^2/4‖ := by ring
      _≤w*‖d-b*g^2/4‖ := mul_le_mul_of_nonneg_right hrw (norm_nonneg _)
      _≤‖g‖^2*Md := hd
  have hx' : r*‖n*x‖≤‖g‖^2*(H*X) := by
    calc
      _≤‖n*x‖ := by nlinarith [norm_nonneg (n*x)]
      _≤‖g‖^3*X := hx
      _=(‖g‖^2*X)*‖g‖ := by ring
      _≤(‖g‖^2*X)*H := mul_le_mul_of_nonneg_left hg (mul_nonneg (sq_nonneg _) hX)
      _=‖g‖^2*(H*X) := by ring
  rw [he,norm_mul,Complex.norm_ofNat]
  calc
    _=12*(r*‖(a-n*b*g^2/4)-n*(d-b*g^2/4)+n*x‖) := by ring
    _≤12*(r*(‖a-n*b*g^2/4‖+‖n‖*‖d-b*g^2/4‖+‖n*x‖)) := by gcongr
    _=12*(r*‖a-n*b*g^2/4‖+r*(‖n‖*‖d-b*g^2/4‖)+r*‖n*x‖) := by ring
    _≤12*(‖g‖^2*Ma+‖g‖^2*Md+‖g‖^2*(H*X)) := by gcongr
    _=‖g‖^2*(12*(Ma+Md+H*X)) := by ring

end NLS.ComplexAnalysis
