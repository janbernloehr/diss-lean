import NLS.ComplexAnalysis.WeightedAffineQuadraticRemainder

/-! Retaining the small weight ratio in affine and diagonal action
cancellation estimates, including collapsed quadratic factors. -/
set_option autoImplicit false
namespace NLS.ComplexAnalysis

theorem weighted_affine_quadratic_remainder_tail_bound
    (w v H B M T J : ℝ) (hw : 0<w) (hv : 0<v)
    (hB : 0≤B) (hT : 0≤T) (g a₀ a₁ τ c : ℂ)
    (hg : ‖g‖≤H) (hτ : ‖τ‖≤v*T) (hmid : ‖τ-c‖≤J)
    (h₁ : ‖a₁-τ*a₀‖≤‖g‖*B/2)
    (h₀ : w*‖g^2*a₀-g^2/4‖≤‖g‖^2*M) :
    (w/v)*‖g^2*a₁-c*g^2/4‖≤‖g‖^2*((w/v)*(H*B/2+J/4)+T*M) := by
  have hv0 : 0<v := hv
  have hratio : 0≤w/v := div_nonneg hw.le hv0.le
  have he : g^2*a₁-c*g^2/4=
      g^2*(a₁-τ*a₀)+τ*(g^2*a₀-g^2/4)+(τ-c)*g^2/4 := by ring
  have hn : ‖g^2*a₁-c*g^2/4‖≤
      ‖g‖^2*‖a₁-τ*a₀‖+‖τ‖*‖g^2*a₀-g^2/4‖+‖τ-c‖*‖g‖^2/4 := by
    rw [he]
    have h := (norm_add_le (g^2*(a₁-τ*a₀)+τ*(g^2*a₀-g^2/4)) ((τ-c)*g^2/4)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
    simpa only [norm_mul,norm_div,norm_pow,Complex.norm_ofNat] using h
  have hfirst : (w/v)*(‖g‖^2*‖a₁-τ*a₀‖)≤‖g‖^2*((w/v)*(H*B/2)) := by
    have h := h₁.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hg hB) (by norm_num))
    calc
      _ ≤ (w/v)*(‖g‖^2*(H*B/2)) := by gcongr
      _ = _ := by ring
  have hsecond : (w/v)*(‖τ‖*‖g^2*a₀-g^2/4‖)≤‖g‖^2*(T*M) := by
    calc
      _≤(w/v)*((v*T)*‖g^2*a₀-g^2/4‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hτ (norm_nonneg _)) hratio
      _=T*(w*‖g^2*a₀-g^2/4‖) := by field_simp
      _≤T*(‖g‖^2*M) := mul_le_mul_of_nonneg_left h₀ hT
      _=‖g‖^2*(T*M) := by ring
  have hthird : (w/v)*(‖τ-c‖*‖g‖^2/4)≤‖g‖^2*((w/v)*(J/4)) := by
    calc
      _ ≤ (w/v)*(J*‖g‖^2/4) := by gcongr
      _ = _ := by ring
  calc
    _≤(w/v)*(‖g‖^2*‖a₁-τ*a₀‖+‖τ‖*‖g^2*a₀-g^2/4‖+‖τ-c‖*‖g‖^2/4) :=
      mul_le_mul_of_nonneg_left hn hratio
    _=(w/v)*(‖g‖^2*‖a₁-τ*a₀‖)+(w/v)*(‖τ‖*‖g^2*a₀-g^2/4‖)+
        (w/v)*(‖τ-c‖*‖g‖^2/4) := by ring
    _≤‖g‖^2*((w/v)*(H*B/2))+‖g‖^2*(T*M)+‖g‖^2*((w/v)*(J/4)) := add_le_add (add_le_add hfirst hsecond) hthird
    _=‖g‖^2*((w/v)*(H*B/2+J/4)+T*M) := by ring

theorem weighted_diagonal_action_cancellation_tail_bound
    (w r H X Ma Md : ℝ) (hr : 0≤r) (hX : 0≤X)
    (g n b a d x : ℂ) (hg : ‖g‖≤H) (hrw : r*‖n‖≤w)
    (ha : r*‖a-n*b*g^2/4‖≤‖g‖^2*Ma)
    (hd : w*‖d-b*g^2/4‖≤‖g‖^2*Md)
    (hx : ‖n*x‖≤‖g‖^3*X) :
    r*‖-12*n*(d-x)+12*a‖≤‖g‖^2*(12*(Ma+Md+r*H*X)) := by
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
  have hx' : r*‖n*x‖≤‖g‖^2*(r*H*X) := by
    calc
      _ ≤ r*(‖g‖^3*X) := mul_le_mul_of_nonneg_left hx hr
      _ = (r*‖g‖^2*X)*‖g‖ := by ring
      _ ≤ (r*‖g‖^2*X)*H := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = ‖g‖^2*(r*H*X) := by ring
  rw [he,norm_mul,Complex.norm_ofNat]
  calc
    _=12*(r*‖(a-n*b*g^2/4)-n*(d-b*g^2/4)+n*x‖) := by ring
    _≤12*(r*(‖a-n*b*g^2/4‖+‖n‖*‖d-b*g^2/4‖+‖n*x‖)) := by gcongr
    _=12*(r*‖a-n*b*g^2/4‖+r*(‖n‖*‖d-b*g^2/4‖)+r*‖n*x‖) := by ring
    _≤12*(‖g‖^2*Ma+‖g‖^2*Md+‖g‖^2*(r*H*X)) := by gcongr
    _=‖g‖^2*(12*(Ma+Md+r*H*X)) := by ring

end NLS.ComplexAnalysis
