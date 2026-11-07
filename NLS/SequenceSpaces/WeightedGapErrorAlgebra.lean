import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar weight bookkeeping for actual gap-normalized primitive and
square errors. No positivity or division by a gap is required. -/
set_option autoImplicit false
namespace NLS

theorem weighted_primitive_gap_error_bound
    (w G Q A M S K L e : ℝ) (hw : 0<w) (hG : 0≤G) (hQ : 0≤Q) (hL : 0≤L)
    (hGweight : w*G≤S) (hQbound : Q≤K)
    (he : e≤G*(A*(M/w)+G*Q)*L) :
    w*e≤G*(A*M+S*K)*L := by
  have hS : 0≤S := (mul_nonneg hw.le hG).trans hGweight
  have hprod := mul_le_mul hGweight hQbound hQ hS
  have halg : w*(G*(A*(M/w)+G*Q)*L)=G*(A*M+(w*G)*Q)*L := by
    field_simp
  calc
    _≤w*(G*(A*(M/w)+G*Q)*L) := mul_le_mul_of_nonneg_left he hw.le
    _=G*(A*M+(w*G)*Q)*L := halg
    _≤G*(A*M+S*K)*L := by gcongr

theorem weighted_square_gap_error_bound
    (w G M e : ℝ) (hw : 1≤w) (hM : 0≤M)
    (he : e≤G^2*(M/w)*(M/w+1)) :
    w*e≤G^2*M*(M+1) := by
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hdiv : M/w≤M := div_le_self hM hw
  have halg : w*(G^2*(M/w)*(M/w+1))=G^2*M*(M/w+1) := by
    field_simp
  calc
    _≤w*(G^2*(M/w)*(M/w+1)) := mul_le_mul_of_nonneg_left he hw0.le
    _=G^2*M*(M/w+1) := halg
    _≤G^2*M*(M+1) := mul_le_mul_of_nonneg_left (by linarith : M/w+1≤M+1) (mul_nonneg (sq_nonneg _) hM)

theorem weighted_diagonal_coefficient_error_bound
    (w E F x : ℝ) (hw : 1≤w) (hE : 0≤E) (hF : 0≤F)
    (hx : x≤8*Real.pi*((E/w)*(F/w+1)+(F/w)/4)) :
    w*x≤8*Real.pi*(E*(F+1)+F/4) := by
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hdiv : F/w≤F := div_le_self hF hw
  have halg : w*(8*Real.pi*((E/w)*(F/w+1)+(F/w)/4))=
      8*Real.pi*(E*(F/w+1)+F/4) := by field_simp
  calc
    _≤w*(8*Real.pi*((E/w)*(F/w+1)+(F/w)/4)) := mul_le_mul_of_nonneg_left hx hw0.le
    _=8*Real.pi*(E*(F/w+1)+F/4) := halg
    _≤8*Real.pi*(E*(F+1)+F/4) := by gcongr

end NLS
