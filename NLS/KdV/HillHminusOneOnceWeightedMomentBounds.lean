import NLS.KdV.HillHminusOneTwoWeightedMomentBounds
import NLS.SequenceSpaces.HilbertSquareWeightInterpolation

/-! A single positive index weight suffices for the actual second-moment
bounds. Exact midpoint interpolation between the existing two weighted
endpoints improves the own-index growth from n^2 to n, retaining the actual
canonical gap, primitive, numerator and fixed normalization. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV
namespace HillHminusUniformPeriodData
variable {N M : ℕ} {V U : Set PeriodOneHminusOne} {A r B : ℝ}
variable {C : HillHminusMiuraChart}
variable (D : HillHminusUniformPeriodData C N V A)
include D

theorem momentKernel_unweighted_second_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (q : PeriodOneHminusOne) (hq : q∈U) (k : ℕ+) (hk : M≤(k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ‖hillHminusMomentKernelVector C N k 2 q‖≤
      (1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2) := by
  let v := hillHminusMomentKernelVector C N k 2 q
  let x := ‖l-u‖^2/(k : ℕ)^2
  have hB := H.bound_pos
  have hx : 0≤x := by dsimp only [x];positivity
  have hxbound : x≤4*Real.pi^4 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<(k : ℕ)^2)).mpr
    nlinarith [mul_self_le_mul_self (norm_nonneg (l-u)) (hp.norm_gap_le H.radius_le)]
  have hxquad : x^2≤4*Real.pi^4*x := by nlinarith [mul_le_mul_of_nonneg_right hxbound hx]
  obtain ⟨_,hrem,hdiag⟩ := D.momentKernel_second_gap_bounds H hUV q hq k hk l u hp
  change ‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖≤((16/Real.pi^3)*B^3)*x^2 at hrem
  change ‖v (k : ℤ)‖≤(8*Real.pi*B^3)*x at hdiag
  have he : v=NLS.Coeff.coordinateRemainder v (k : ℤ)+lp.single 2 (k : ℤ) (v (k : ℤ)) := by
    dsimp only [NLS.Coeff.coordinateRemainder];abel
  calc
    ‖v‖≤‖NLS.Coeff.coordinateRemainder v (k : ℤ)‖+‖v (k : ℤ)‖ := by
      calc
        _=‖NLS.Coeff.coordinateRemainder v (k : ℤ)+lp.single 2 (k : ℤ) (v (k : ℤ))‖ := congrArg norm he
        _≤_ := by simpa only [lp.norm_single (by norm_num : 0<(2 : ENNReal))] using
          norm_add_le (NLS.Coeff.coordinateRemainder v (k : ℤ)) (lp.single 2 (k : ℤ) (v (k : ℤ)))
    _≤((16/Real.pi^3)*B^3)*(4*Real.pi^4*x)+(8*Real.pi*B^3)*x := by
      exact (add_le_add hrem hdiag).trans (by gcongr)
    _=(72*Real.pi*B^3)*x := by field_simp;ring
    _≤(1032*Real.pi*B^3)*x := by gcongr;norm_num

/-- Midpoint interpolation retains one reciprocal contour weight and the
full actual gap factor. The power of k is exactly one. -/
theorem momentKernel_onceWeighted_second_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (q : PeriodOneHminusOne) (hq : q∈U) (k : ℕ+) (hk : M≤(k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u) :
    ‖NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal (hillHminusMomentKernelVector C N k 2 q)‖≤
      (1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ) := by
  let v := hillHminusMomentKernelVector C N k 2 q
  let a := NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal v
  let b := NLS.Coeff.multiplier (NLS.Coeff.positiveIndexPowerReciprocal 2) v
  have hmid := NLS.Coeff.norm_sq_middle_weight_le
    (fun j => (NLS.Coeff.positiveIndexWeight j)⁻¹) v b a
    (fun j => by simp only [b,NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexPowerReciprocal_apply,inv_pow])
    (fun _ => rfl)
  have hv := D.momentKernel_unweighted_second_bound H hUV q hq k hk l u hp
  have hb := D.momentKernel_twoWeighted_second_bound H hUV q hq k hk l u hp
  have hB := H.bound_pos
  have hs : ‖a‖^2≤((1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ))^2 := by
    calc
      _≤‖v‖*‖b‖ := hmid
      _≤((1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2))*
        ((1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ)^2) :=
          mul_le_mul hv hb (norm_nonneg _) (by positivity)
      _=_ := by field_simp
  exact (sq_le_sq₀ (norm_nonneg a) (by positivity)).mp hs

omit D in
private theorem exists_onceWeighted_inverse_column
    (R Q : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2) (hR : ‖R‖≤2) (hQ : ‖Q‖≤2) (n : ℕ+)
    (hcompat : ∀ j : ℤ, NLS.Coeff.positiveIndexWeight j^2*(R (lp.single 2 (n : ℤ) 1)) j=
      (n : ℂ)^2*(Q (lp.single 2 (n : ℤ) 1)) j) :
    ∃ a : NLS.Coeff 2,
      (∀ j, a j=NLS.Coeff.positiveIndexWeight j*(R (lp.single 2 (n : ℤ) 1)) j) ∧ ‖a‖≤2*(n : ℝ) := by
  let v := R (lp.single 2 (n : ℤ) 1)
  let b : NLS.Coeff 2 := (n : ℂ)^2 • Q (lp.single 2 (n : ℤ) 1)
  have hv : ‖v‖≤2 := by
    simpa only [lp.norm_single (by norm_num : 0<(2 : ENNReal)),norm_one,mul_one] using
      (R.le_opNorm (lp.single 2 (n : ℤ) (1 : ℂ))).trans
        (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
  have hb : ‖b‖≤2*(n : ℝ)^2 := by
    have hcol : ‖Q (lp.single 2 (n : ℤ) (1 : ℂ))‖≤2 := by
      simpa only [lp.norm_single (by norm_num : 0<(2 : ENNReal)),norm_one,mul_one] using
        (Q.le_opNorm (lp.single 2 (n : ℤ) (1 : ℂ))).trans
          (mul_le_mul_of_nonneg_right hQ (norm_nonneg _))
    change ‖(n : ℂ)^2 • Q (lp.single 2 (n : ℤ) 1)‖≤_
    rw [norm_smul,norm_pow,Complex.norm_natCast]
    nlinarith [mul_le_mul_of_nonneg_left hcol (sq_nonneg (n : ℝ))]
  obtain ⟨a,ha,hbound⟩ := NLS.Coeff.exists_middle_weight_of_square_relation NLS.Coeff.positiveIndexWeight v b
    (fun j => (hcompat j).symm)
  refine ⟨a,ha,?_⟩
  have hs := hbound.trans (mul_le_mul hv hb (norm_nonneg _) (by norm_num : (0 : ℝ)≤2))
  nlinarith [norm_nonneg a]

/-- The ACTUAL second moment has only linear own-index growth, with exact
n/k normalization and the same rough gap majorant as the convergent series. -/
theorem normalizedMoment_two_onceWeighted_bound
    (H : HillHminusCriticalPrimitiveCutData C N M U r B) (hUV : U⊆V)
    (R Q : PeriodOneHminusOne → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (q : PeriodOneHminusOne) (hq : q∈U) (n k : ℕ+) (hk : M≤(k : ℕ))
    (l u : ℂ) (hp : HillHminusHighGapPair q k r l u)
    (hR : ‖R q‖≤2) (hQ : ‖Q q‖≤2)
    (hcompat : ∀ j : ℤ, NLS.Coeff.positiveIndexWeight j^2*(R q (lp.single 2 (n : ℤ) 1)) j=
      (n : ℂ)^2*(Q q (lp.single 2 (n : ℤ) 1)) j) :
    ‖hillHminusNormalizedMoment C N R n k 2 q‖≤
      (1376*Real.pi^2*B^3)*(n : ℝ)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ) := by
  obtain ⟨a,ha,hbound⟩ := exists_onceWeighted_inverse_column (R q) (Q q) hR hQ n hcompat
  have he : R q (lp.single 2 (n : ℤ) 1)=NLS.Coeff.multiplier NLS.Coeff.positiveIndexReciprocal a := by
    ext j
    rw [NLS.Coeff.multiplier_apply,NLS.Coeff.positiveIndexReciprocal_apply,ha j]
    field_simp [NLS.Coeff.positiveIndexWeight_ne_zero]
  rw [D.norm_normalizedMoment_two_eq R n k q (hUV hq),he,NLS.Coeff.dualPairing_multiplier_left]
  apply (mul_le_mul_of_nonneg_left (NLS.Coeff.norm_dualPairing_le _ _) (by positivity : 0≤2*Real.pi/3)).trans
  calc
    _≤(2*Real.pi/3)*((2*(n : ℝ))*((1032*Real.pi*B^3)*(‖l-u‖^2/(k : ℕ)^2)/(k : ℕ))) := by
      gcongr
      exact D.momentKernel_onceWeighted_second_bound H hUV q hq k hk l u hp
    _=_ := by ring

end HillHminusUniformPeriodData
end NLS.KdV
