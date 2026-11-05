import NLS.MKdV.MiuraOpenAngularPhaseDescent

/-! # The full NLS unit phase has exactly the original selected action domain

The normalized angular coordinate is a positive real multiple of the
original scaled NLS Cartesian coordinate. Its zero set is exactly the
collapsed physical mKdV action, so its unit phase is defined on precisely
the selected original open-action locus. No other gap is required open.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

private theorem real_cartesian_sub_I_mul_eq_zero_iff (z : ℂ × ℂ)
    (hx : z.1.im = 0) (hy : z.2.im = 0) : z.1-I*z.2 = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp only [sub_re,mul_re,I_re,I_im,hy,zero_mul,one_mul,sub_zero,zero_re] at hr
    simp only [sub_im,mul_im,I_re,I_im,hx,hy,zero_mul,one_mul,zero_add,zero_sub,zero_im,neg_eq_zero] at hi
    exact Prod.ext (Complex.ext hr hx) (Complex.ext hi hy)
  · intro h
    rw [h]
    simp

theorem miuraNativeNLSAngularCoordinate_eq_scaled_original (s m : ℕ) (hm : 1 ≤ m)
    (a : MiuraRealSobolevSource s) :
    miuraNativeNLSAngularCoordinate s m a = (Weight.sobolev (s : ℝ) m : ℂ)*
      ((miuraL2CartesianCoordinates m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)).1-
        I*(miuraL2CartesianCoordinates m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val)).2) := by
  have he := miuraSobolevNormalizedCartesianMap_eval s a.val (m : ℤ)
  rw [miuraSobolevPositiveCartesianMap_positive s a.val (fun j => a.property j) m hm] at he
  unfold miuraNativeNLSAngularCoordinate
  rw [he]
  change _*_-I*(_*_) = _
  ring

theorem miuraNativeNLSAngularCoordinate_zero_iff_physical_action_zero (s m : ℕ) (hm : 1 ≤ m)
    (a : MiuraRealSobolevSource s) :
    miuraNativeNLSAngularCoordinate s m a = 0 ↔
      miuraL2Action m (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) = 0 := by
  let u := hierarchySobolevJetL2 s 0 (Nat.zero_le s) a.val
  have hu := miuraSobolevL2Inclusion_real s a.val (fun j => a.property j)
  obtain ⟨hx,hy⟩ := miuraL2CartesianCoordinates_real u hu m hm
  rw [miuraNativeNLSAngularCoordinate_eq_scaled_original s m hm a,mul_eq_zero]
  have hw : (Weight.sobolev (s : ℝ) (m : ℤ) : ℂ) ≠ 0 := (Weight.sobolev (s : ℝ)).complex_ne_zero m
  rw [or_iff_right hw,real_cartesian_sub_I_mul_eq_zero_iff _ hx hy]
  exact miuraL2CartesianCoordinates_eq_zero_iff_action_zero u hu m hm

theorem norm_miuraNativeNLSUnitPhase (s m : ℕ) (a : MiuraRealSobolevSource s)
    (h : miuraNativeNLSAngularCoordinate s m a ≠ 0) : ‖miuraNativeNLSUnitPhase s m a‖ = 1 := by
  unfold miuraNativeNLSUnitPhase
  simp only [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr h)

end NLS.MKdV
