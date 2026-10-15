import NLS.Fourier.DiscreteHausdorffYoung
import NLS.Fourier.CircleSampling

/-!
# Hausdorff–Young for physical trigonometric polynomials

Sufficiently large cyclic grids separate every finite set of signed frequencies.
Discrete interpolation and convergence of sample moments give the constant-one
Lp estimate for actual continuous Fourier polynomials at every positive period.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.Fourier
open NLS.FiniteMatrix
variable {L : ℝ} [Fact (0 < L)]

/-- A grid larger than twice the maximal absolute frequency avoids aliasing. -/
theorem frequency_injective_of_large (S : Finset ℤ) (N : ℕ) (hN : 2*S.sup Int.natAbs ≤ N) :
    Function.Injective (fun n : S => (n.val : ZMod (N+1))) := by
  intro i j hij
  by_contra hne
  have hdiff : (i.val-j.val) ≠ 0 := sub_ne_zero.mpr (Subtype.val_injective.ne hne)
  have hz : ((i.val-j.val : ℤ) : ZMod (N+1)) = 0 := by push_cast; exact sub_eq_zero.mpr hij
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (i.val-j.val) (N+1)).mp hz
  have hd' : N+1 ∣ (i.val-j.val).natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
  have hb := Nat.le_of_dvd (Int.natAbs_pos.mpr hdiff) hd'
  have hi : i.val.natAbs ≤ S.sup Int.natAbs := Finset.le_sup i.property
  have hj : j.val.natAbs ≤ S.sup Int.natAbs := Finset.le_sup j.property
  have hsum := Int.natAbs_sub_le i.val j.val
  omega

/-- Positive-phase synthesis is the negative-phase DFT evaluated at the reflected index. -/
theorem polynomial_grid_eq_dft (S : Finset ℤ) (N : ℕ) [NeZero N]
    (he : Function.Injective (fun n : S => (n.val : ZMod N))) (a : ℤ → ℂ) (j : ZMod N) :
    continuousFourierPolynomial (L := L) S a (circleGridPoint N j) =
      ZMod.dft (extendZero ⟨fun n : S => (n.val : ZMod N),he⟩ (fun n => a n.val)) (-j) := by
  let e : S ↪ ZMod N := ⟨fun n : S => (n.val : ZMod N),he⟩
  change _ = ZMod.dft (extendZero e (fun n => a n.val)) (-j)
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul,mul_neg,neg_neg]
  rw [show (∑ k : ZMod N, ZMod.stdAddChar (k*j)*extendZero e (fun n => a n.val) k) =
      ∑ k : ZMod N, extendZero e (fun n => a n.val) k*ZMod.stdAddChar (k*j) by
        apply Finset.sum_congr rfl; intro k _; ring]
  rw [sum_extendZero_mul]
  simp only [continuousFourierPolynomial,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    fourier_circleGridPoint]
  exact (Finset.sum_attach S (fun n => a n*ZMod.stdAddChar ((n : ZMod N)*j))).symm

end NLS.Fourier

namespace NLS.Fourier
open NLS.FiniteMatrix
variable {L : ℝ} [Fact (0 < L)]

theorem polynomial_grid_moment_bound {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp₂ : p ≤ 2) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (S : Finset ℤ) (a : ℤ → ℂ) (N : ℕ) (hN : 2*S.sup Int.natAbs ≤ N) :
    ((N+1:ℕ):ℝ)⁻¹ * ∑ j : ZMod (N+1),
      ‖continuousFourierPolynomial (L := L) S a (circleGridPoint (N+1) j)‖^q.toReal ≤
      ‖WithLp.toLp p (fun n : S => a n.val)‖^q.toReal := by
  let e : S ↪ ZMod (N+1) := ⟨fun n => (n.val : ZMod (N+1)),frequency_injective_of_large S N hN⟩
  have he (j : ZMod (N+1)) : continuousFourierPolynomial (L := L) S a (circleGridPoint (N+1) j) =
      ZMod.dft (extendZero e (fun n => a n.val)) (-j) := polynomial_grid_eq_dft S (N+1) e.injective a j
  simp_rw [he]
  have hsum := Equiv.sum_comp (Equiv.neg (ZMod (N+1))) (fun j => ‖ZMod.dft (extendZero e (fun n => a n.val)) j‖^q.toReal)
  simp only [Equiv.neg_apply] at hsum
  rw [hsum]
  have h := dft_moment_bound hp₂ hp hq (extendZero e (fun n => a n.val))
  rwa [norm_extendZero hp] at h

/-- Pass the sharp discrete moment estimate to the normalized Haar integral. -/
theorem integral_polynomial_rpow_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp₂ : p ≤ 2) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (S : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x, ‖continuousFourierPolynomial (L := L) S a x‖^q.toReal ∂AddCircle.haarAddCircle) ≤
      ‖WithLp.toLp p (fun n : S => a n.val)‖^q.toReal := by
  apply le_of_tendsto (tendsto_circleGridAverage_norm_rpow (continuousFourierPolynomial S a) hq.le)
  filter_upwards [eventually_ge_atTop (2*S.sup Int.natAbs)] with N hN
  exact polynomial_grid_moment_bound hp₂ hp hq S a N hN

end NLS.Fourier

namespace NLS.Fourier
variable {L : ℝ} [Fact (0 < L)]

theorem norm_continuous_toLp {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : 0 < q.toReal)
    (f : C(AddCircle L,ℂ)) :
    ‖ContinuousMap.toLp q AddCircle.haarAddCircle ℂ f‖ =
      (∫ x, ‖f x‖^q.toReal ∂AddCircle.haarAddCircle)^(1/q.toReal) := by
  have hf : MemLp f q AddCircle.haarAddCircle := f.memLp (p := q) AddCircle.haarAddCircle ℂ
  rw [Lp.norm_def,eLpNorm_congr_ae (ContinuousMap.coeFn_toLp _ f),
    hf.eLpNorm_eq_integral_rpow_norm (ENNReal.toReal_pos_iff.mp hq).1.ne' (ENNReal.toReal_pos_iff.mp hq).2.ne,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)) _)]
  rw [one_div]

/-- Constant-one synthesis estimate for physical finite Fourier polynomials. -/
theorem norm_polynomial_toLp_le {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] (hp₂ : p ≤ 2) (hp : 0 < p.toReal) (hq : 0 < q.toReal)
    (S : Finset ℤ) (a : ℤ → ℂ) :
    ‖ContinuousMap.toLp q AddCircle.haarAddCircle ℂ (continuousFourierPolynomial (L := L) S a)‖ ≤
      ‖WithLp.toLp p (fun n : S => a n.val)‖ := by
  rw [norm_continuous_toLp hq]
  have h := Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    (integral_polynomial_rpow_le (L := L) hp₂ hp hq S a) (by positivity : 0 ≤ 1/q.toReal)
  rw [← Real.rpow_mul (norm_nonneg _),mul_one_div_cancel hq.ne',Real.rpow_one] at h
  exact h

end NLS.Fourier
