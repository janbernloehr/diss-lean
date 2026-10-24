import NLS.SequenceSpaces.HilbertCotangent
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! # Bounded bilinear transpose of an integer-indexed Hilbert matrix

The unconjugated coefficient pairing defines the ordinary transpose of a
bounded operator on complex ell-two. It transposes matrix entries and its
kernel detects density of the original range. All series below converge
absolutely by Hilbert duality.
-/
noncomputable section
open Set Complex
open scoped ComplexConjugate
namespace NLS.Coeff

def hilbertMatrixTranspose (A : Coeff 2 →L[ℂ] Coeff 2) : Coeff 2 →L[ℂ] Coeff 2 :=
  hilbertCotangentCoefficients.comp
    (((ContinuousLinearMap.compL ℂ (Coeff 2) (Coeff 2) ℂ).flip A).comp dualPairing)

theorem dualPairing_hilbertMatrixTranspose (A : Coeff 2 →L[ℂ] Coeff 2) (a b : Coeff 2) :
    dualPairing (hilbertMatrixTranspose A a) b = dualPairing a (A b) :=
  dualPairing_hilbertCotangentCoefficients ((dualPairing a).comp A) b

theorem hilbertMatrixTranspose_apply (A : Coeff 2 →L[ℂ] Coeff 2) (a : Coeff 2) (m : ℤ) :
    hilbertMatrixTranspose A a m = ∑' n : ℤ, a n * A (lp.single 2 m 1) n := by
  change hilbertCotangentCoefficients ((dualPairing a).comp A) m = _
  rw [hilbertCotangentCoefficients_apply]
  rfl

theorem summable_norm_hilbertMatrixTranspose_apply
    (A : Coeff 2 →L[ℂ] Coeff 2) (a : Coeff 2) (m : ℤ) :
    Summable (fun n : ℤ => ‖a n * A (lp.single 2 m 1) n‖) :=
  summable_norm_dualPairing a (A (lp.single 2 m 1))

@[simp] theorem dualPairing_hilbert_single_left (a : Coeff 2) (n : ℤ) :
    dualPairing (lp.single 2 n (1 : ℂ)) a = a n := by
  simp [dualPairing_apply, lp.single_apply, Pi.single_apply]

@[simp] theorem dualPairing_hilbert_single_right (a : Coeff 2) (n : ℤ) :
    dualPairing a (lp.single 2 n (1 : ℂ)) = a n := by
  simp [dualPairing_apply, lp.single_apply, Pi.single_apply]

theorem dualPairing_hilbert_comm (a b : Coeff 2) : dualPairing a b = dualPairing b a := by
  apply tsum_congr
  intro n
  exact mul_comm _ _

/-- The row and column indices are literally exchanged, with no complex conjugation. -/
@[simp] theorem hilbertMatrixTranspose_single (A : Coeff 2 →L[ℂ] Coeff 2) (n m : ℤ) :
    hilbertMatrixTranspose A (lp.single 2 n 1) m = A (lp.single 2 m 1) n := by
  change hilbertCotangentCoefficients ((dualPairing (lp.single 2 n 1)).comp A) m = _
  rw [hilbertCotangentCoefficients_apply]
  exact dualPairing_hilbert_single_left _ _

theorem hilbertMatrixTranspose_involutive (A : Coeff 2 →L[ℂ] Coeff 2) :
    hilbertMatrixTranspose (hilbertMatrixTranspose A) = A := by
  ext a n
  change hilbertCotangentCoefficients ((dualPairing a).comp (hilbertMatrixTranspose A)) n = _
  rw [hilbertCotangentCoefficients_apply]
  change dualPairing a (hilbertMatrixTranspose A (lp.single 2 n 1)) = _
  rw [dualPairing_hilbert_comm, dualPairing_hilbertMatrixTranspose,
    dualPairing_hilbert_single_left]

/-- Vanishing of the transpose kernel is exactly density of the original operator's range. -/
theorem injective_hilbertMatrixTranspose_iff_denseRange (A : Coeff 2 →L[ℂ] Coeff 2) :
    Function.Injective (hilbertMatrixTranspose A) ↔ DenseRange A := by
  constructor
  · intro hi
    have ho : A.rangeᗮ = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro a ha
      have hz : hilbertMatrixTranspose A (star a) = 0 := by
        ext m
        rw [hilbertMatrixTranspose_apply]
        have h := ((A.range.mem_orthogonal' a).mp ha) (A (lp.single 2 m 1)) ⟨_,rfl⟩
        simpa only [lp.inner_eq_tsum, RCLike.inner_apply', starRingEnd_apply, lp.star_apply, lp.coeFn_zero, Pi.zero_apply] using h
      have hs : star a = 0 := hi (hz.trans (map_zero _).symm)
      exact star_eq_zero.mp hs
    have hc := Submodule.topologicalClosure_eq_top_iff.mpr ho
    intro a
    change a ∈ (A.range.topologicalClosure : Set (Coeff 2))
    rw [hc]
    trivial
  · intro hd
    apply (injective_iff_map_eq_zero _).mpr
    intro a ha
    have he : (fun b : Coeff 2 => dualPairing a b) = fun _ => 0 :=
      hd.equalizer (dualPairing a).continuous continuous_const (by
        funext b
        change dualPairing a (A b) = 0
        rw [← dualPairing_hilbertMatrixTranspose, ha, map_zero]
        rfl)
    ext n
    have hn := congrFun he (lp.single 2 n 1)
    simpa only [dualPairing_hilbert_single_right, lp.coeFn_zero, Pi.zero_apply] using hn

end NLS.Coeff
