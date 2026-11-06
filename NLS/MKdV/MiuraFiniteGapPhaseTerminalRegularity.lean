import NLS.MKdV.MiuraOppositeAbelianPhase
import NLS.KdV.HillFinitePhaseFamilyRegularity

/-! # Actual full finite-gap phase differentiability at every terminal configuration

An own open gap suffices; every other gap and every contributing divisor
may be terminal or closed. On an own closed gap the full phase is zero
along the whole orbit. The terminal derivative's canonical value remains
separate from this unconditional differentiability statement.
-/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

theorem miuraNativeFullAbelianPhase_actionFlow_closed
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j n : ℕ) (hn : 1 ≤ n) (t0 : ℝ)
    (hgap : hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t0).val
      (miuraNativeHillActionCurve s hs a j t0).property.1
      (miuraNativeHillActionCurve s hs a j t0).property.2 n = 0) (t : ℝ) :
    miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t) = 0 := by
  apply hillFullAbelianPhase_closed
  exact (congrFun (hillRealGapHalfLength_eq_of_labels (miuraNativeHillActionCurve s hs a j t)
    (miuraNativeHillActionCurve s hs a j t0) (miuraNativeHillActionCurve_labels s hs a j t0 t)) n).trans hgap

theorem differentiableAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (t : ℝ)
    (hclosed : ∀ k,k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1
      (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0) :
    DifferentiableAt ℝ (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) t := by
  by_cases hgap : hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1
      (miuraNativeHillActionCurve s hs a j t).property.2 n = 0
  · have he : (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) = fun _ => (0:ℂ) :=
      funext (miuraNativeFullAbelianPhase_actionFlow_closed s hs a j n hn t hgap)
    rw [he]
    exact differentiableAt_const _
  · have hd := differentiableAt_hillFiniteAbelianPhase_family (miuraNativeHillActionCurve s hs a j) t
      (continuous_miuraNativeHillActionCurve s hs a j).continuousAt
      (differentiableAt_miuraNativeHillActionCoefficients s hs a j hj t) n hn hgap F
    have he : (fun r => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) =ᶠ[𝓝 t]
        (fun r => hillFiniteAbelianPhase (miuraNativeHillActionCurve s hs a j r) n hn F) := by
      apply Filter.Eventually.of_forall
      intro r
      apply hillFullAbelianPhase_eq_finite_of_closed_complement
      intro k hk
      exact (congrFun (hillRealGapHalfLength_eq_of_labels (miuraNativeHillActionCurve s hs a j r)
        (miuraNativeHillActionCurve s hs a j t) (miuraNativeHillActionCurve_labels s hs a j t r)) (k+1)).trans
          (hclosed k hk)
    exact hd.congr_of_eventuallyEq he

theorem differentiableAt_miuraNativeOppositeAbelianPhase_actionFlow_finiteGap
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (j : ℕ) (hj : 1 ≤ j)
    (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) (t : ℝ)
    (hclosed : ∀ k,k ∉ F → hillRealGapHalfLength (miuraNativeHillActionCurve s hs a j t).val
      (miuraNativeHillActionCurve s hs a j t).property.1
      (miuraNativeHillActionCurve s hs a j t).property.2 (k+1) = 0) :
    DifferentiableAt ℝ (fun r => miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j r)) t :=
  (differentiableAt_miuraNativeFullAbelianPhase_actionFlow_finiteGap s hs a j hj n hn F t hclosed).star

end NLS.MKdV
