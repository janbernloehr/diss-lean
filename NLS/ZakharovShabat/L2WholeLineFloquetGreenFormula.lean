import NLS.ZakharovShabat.L2FloquetGreenKernelAction
import NLS.ZakharovShabat.L2WholeLineDiagonalGreenFormula
import NLS.ZakharovShabat.L2WholeLineNonrealFloquetInverse

/-! # The original physical nonreal resolvent is the one-sided matrix Green integral -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Matrix Module Complex
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The existing physical resolvent has the stable/unstable full-fundamental
Green formula for forcing which vanishes outside a finite interval. -/
theorem wholeLineNonrealResolvent_ae_green_formula (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im ≠ 0)
    (μ ν : ℂ) (hne : μ ≠ ν) (b : Basis (Fin 2) ℂ (Fin 2 → ℂ))
    (hμ : l2Monodromy u z *ᵥ b 0 = μ • b 0)
    (hν : l2Monodromy u z *ᵥ b 1 = ν • b 1)
    (hstable : (Complex.log μ).re < 0) (hunstable : 0 < (Complex.log ν).re)
    (C : ℝ) (hC : ∀ t, ‖l2FloquetPeriodicMatrix u z b ![μ,ν] t‖ ≤ C ∧
      ‖(l2FloquetPeriodicMatrix u z b ![μ,ν] t)⁻¹‖ ≤ C)
    (g : WholeLineL2) (a c : ℝ)
    (hleft : ∀ᵐ t : ℝ, t ≤ a → wholeLineL2Pair g t = 0)
    (hright : ∀ᵐ t : ℝ, c ≤ t → wholeLineL2Pair g t = 0) :
    wholeLineL2Pair (wholeLineNonrealResolvent u hu z hz g) =ᵐ[volume]
      (fun t => (∫ s in a..t, wholeLineMatrixAction (l2FloquetModeKernel u z μ ν t s)
        (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2))-
      ∫ s in t..c, wholeLineMatrixAction (l2FloquetModeKernel u z ν μ t s)
        (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)) := by
  let B := l2FloquetPeriodicMatrix u z b ![μ,ν]
  let h := wholeLineMatrixMulCLM (fun s => (B s)⁻¹)
    (continuous_inv_l2FloquetPeriodicMatrix u z b ![μ,ν]) C (fun s => (hC s).2)
      (wholeLinePencilForcing g)
  have hh : wholeLineL2Pair h =ᵐ[volume] (fun s => wholeLineMatrixAction (B s)⁻¹
      (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2)) := by
    filter_upwards [wholeLineMatrixMulCLM_pair_ae (fun s => (B s)⁻¹)
      (continuous_inv_l2FloquetPeriodicMatrix u z b ![μ,ν]) C (fun s => (hC s).2)
        (wholeLinePencilForcing g),wholeLinePencilForcing_pair_ae g] with s hs hg
    rw [hs,hg]
  have hl : ∀ᵐ s : ℝ, s ≤ a → wholeLineL2Pair h s = 0 := by
    filter_upwards [hh,hleft] with s hs hg
    intro hsa
    rw [hs,hg hsa]
    simp [wholeLineMatrixAction]
  have hr : ∀ᵐ s : ℝ, c ≤ s → wholeLineL2Pair h s = 0 := by
    filter_upwards [hh,hright] with s hs hg
    intro hcs
    rw [hs,hg hcs]
    simp [wholeLineMatrixAction]
  have hi0 (t : ℝ) :
      (∫ s in a..t, Complex.exp (Complex.log μ*((t-s : ℝ) : ℂ))*wholeLineFirstCoordinate h s) •
        l2FloquetPeriodicColumn u z (b 0) μ t =
      ∫ s in a..t, wholeLineMatrixAction (l2FloquetModeKernel u z μ ν t s)
        (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2) := by
    rw [← intervalIntegral.integral_smul_const]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [wholeLineFirstCoordinate_ae h,hh] with s hs hh'
    intro _
    rw [hs,hh',l2FloquetModeKernel_action_first u z μ ν hne b hμ hν]
  have hi1 (t : ℝ) :
      (∫ s in t..c, Complex.exp (Complex.log ν*((t-s : ℝ) : ℂ))*wholeLineSecondCoordinate h s) •
        l2FloquetPeriodicColumn u z (b 1) ν t =
      ∫ s in t..c, wholeLineMatrixAction (l2FloquetModeKernel u z ν μ t s)
        (I*(wholeLineL2Pair g s).1,-I*(wholeLineL2Pair g s).2) := by
    rw [← intervalIntegral.integral_smul_const]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [wholeLineSecondCoordinate_ae h,hh] with s hs hh'
    intro _
    rw [hs,hh',l2FloquetModeKernel_action_second u z μ ν hne b hμ hν]
  rw [← wholeLineFloquetInverse_eq_nonrealResolvent u hu z hz b ![μ,ν]
    hstable.ne hunstable.ne' C hC]
  let y := wholeLineDiagonalODEInverse (Complex.log μ) (Complex.log ν)
    hstable.ne hunstable.ne' h
  change wholeLineL2Pair (wholeLineMatrixMulCLM B
    (continuous_l2FloquetPeriodicMatrix u z b ![μ,ν]) C (fun s => (hC s).1) y) =ᵐ[volume] _
  filter_upwards [wholeLineMatrixMulCLM_pair_ae B
    (continuous_l2FloquetPeriodicMatrix u z b ![μ,ν]) C (fun s => (hC s).1) y,
    wholeLineDiagonalODEInverse_ae_green_integrals (Complex.log μ) (Complex.log ν)
      hstable hunstable h a c hl hr] with t ht hy
  change wholeLineL2Pair y t = _ at hy
  rw [ht,hy,wholeLineMatrixAction_columns]
  change (∫ s in a..t, Complex.exp (Complex.log μ*((t-s : ℝ) : ℂ))*wholeLineFirstCoordinate h s) •
      l2FloquetPeriodicColumn u z (b 0) μ t+
    (-(∫ s in t..c, Complex.exp (Complex.log ν*((t-s : ℝ) : ℂ))*wholeLineSecondCoordinate h s)) •
      l2FloquetPeriodicColumn u z (b 1) ν t = _
  rw [neg_smul,hi0,hi1,sub_eq_add_neg]

end NLS.ZakharovShabat
