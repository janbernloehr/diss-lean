import NLS.KdV.MiuraCanonicalRootReflection
import NLS.KdV.MiuraRealSource
import NLS.ZakharovShabat.SourceAbelianSourceContinuity
import NLS.ZakharovShabat.SourceFullAbelianPrimitive

/-! # Reflection of the normalized primitive on actual real Miura sources

The real source path from zero fixes the logarithm period, in addition
to the sign already fixed by the canonical product root.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem sourceAbelianPrimitive_hillMiuraRealSource_neg
    (u : PeriodOneRealL2) (z : ℂ) (hzi : z.im ≠ 0) :
    sourceAbelianPrimitive (by simp) (by norm_num) (hillMiuraRealSource u).val
        (hillMiuraRealSource u).property (-z) =
      -sourceAbelianPrimitive (by simp) (by norm_num) (hillMiuraRealSource u).val
        (hillMiuraRealSource u).property z := by
  let ψ : ℝ → realTypeSourceSubmodule 2 := fun s => s • hillMiuraRealSource u
  have hψ : Continuous ψ := by dsimp [ψ]; fun_prop
  have hdiag (s : ℝ) : hillMiuraDiagonal ((s : ℂ) • u.val) = (ψ s).val := by
    exact map_smul hillMiuraDiagonal (s : ℂ) u.val
  have hz (s : ℝ) : z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property z hzi
  have hnz (s : ℝ) : -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val :=
    sourceCanonicalRootDomain_of_im_ne_zero _ _ _ (ψ s).property (-z) (by simpa using hzi)
  have hc (w : ℂ) (hw : ∀ s, w ∈ sourceCanonicalRootDomain (by simp) (by norm_num) (ψ s).val) :
      Continuous (fun s => sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property w) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (continuousAt_sourceAbelianPrimitive_source _ _ (ψ s) w (hw s)).comp hψ.continuousAt
  have he := continuousLogarithms_eqOn
    (fun s => sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property (-z))
    (fun s => -sourceAbelianPrimitive (by simp) (by norm_num) (ψ s).val (ψ s).property z)
    (Icc (0 : ℝ) 1) isPreconnected_Icc (hc (-z) hnz).continuousOn (hc z hz).neg.continuousOn
    (fun s _hs => by
      rw [sourceAbelianPrimitive_exp (p := 2) (by simp) (by norm_num) (ψ s).val (ψ s).property (-z)
        (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ (hnz s)), exp_neg,
        sourceAbelianPrimitive_exp (p := 2) (by simp) (by norm_num) (ψ s).val (ψ s).property z
          (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ (hz s))]
      have hi := inv_eq_of_mul_eq_one_right
        (sourceFloquetMultiplier_mul_companion (by simp) (by norm_num) (ψ s).val z (hz s))
      rw [hi]
      unfold sourceFloquetMultiplier
      rw [← hdiag s, sourceCanonicalRoot_hillMiuraDiagonal_neg]
      change (hillMiuraFrequencyTrace _ (-z) + _) / 2 = (hillMiuraFrequencyTrace _ z - _) / 2
      rw [hillMiuraFrequencyTrace_even, sub_eq_add_neg])
    0 (by constructor <;> norm_num) (by
      simp only [ψ, zero_smul, ZeroMemClass.coe_zero, sourceAbelianPrimitive_zero]
      ring)
  simpa only [ψ, one_smul] using he (by constructor <;> norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)

theorem sourceFullAbelianPrimitive_hillMiuraRealSource_neg
    (u : PeriodOneRealL2) {W : Set (CoeffPair 2)}
    (D : SourceAbelianSpectralChart (by simp) (by norm_num) W (hillMiuraRealSource u).val)
    (k : ℤ) (z : ℂ) (hzi : z.im ≠ 0) :
    sourceFullAbelianPrimitive (by simp) (by norm_num) W (-k) (-z,(hillMiuraRealSource u).val) =
      -sourceFullAbelianPrimitive (by simp) (by norm_num) W k (z,(hillMiuraRealSource u).val) := by
  have hz := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) _
    (hillMiuraRealSource u).property z hzi
  have hnz := sourceCanonicalRootDomain_of_im_ne_zero (by simp) (by norm_num) _
    (hillMiuraRealSource u).property (-z) (by simpa using hzi)
  rw [sourceFullAbelianPrimitive_eq_real _ D _ _
      (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ hnz),
    sourceFullAbelianPrimitive_eq_real _ D _ _
      (sourceCanonicalRootDomain_subset_openGapComplement _ _ _ hz),
    sourceAbelianPrimitive_hillMiuraRealSource_neg u z hzi, Int.cast_neg]
  ring

end NLS.KdV
