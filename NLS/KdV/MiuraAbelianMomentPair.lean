import NLS.KdV.MiuraAbelianPrimitiveReflection
import NLS.ZakharovShabat.SourceAbelianMomentPeriodCircle
import NLS.ZakharovShabat.SourceReflectedPeriodCircle
import NLS.ComplexAnalysis.CircleIntegralReflection
import NLS.ComplexAnalysis.NonrealCircleIntegralComparison

/-! # Pairing the actual positive and negative Miura second moments -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

/-- The negative gap contributes the opposite-frequency numerator on
the positive circle. The selected numerator index is retained literally. -/
theorem miura_secondMoment_pair_eq_circle
    (u : PeriodOneRealL2) {W : Set (CoeffPair 2)}
    {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (n k : ℤ)
    (D : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (hillMiuraRealSource u).val k) :
    A.moment n k 2 (hillMiuraRealSource u).val -
        A.moment n (-k) 2 (hillMiuraRealSource u).val =
      ∮ z in C((D.center : ℂ),D.radius),
        sourceFullAbelianPrimitive (by simp) (by norm_num) W k (z,(hillMiuraRealSource u).val)^2 *
          (sourcePsiCandidate n (z,(s n (hillMiuraRealSource u).val : Coeff 2)) -
            sourcePsiCandidate n (-z,(s n (hillMiuraRealSource u).val : Coeff 2))) /
          sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraRealSource u).val z := by
  let φ := hillMiuraRealSource u
  let h := sourcePeriodicReflection_hillMiuraDiagonal u.val
  let E := D.reflect h
  have hφ : φ.val ∈ A.sourceBall φ := mem_ball_self (A.localChart φ).radius_pos
  obtain ⟨B⟩ := (A.localChart φ).charts φ.val hφ
  let f (j : ℤ) (z : ℂ) := sourceAbelianMomentIntegrand (by simp) (by norm_num) W n j 2
    (z,((s n φ.val : Coeff 2),φ.val))
  have hf (j : ℤ) := analyticOnNhd_sourceAbelianMomentIntegrand_fixed
    (by simp) (by norm_num) W n j 2 (s n φ.val : Coeff 2) φ.val B
  have hp : CircleIntegrable (f k) (D.center : ℂ) D.radius :=
    ((hf k).continuousOn.mono D.sphere_subset_rootDomain).circleIntegrable D.radius_pos.le
  have hn : CircleIntegrable (fun z => -f (-k) (-z)) (D.center : ℂ) D.radius := by
    refine (show ContinuousOn (fun z => -f (-k) (-z)) (sphere (D.center : ℂ) D.radius) from ?_).circleIntegrable D.radius_pos.le
    intro z hz
    have hr := (h.neg_mem_rootDomain_iff z).mpr (D.sphere_subset_rootDomain hz)
    exact (((hf (-k) (-z) hr).continuousAt.comp continuous_neg.continuousAt).neg).continuousWithinAt
  rw [A.moment_eq_periodCircle φ n k 2 D, A.moment_eq_periodCircle φ n (-k) 2 E]
  change (∮ z in C((D.center : ℂ),D.radius), f k z) -
    (∮ z in C((E.center : ℂ),E.radius), f (-k) z) = _
  simp only [E,SourceCriticalRootPeriodCircle.reflect,ofReal_neg]
  rw [← circleIntegral_neg_pullback, ← circleIntegral.integral_sub hp hn]
  apply circleIntegral_eq_of_eq_on_nonreal _ _ D.center D.radius D.radius_pos
  intro z _hz hi
  dsimp only [f,sourceAbelianMomentIntegrand,sourcePsiContourIntegrandJoint,φ]
  rw [sourceFullAbelianPrimitive_hillMiuraRealSource_neg u B k z hi]
  rw [show sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraRealSource u).val (-z) =
    -sourceCanonicalRoot (by simp) (by norm_num) (hillMiuraRealSource u).val z from
      sourceCanonicalRoot_hillMiuraDiagonal_neg u.val z]
  ring

end NLS.KdV
