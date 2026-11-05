import NLS.MKdV.MiuraCartesianRotations
import NLS.MKdV.MiuraCartesianPlaneCanonical

/-! # Every actual Cartesian Jacobian row and its Gardner action image -/
noncomputable section
open Set Complex Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraCartesianJacobian_eval (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (m : ℕ) (hm : 1 ≤ m) (h : Coeff 2) :
    miuraPositiveCartesianEval m (fderiv ℂ miuraPositiveCartesianMap a h) =
      fderiv ℂ (miuraL2CartesianCoordinates m) a h := by
  obtain ⟨U,hU,haU,_,hcoord⟩ := exists_local_miuraL2CartesianSequence_analytic a ha
  have hmZ : (0 : ℤ) < m := by omega
  have he : (fun b => miuraPositiveCartesianEval m (miuraPositiveCartesianMap b)) =ᶠ[𝓝 a]
      miuraL2CartesianCoordinates m := by
    filter_upwards [hU.mem_nhds haU] with b hb
    have hc := hcoord b hb m
    change ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence b).1).val.val m,
      (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence b).2).val.val m) = _
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hmZ,if_pos hmZ]
    simpa only [miuraL2CartesianCoefficient,if_pos hmZ,Int.toNat_natCast] using! hc
  have hd := (miuraPositiveCartesianEval (m : ℤ)).hasFDerivAt.comp a
    (analyticAt_miuraPositiveCartesianMap a ha).differentiableAt.hasFDerivAt
  have hf := congrArg (fun L : Coeff 2 →L[ℂ] (ℂ × ℂ) => L h) hd.fderiv
  have hg := congrArg (fun L : Coeff 2 →L[ℂ] (ℂ × ℂ) => L h) he.fderiv_eq
  exact hf.symm.trans hg

theorem miuraCartesianJacobian_mean (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) (h : Coeff 2) :
    (fderiv ℂ miuraPositiveCartesianMap a h).2 = h 0 := by
  have hd := (ContinuousLinearMap.snd ℂ (MiuraPositiveHalf × MiuraPositiveHalf) ℂ).hasFDerivAt.comp a
    (analyticAt_miuraPositiveCartesianMap a ha).differentiableAt.hasFDerivAt
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv
  change (fderiv ℂ (fun b : Coeff 2 => b 0) a) h = (fderiv ℂ miuraPositiveCartesianMap a h).2 at he
  change (fderiv ℂ ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0) : Coeff 2 → ℂ) a) h = _ at he
  rw [(lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).fderiv] at he
  exact he.symm

theorem miuraCartesianJacobian_Gardner_action (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) :
    fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
        (l2GardnerDirection (miuraL2Action n) (scalarInclusion a)) =
      miuraCartesianActionVector n (miuraPositiveCartesianMap (scalarInclusion a)) := by
  have har : ∀ j, scalarInclusion a j = conj (scalarInclusion a (-j)) := by
    intro j
    simpa only [scalarInclusion_apply] using ha j
  apply WeightedCoeff.positivePairMean_ext
  · intro k hk
    have hi : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk.le
    have hnat : 1 ≤ k.toNat := by omega
    have hd := miuraCartesianJacobian_eval (scalarInclusion a) har k.toNat hnat
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))
    rw [hi] at hd
    change miuraPositiveCartesianEval k (fderiv ℂ miuraPositiveCartesianMap (scalarInclusion a)
      (l2GardnerDirection (miuraL2Action n) (scalarInclusion a))) =
        miuraPositiveCartesianEval k (miuraCartesianActionVector n (miuraPositiveCartesianMap (scalarInclusion a)))
    rw [hd,miuraCartesianActionVector_eval]
    have hM := miuraPositiveCartesianMap_positive (scalarInclusion a) har k.toNat hnat
    rw [hi] at hM
    rw [hM]
    have hkn : k = (n : ℤ) ↔ k.toNat = n := by omega
    simpa only [hkn] using fderiv_miuraCartesian_apply_Gardner_action a ha k.toNat n hnat hn
  · rw [miuraCartesianJacobian_mean (scalarInclusion a) har]
    change l2GardnerDirection (miuraL2Action n) (scalarInclusion a) 0 = 0
    rw [l2GardnerDirection,l2SpatialDerivative_apply _ (miuraActionGardner_memlp a ha n hn)]
    simp

end NLS.MKdV
