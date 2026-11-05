import NLS.MKdV.MiuraCartesianFreeDifferential
import NLS.SequenceSpaces.PositiveWeightedCoefficients

/-! # The Cartesian map in its natural positive-index Banach target

The closed positive-frequency target removes unused encoding slots.
Projection retains all actual Cartesian variables and the signed mean.
Its actual free derivative is identified at every positive coordinate.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraPositiveHalf := WeightedCoeff.positiveSubmodule (Weight.sobolev (1/2)) 2
abbrev MiuraPositiveCartesianTarget := (MiuraPositiveHalf × MiuraPositiveHalf) × ℂ

def miuraPositiveCartesianProjection : MiuraL2CartesianTarget × ℂ →L[ℂ] MiuraPositiveCartesianTarget :=
  ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2).prodMap
    (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2)).prodMap (ContinuousLinearMap.id ℂ ℂ)

def miuraPositiveCartesianMap (a : Coeff 2) : MiuraPositiveCartesianTarget :=
  miuraPositiveCartesianProjection (miuraL2CartesianMeanMap a)

theorem analyticAt_miuraPositiveCartesianMap (a : Coeff 2) (ha : ∀ j, a j = conj (a (-j))) :
    AnalyticAt ℂ miuraPositiveCartesianMap a :=
  (miuraPositiveCartesianProjection.analyticAt _).comp (analyticAt_miuraL2CartesianMeanMap a ha)

def miuraPositiveCartesianEval (n : ℤ) : MiuraPositiveCartesianTarget →L[ℂ] (ℂ × ℂ) :=
  let e := (WeightedCoeff.evalCLM (Weight.sobolev (1/2)) 2 n).comp MiuraPositiveHalf.subtypeL
  let f := ContinuousLinearMap.fst ℂ (MiuraPositiveHalf × MiuraPositiveHalf) ℂ
  ((e.comp (ContinuousLinearMap.fst ℂ MiuraPositiveHalf MiuraPositiveHalf)).comp f).prod
    ((e.comp (ContinuousLinearMap.snd ℂ MiuraPositiveHalf MiuraPositiveHalf)).comp f)

@[simp] theorem miuraPositiveCartesianEval_apply (n : ℤ) (z : MiuraPositiveCartesianTarget) :
    miuraPositiveCartesianEval n z = (z.1.1.val.val n,z.1.2.val.val n) := rfl

/-- The actual free bounded Jacobian in the natural full positive target. -/
def miuraCartesianFreeJacobian : Coeff 2 →L[ℂ] MiuraPositiveCartesianTarget :=
  fderiv ℂ miuraPositiveCartesianMap 0

theorem miuraCartesianFreeJacobian_positive (n : ℕ) (hn : 1 ≤ n) (h : Coeff 2) :
    miuraPositiveCartesianEval n (miuraCartesianFreeJacobian h) =
      (sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*
          (sourceBirkhoffFourier (scalarL2Diagonal h)).1 n,
       -(sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*
          (sourceBirkhoffFourier (scalarL2Diagonal h)).2 n)) := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  obtain ⟨U,hU,h0U,_,hcoord⟩ := exists_local_miuraL2CartesianSequence_analytic 0 hzero
  have hnZ : (0 : ℤ) < n := by omega
  have he : (fun a => miuraPositiveCartesianEval n (miuraPositiveCartesianMap a)) =ᶠ[𝓝 (0 : Coeff 2)]
      miuraL2CartesianCoordinates n := by
    filter_upwards [hU.mem_nhds h0U] with a ha
    have h := hcoord a ha n
    change ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).1).val.val n,
      (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence a).2).val.val n) = _
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hnZ,if_pos hnZ]
    simpa only [miuraL2CartesianCoefficient,if_pos hnZ,Int.toNat_natCast] using! h
  have hd := (miuraPositiveCartesianEval (n : ℤ)).hasFDerivAt.comp (0 : Coeff 2)
    (analyticAt_miuraPositiveCartesianMap 0 hzero).differentiableAt.hasFDerivAt
  have hf := congrArg (fun L : Coeff 2 →L[ℂ] (ℂ × ℂ) => L h) hd.fderiv
  have hg := congrArg (fun L : Coeff 2 →L[ℂ] (ℂ × ℂ) => L h) he.fderiv_eq
  exact hf.symm.trans (hg.trans (fderiv_miuraL2CartesianCoordinates_zero n hn h))

theorem miuraCartesianFreeJacobian_mean (h : Coeff 2) : (miuraCartesianFreeJacobian h).2 = h 0 := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  have hd := (ContinuousLinearMap.snd ℂ (MiuraPositiveHalf × MiuraPositiveHalf) ℂ).hasFDerivAt.comp (0 : Coeff 2)
    (analyticAt_miuraPositiveCartesianMap 0 hzero).differentiableAt.hasFDerivAt
  have he := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hd.fderiv
  change (fderiv ℂ (fun a : Coeff 2 => a 0) 0) h = (miuraCartesianFreeJacobian h).2 at he
  change (fderiv ℂ ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0) : Coeff 2 → ℂ) 0) h = _ at he
  rw [(lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).fderiv] at he
  exact he.symm

end NLS.MKdV
