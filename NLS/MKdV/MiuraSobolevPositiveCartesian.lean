import NLS.MKdV.MiuraSobolevCartesianActions
import NLS.MKdV.MiuraCartesianFreeEquivalence
import NLS.SequenceSpaces.PositiveWeightEquivalence

/-! # Native positive Cartesian maps and actual free Sobolev derivatives -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraPositiveSobolevHalf (s : ℕ) := WeightedCoeff.positiveSubmodule (miuraCartesianWeight s) 2
abbrev MiuraPositiveSobolevTarget (s : ℕ) :=
  (MiuraPositiveSobolevHalf s × MiuraPositiveSobolevHalf s) × ℂ

def miuraSobolevPositiveProjection (s : ℕ) :
    MiuraSobolevCartesianTarget s →L[ℂ] (MiuraPositiveSobolevHalf s × MiuraPositiveSobolevHalf s) :=
  (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2).prodMap
    (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2)

def miuraSobolevPositiveCartesianMap (s : ℕ) (a : ScalarSobolev s) : MiuraPositiveSobolevTarget s :=
  (miuraSobolevPositiveProjection s (miuraSobolevCartesianSequence s a),a.val 0)

theorem analyticAt_miuraSobolevPositiveCartesianMap (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) : AnalyticAt ℂ (miuraSobolevPositiveCartesianMap s) a :=
  ((miuraSobolevPositiveProjection s).analyticAt _).comp (analyticAt_miuraSobolevCartesianSequence s a ha) |>.prod
    ((WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).analyticAt a)

def miuraSobolevPositiveEval (s : ℕ) (n : ℤ) : MiuraPositiveSobolevTarget s →L[ℂ] (ℂ × ℂ) :=
  let e := (WeightedCoeff.evalCLM (miuraCartesianWeight s) 2 n).comp (MiuraPositiveSobolevHalf s).subtypeL
  let f := ContinuousLinearMap.fst ℂ (MiuraPositiveSobolevHalf s × MiuraPositiveSobolevHalf s) ℂ
  ((e.comp (ContinuousLinearMap.fst ℂ (MiuraPositiveSobolevHalf s) (MiuraPositiveSobolevHalf s))).comp f).prod
    ((e.comp (ContinuousLinearMap.snd ℂ (MiuraPositiveSobolevHalf s) (MiuraPositiveSobolevHalf s))).comp f)

@[simp] theorem miuraSobolevPositiveEval_apply (s : ℕ) (n : ℤ) (z : MiuraPositiveSobolevTarget s) :
    miuraSobolevPositiveEval s n z = (z.1.1.val.val n,z.1.2.val.val n) := rfl

def miuraSobolevCartesianFreeJacobian (s : ℕ) : ScalarSobolev s →L[ℂ] MiuraPositiveSobolevTarget s :=
  fderiv ℂ (miuraSobolevPositiveCartesianMap s) 0

theorem miuraSobolevCartesianFreeJacobian_positive (s : ℕ) (n : ℕ) (hn : 1 ≤ n) (h : ScalarSobolev s) :
    miuraSobolevPositiveEval s n (miuraSobolevCartesianFreeJacobian s h) =
      (sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*
        (-(h.val (-(n : ℤ))+h.val n)/(Real.sqrt 2 : ℂ)),
       -(sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*
        ((h.val (-(n : ℤ))-h.val n)/((Real.sqrt 2 : ℂ)*I)))) := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by intro j; simp
  obtain ⟨U,hU,h0U,_,hcoord⟩ := exists_local_miuraSobolevCartesianSequence_analytic s 0 hzero
  have hnZ : (0 : ℤ) < n := by omega
  have he : (fun a => miuraSobolevPositiveEval s n (miuraSobolevPositiveCartesianMap s a)) =ᶠ[𝓝 (0 : ScalarSobolev s)]
      (fun a => miuraL2CartesianCoordinates n (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)) := by
    filter_upwards [hU.mem_nhds h0U] with a ha
    have hc := hcoord a ha n
    change ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a).1).val.val n,
      (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s a).2).val.val n) = _
    rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hnZ,if_pos hnZ]
    simpa only [miuraL2CartesianCoefficient,if_pos hnZ,Int.toNat_natCast] using! hc
  have hm := (miuraSobolevPositiveEval s (n : ℤ)).hasFDerivAt.comp (0 : ScalarSobolev s)
    (analyticAt_miuraSobolevPositiveCartesianMap s 0 hzero).differentiableAt.hasFDerivAt
  have hz : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  have hc0 : HasFDerivAt (miuraL2CartesianCoordinates n)
      (fderiv ℂ (miuraL2CartesianCoordinates n) 0) (hierarchySobolevJetL2 s 0 (Nat.zero_le s) (0 : ScalarSobolev s)) := by
    simpa only [map_zero] using (analyticAt_miuraL2CartesianCoordinates 0 hz n hn).differentiableAt.hasFDerivAt
  have hc := hc0.comp (0 : ScalarSobolev s) (hierarchySobolevJetL2 s 0 (Nat.zero_le s)).hasFDerivAt
  have h1 := congrArg (fun L : ScalarSobolev s →L[ℂ] (ℂ × ℂ) => L h) hm.fderiv
  have h2 := congrArg (fun L : ScalarSobolev s →L[ℂ] (ℂ × ℂ) => L h) he.fderiv_eq
  have h3 := congrArg (fun L : ScalarSobolev s →L[ℂ] (ℂ × ℂ) => L h) hc.fderiv
  have h4 := fderiv_miuraL2CartesianCoordinates_zero n hn (hierarchySobolevJetL2 s 0 (Nat.zero_le s) h)
  have hh := h1.symm.trans (h2.trans (h3.trans h4))
  simpa only [sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,scalarL2Diagonal_fst,scalarL2Diagonal_snd,
    hierarchySobolevJetL2_apply,pow_zero,one_mul] using! hh

theorem miuraSobolevCartesianFreeJacobian_mean (s : ℕ) (h : ScalarSobolev s) :
    (miuraSobolevCartesianFreeJacobian s h).2 = h.val 0 := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by intro j; simp
  have hd := (ContinuousLinearMap.snd ℂ (MiuraPositiveSobolevHalf s × MiuraPositiveSobolevHalf s) ℂ).hasFDerivAt.comp
    (0 : ScalarSobolev s) (analyticAt_miuraSobolevPositiveCartesianMap s 0 hzero).differentiableAt.hasFDerivAt
  have he := congrArg (fun L : ScalarSobolev s →L[ℂ] ℂ => L h) hd.fderiv
  change (fderiv ℂ ((WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0) : ScalarSobolev s → ℂ) 0) h = _ at he
  rw [(WeightedCoeff.evalCLM (Weight.sobolev (s : ℝ)) 2 0).fderiv] at he
  exact he.symm

end NLS.MKdV
