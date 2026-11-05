import NLS.MKdV.MiuraNativeActionFlowDerivative
import NLS.MKdV.MiuraThetaActionDirection

/-! # The native Sobolev action velocity is the actual physical Gardner field

The derivative lifted from a finite target rotation retains the original
L² Fourier coefficients of the constructed Hamiltonian action flow.
Thus native chain rules evaluate on the original Gardner vector, rather
than on a newly prescribed coordinate velocity.
-/
noncomputable section
open Set Complex Filter Topology NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraNativeActionVelocity_L2_source (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) :
    hierarchySobolevJetL2 s 0 (Nat.zero_le _) (miuraNativeActionVelocity s a n) =
      (sourceActionDifferenceVector n (-(n : ℤ)) (miuraActionInitialSource s a.val (fun j => a.property j)).val).fst := by
  let D := miuraActionFlowFamily.data
  let φ := miuraActionInitialSource s a.val (fun j => a.property j)
  let J := hierarchySobolevJetL2 s 0 (Nat.zero_le s)
  let P : CoeffPair 2 →L[ℂ] Coeff 2 :=
    (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2)).comp (CoeffPair.toMax 2).toContinuousLinearMap
  have hd := (J.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    (hasDerivAt_miuraActionFlow_native_zero s hs a n hn)
  have hS := (P.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0
    (D.hasDerivAt_hilbertPairedActionFlow φ n (-(n : ℤ)) 0)
  have he : (fun t => J (miuraActionFlow s a.val (fun j => a.property j) n t)) =
      fun t => (D.hilbertPairedActionFlow φ n (-(n : ℤ)) t).val.fst := by
    funext t
    ext j
    rw [hierarchySobolevJetL2_apply,pow_zero,one_mul,miuraActionFlow_coefficient]
  change HasDerivAt (fun t => J (miuraActionFlow s a.val (fun j => a.property j) n t))
    (J (miuraNativeActionVelocity s a n)) 0 at hd
  rw [he] at hd
  change HasDerivAt (fun t => (D.hilbertPairedActionFlow φ n (-(n : ℤ)) t).val.fst)
    (sourceActionDifferenceVector n (-(n : ℤ)) (D.hilbertPairedActionFlow φ n (-(n : ℤ)) 0).val).fst 0 at hS
  rw [D.hilbertPairedActionFlow_zero] at hS
  exact hd.unique hS

/-- Every native positive Sobolev action velocity represents the same
actual L² Gardner derivative of the independent physical action J_n. -/
theorem miuraNativeActionVelocity_L2_Gardner (s : ℕ) (hs : 1 ≤ s)
    (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n) :
    hierarchySobolevJetL2 s 0 (Nat.zero_le _) (miuraNativeActionVelocity s a n) =
      l2GardnerDirection (miuraL2Action n) (hierarchySobolevJetL2 s 0 (Nat.zero_le _) a.val) := by
  let b := hierarchySobolevToScalarDomain s hs a.val
  have hb : ∀ j, b.val j = conj (b.val (-j)) := by
    intro j
    simpa only [b,hierarchySobolevToScalarDomain_apply] using (fun j => a.property j) j
  have hsource : (miuraActionInitialSource s a.val (fun j => a.property j)).val = sobolevSourceInclusion (b,b) := by
    rw [miuraActionInitialSource_L2_diagonal,← scalarInclusion_hierarchySobolevToScalarDomain s hs a.val,
      scalarL2Diagonal_scalarInclusion]
  have hv : sourceActionDifferenceVector n (-(n : ℤ)) (sobolevSourceInclusion (b,b)) =
      scalarL2Diagonal (l2GardnerDirection (miuraL2Action n) (scalarInclusion b)) := by
    rw [sourceActionDifferenceVector,sourceHamiltonianVector,sourceHamiltonianVector,← map_sub]
    exact miuraActionDifference_direction b hb n hn
  rw [miuraNativeActionVelocity_L2_source s hs a n hn,hsource,hv,scalarL2Diagonal_fst]
  rw [scalarInclusion_hierarchySobolevToScalarDomain s hs a.val]

end NLS.MKdV
