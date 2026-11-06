import NLS.MKdV.MiuraFinitePhaseLieContinuity

/-! # Full independent phase Lie continuity on every fixed finite-gap stratum

The entire physical action orbit preserves the closed complement. The
literal full phase and every finite partial phase containing the possible
open gaps therefore agree along the whole orbit. Their actual Lie
derivatives agree, even at terminal or closed contributing divisors.
-/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.MKdV

def miuraNativeClosedComplement (s : ℕ) (hs : 1 ≤ s) (F : Finset ℕ) : Set (MiuraRealSobolevSource s) :=
  {a | ∀ k,k ∉ F → hillRealGapHalfLength
    (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)).val
    (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)).property.1
    (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)).property.2 (k+1) = 0}

theorem miuraNativeFullAbelianPhase_actionFlow_eq_finite
    (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (a : MiuraRealSobolevSource s) (ha : a ∈ miuraNativeClosedComplement s hs F) (j : ℕ) (t : ℝ) :
    miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t) =
      miuraNativeFiniteAbelianPhase s hs n hn F (miuraNativeRealActionFlow s a j t) := by
  apply hillFullAbelianPhase_eq_finite_of_closed_complement
  intro k hk
  have hl := miuraNativeHillLabels_actionFlow s hs a j t
  exact (congrFun (hillRealGapHalfLength_eq_of_labels (miuraNativeHillActionCurve s hs a j t)
    (realSobolevMiuraHillPotential (hierarchySobolevToScalarDomain s hs a.val) (miuraNativeH1Profile_real s hs a)) hl) (k+1)).trans (ha k hk)

theorem miuraNativeFullAbelianPhase_Lie_eq_finite
    (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ)
    (a : MiuraRealSobolevSource s) (ha : a ∈ miuraNativeClosedComplement s hs F) (j : ℕ) :
    miuraNativeActionLieDerivative s j (miuraNativeFullAbelianPhase s hs n hn) a =
      miuraNativeActionLieDerivative s j (miuraNativeFiniteAbelianPhase s hs n hn F) a := by
  have he : (fun t => miuraNativeFullAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t)) =
      (fun t => miuraNativeFiniteAbelianPhase s hs n hn F (miuraNativeRealActionFlow s a j t)) :=
    funext (miuraNativeFullAbelianPhase_actionFlow_eq_finite s hs n hn F a ha j)
  exact congrArg (fun f : ℝ → ℂ => deriv f 0) he

theorem continuousOn_miuraNativeFullAbelianPhase_Lie_finiteGap
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) :
    ContinuousOn (miuraNativeActionLieDerivative s j (miuraNativeFullAbelianPhase s hs n hn))
      (miuraNativeClosedComplement s hs F ∩ {a | miuraNativeNLSAngularCoordinate s n a ≠ 0}) := by
  apply ((continuousOn_miuraNativeFiniteAbelianPhase_Lie s hs j hj n hn F).mono (fun _ h => h.2)).congr
  intro a ha
  exact miuraNativeFullAbelianPhase_Lie_eq_finite s hs n hn F a ha.1 j

theorem continuousOn_miuraNativeOppositeAbelianPhase_Lie_finiteGap
    (s : ℕ) (hs : 1 ≤ s) (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 1 ≤ n) (F : Finset ℕ) :
    ContinuousOn (miuraNativeActionLieDerivative s j (miuraNativeOppositeAbelianPhase s hs n hn))
      (miuraNativeClosedComplement s hs F ∩ {a | miuraNativeNLSAngularCoordinate s n a ≠ 0}) := by
  have he : (miuraNativeActionLieDerivative s j (miuraNativeOppositeAbelianPhase s hs n hn)) =
      fun a => conj (miuraNativeActionLieDerivative s j (miuraNativeFullAbelianPhase s hs n hn) a) :=
    funext (miuraNativeActionLieDerivative_conj s j (miuraNativeFullAbelianPhase s hs n hn))
  rw [he]
  exact continuous_conj.comp_continuousOn (continuousOn_miuraNativeFullAbelianPhase_Lie_finiteGap s hs j hj n hn F)

end NLS.MKdV
