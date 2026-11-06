import NLS.MKdV.MiuraNativeFiniteGapApproximation

/-! # Actual independent phase rotation with arbitrary action support

Norm convergence of genuine finite-gap profiles, continuity of the actual
action group in its initial data, and continuity of the independent phase
on its exact own-open domain remove the finite-gap restriction. The full
unit-phase product then descends to all physical actions and signed mean.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.MKdV

theorem continuousAt_miuraNativeOppositeAbelianPhase
    (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) (a : MiuraRealSobolevSource s)
    (ha : miuraNativeNLSAngularCoordinate s n a ≠ 0) :
    ContinuousAt (miuraNativeOppositeAbelianPhase s hs n hn) a := by
  have hopen : IsOpen {b : MiuraRealSobolevSource s | miuraNativeNLSAngularCoordinate s n b ≠ 0} :=
    isOpen_ne.preimage (continuous_miuraNativeNLSAngularCoordinate s n)
  exact (continuousOn_miuraNativeOppositeAbelianPhase s hs n hn a ha).continuousAt (hopen.mem_nhds ha)

theorem miuraNativeOppositeAbelianPhase_actionFlow_open
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (ha : miuraNativeNLSAngularCoordinate s n a ≠ 0) (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t) =
      Complex.exp (-(if n = j then I else 0)*(t:ℂ))*miuraNativeOppositeAbelianPhase s hs n hn a := by
  have happrox := tendsto_miuraNativeFiniteGapApproximation s hs a
  have hflow := (continuous_miuraNativeRealActionFlow_initial s hs j hj t).tendsto a |>.comp happrox
  have hQ := (continuousAt_miuraNativeOppositeAbelianPhase s hs n hn a ha).tendsto.comp happrox
  have hQflow := (continuousAt_miuraNativeOppositeAbelianPhase s hs n hn _
    (miuraNativeNLSAngularCoordinate_actionFlow_ne_zero s a n hn ha j hj t)).tendsto.comp hflow
  have he : ∀ S : Finset ℤ,
      miuraNativeOppositeAbelianPhase s hs n hn
        (miuraNativeRealActionFlow s (miuraNativeFiniteGapApproximation s hs a S) j t) =
        Complex.exp (-(if n = j then I else 0)*(t:ℂ))*
          miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeFiniteGapApproximation s hs a S) :=
    fun S => miuraNativeOppositeAbelianPhase_actionFlow_finiteGap s hs _ j hj n hn _
      (miuraNativeFiniteGapApproximation_closedComplement s hs a S) t
  have hright := hQ.const_mul (Complex.exp (-(if n = j then I else 0)*(t:ℂ)))
  exact tendsto_nhds_unique hQflow (hright.congr' (Filter.Eventually.of_forall (fun S => (he S).symm)))

theorem miuraNativeOppositeAbelianPhase_actionFlow
    (s : ℕ) (hs : 1 ≤ s) (a : MiuraRealSobolevSource s) (n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj : 1 ≤ j) (t : ℝ) :
    miuraNativeOppositeAbelianPhase s hs n hn (miuraNativeRealActionFlow s a j t) =
      Complex.exp (-(if n = j then I else 0)*(t:ℂ))*miuraNativeOppositeAbelianPhase s hs n hn a := by
  by_cases ha : miuraNativeNLSAngularCoordinate s n a = 0
  · have hn0 := (miuraNativeHill_halfLength_zero_iff_angular_zero s hs a n hn).mpr ha
    have horbit := miuraNativeFullAbelianPhase_actionFlow_closed s hs a j n hn 0
      (by simpa only [miuraNativeHillActionCurve_zero] using hn0) t
    rw [miuraNativeOppositeAbelianPhase,horbit,map_zero,
      miuraNativeOppositeAbelianPhase_closed s hs n hn a ha,mul_zero]
  · exact miuraNativeOppositeAbelianPhase_actionFlow_open s hs a n hn ha j hj t

theorem exists_miuraIndependentAbelianPhase_action_factor (s : ℕ) (hs : 1 ≤ s) (n : ℕ) (hn : 1 ≤ n) :
    ∃ f : MiuraNativeActionMeanTarget s → ℂ,∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) =
        miuraNativeNLSUnitPhase s n a*miuraNativeOppositeAbelianPhase s hs n hn a := by
  apply exists_opposite_unit_phase_action_factor s hs n hn (miuraNativeOppositeAbelianPhase s hs n hn)
    (continuousOn_miuraNativeOppositeAbelianPhase s hs n hn)
    (norm_miuraNativeOppositeAbelianPhase_le_one s hs n hn)
  intro a _ j hj t
  exact miuraNativeOppositeAbelianPhase_actionFlow s hs a n hn j hj t

end NLS.MKdV
