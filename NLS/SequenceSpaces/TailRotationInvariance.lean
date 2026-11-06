import NLS.SequenceSpaces.RealActionTorusNorm
import NLS.SequenceSpaces.RealTailRotationOrbit
import NLS.SequenceSpaces.RealCoeffNorm
import NLS.SequenceSpaces.ComplexActionStationarity
import NLS.SequenceSpaces.ComplexSignInvariance
import Mathlib.Analysis.Calculus.MeanValue

/-! # Tail rotation stationarity implies action-fiber invariance

The finite head is retained linearly. Stationarity is needed only outside
that head. A uniform torus bound allows finite rotations in a larger ball;
norm convergence then gives invariance on infinite real action fibers.
Holomorphic uniqueness supplies all independent complex tail signs.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Infinitesimal tail rotations determine every real action fiber near zero,
with the finite head kept fixed. -/
theorem eq_of_real_tail_actions_of_rotation_stationary (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (R : ℝ)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hrot : ∀ a ∈ ball 0 R, ∀ k ∉ S,
      fderiv ℂ f a (actionRotationVectorCLM p k a) = 0)
    (z w : RealCoeff p × RealCoeff p) (hz : 2*‖z‖ < R)
    (ha : ∀ n, RealCoeff.pairAction w n = RealCoeff.pairAction z n)
    (hh : ∀ n ∈ S, z.1 n = w.1 n ∧ z.2 n = w.2 n) :
    f (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) w) =
      f (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) z) := by
  let J := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  have hnorm (v : RealCoeff p × RealCoeff p) : ‖J v‖ = ‖v‖ := by
    simp [J,Prod.norm_def,RealCoeff.norm_complexCLM]
  have hmem (v : RealCoeff p × RealCoeff p)
      (hv : ∀ n, RealCoeff.pairAction v n = RealCoeff.pairAction z n) :
      J v ∈ ball 0 R := by
    simp only [mem_ball,dist_zero_right,hnorm]
    exact lt_of_le_of_lt (RealCoeff.norm_le_two_mul_of_pairAction_eq z v hv) hz
  have horbit (v : RealCoeff p × RealCoeff p)
      (hv : ∀ n, RealCoeff.pairAction v n = RealCoeff.pairAction z n)
      (k : ℤ) (hk : k ∉ S) (t : ℝ) :
      f (J (RealCoeff.actionRotation v k t)) = f (J v) := by
    let γ : ℝ → Coeff p × Coeff p := fun t => J (RealCoeff.actionRotation v k t)
    have hstay (u : ℝ) : γ u ∈ ball 0 R :=
      hmem _ (fun n => (RealCoeff.pairAction_actionRotation v k n u).trans (hv n))
    have hd (u : ℝ) : HasDerivAt (fun t => f (γ t)) 0 u := by
      have hγ := J.hasFDerivAt.comp_hasDerivAt u (RealCoeff.hasDerivAt_actionRotation v k u)
      have hdf := ((hf _ (hstay u)).differentiableAt (isOpen_ball.mem_nhds (hstay u))).hasFDerivAt.restrictScalars ℝ
      have h := hdf.comp_hasDerivAt u hγ
      have hzero : (fderiv ℂ f (γ u)).restrictScalars ℝ
          (J (RealCoeff.actionRotationVector (RealCoeff.actionRotation v k u) k)) = 0 := by
        change fderiv ℂ f (γ u) (J (RealCoeff.actionRotationVector _ k)) = 0
        rw [complex_actionRotationVector]
        exact hrot _ (hstay u) k hk
      simpa only [Function.comp_def,hzero] using h
    have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simpa [γ] using he
  have hmoves (moves : List (ℤ × ℝ)) (hs : ∀ move ∈ moves, move.1 ∉ S)
      (v : RealCoeff p × RealCoeff p)
      (hv : ∀ n, RealCoeff.pairAction v n = RealCoeff.pairAction z n) :
      f (J (RealCoeff.actionRotationSequence v moves)) = f (J v) := by
    induction moves generalizing v with
    | nil => rfl
    | cons move moves ih =>
      exact (ih (fun m hm => hs m (List.mem_cons_of_mem _ hm)) _
        (fun n => (RealCoeff.pairAction_actionRotation v move.1 n move.2).trans (hv n))).trans
        (horbit v hv move.1 (hs move (by simp)) move.2)
  have hfinite (A : Finset ℤ) : f (J (RealCoeff.splicePair z w A)) = f (J z) := by
    obtain ⟨moves,hs,hm⟩ := RealCoeff.exists_tailRotationSequence_eqOn S A z w
      (fun n => (ha n).symm) hh
    have he : RealCoeff.actionRotationSequence z moves = RealCoeff.splicePair z w A := by
      apply Prod.ext <;> ext n
      · exact (hm n).1.trans (RealCoeff.splicePair_apply z w A n).1.symm
      · exact (hm n).2.trans (RealCoeff.splicePair_apply z w A n).2.symm
    rw [← he]
    exact hmoves moves hs z (fun _ => rfl)
  have hcont := ((hf _ (hmem w ha)).differentiableAt
    (isOpen_ball.mem_nhds (hmem w ha))).continuousAt
  have hlim := hcont.tendsto.comp (J.continuous.continuousAt.tendsto.comp
    (RealCoeff.tendsto_splicePair hp z w))
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (Eventually.of_forall
    (fun A => (hfinite A).symm)))

/-- Holomorphic tail rotation stationarity supplies every independent tail
sign symmetry on a smaller common ball. The head may vanish. -/
theorem pairSignChange_invariant_of_tail_rotation_stationary (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hrot : ∀ a ∈ ball 0 R, ∀ k ∉ S,
      fderiv ℂ f a (actionRotationVectorCLM p k a) = 0)
    (e d : ℤ → Bool) (he : ∀ n ∈ S, e n = false) (hd : ∀ n ∈ S, d n = false)
    (a : Coeff p × Coeff p) (ha : a ∈ ball 0 (R/2)) :
    f (pairSignChange e d a) = f a := by
  have hsub : ball (0 : Coeff p × Coeff p) (R/2) ⊆ ball 0 R :=
    ball_subset_ball (by linarith)
  apply eqOn_pairSignChange_of_real_agreement f 0 (R/2) (by positivity)
    (by constructor <;> intro n <;> simp) (hf.mono hsub) e d (map_zero _) _ ha
  intro b hb hbr
  obtain ⟨z,rfl⟩ := (mem_realPairLocus_iff b).mp hbr
  let J := (RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)
  obtain ⟨w,hw⟩ := (mem_realPairLocus_iff _).mp (pairSignChange_mem_realPairLocus e d (J z) hbr)
  have hnorm : ‖J z‖ = ‖z‖ := by simp [J,Prod.norm_def,RealCoeff.norm_complexCLM]
  have hz : 2*‖z‖ < R := by
    simp only [mem_ball,dist_zero_right] at hb
    change ‖J z‖ < R/2 at hb
    rw [hnorm] at hb
    linarith
  have ha (n : ℤ) : RealCoeff.pairAction w n = RealCoeff.pairAction z n := by
    have heq := pairSignChange_action e d (J z) n
    rw [← hw] at heq
    have heq' : (w.1 n : ℂ)^2+(w.2 n : ℂ)^2 = (z.1 n : ℂ)^2+(z.2 n : ℂ)^2 := heq
    have hr : (w.1 n)^2+(w.2 n)^2 = (z.1 n)^2+(z.2 n)^2 := by exact_mod_cast heq'
    dsimp [RealCoeff.pairAction]
    rw [hr]
  have hh (n : ℤ) (hn : n ∈ S) : z.1 n = w.1 n ∧ z.2 n = w.2 n := by
    have hx := congrArg (fun b : Coeff p × Coeff p => b.1 n) hw
    have hy := congrArg (fun b : Coeff p × Coeff p => b.2 n) hw
    change (w.1 n : ℂ) = signChange e (J z).1 n at hx
    change (w.2 n : ℂ) = signChange d (J z).2 n at hy
    simp only [signChange_apply,he n hn,hd n hn,Bool.false_eq_true,↓reduceIte] at hx hy
    exact ⟨(Complex.ofReal_injective hx).symm,(Complex.ofReal_injective hy).symm⟩
  simpa only [hw] using eq_of_real_tail_actions_of_rotation_stationary hp S f R
    hf.differentiableOn hrot z w hz ha hh

end NLS.Coeff
