import NLS.MKdV.MiuraNormalizedCartesianHomeomorph
import NLS.MKdV.MiuraNativeActionMeanParameters
import NLS.SequenceSpaces.ContinuousTailRotationInvariants

/-! # Complete physical action fibers determine every continuous flow invariant

The conclusion uses the whole infinite native action sequence and the
literal signed mean. A continuous observable fixed by every actual action
flow is constant on every full physical action fiber, including arbitrary
support and closed actions. No finite-gap or nonzero-mean hypothesis is used.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV
variable {Y : Type*} [TopologicalSpace Y] [T1Space Y]

theorem miuraContinuousObservable_eq_of_actionMean_eq (s : ℕ) (hs : 1 ≤ s)
    (F : MiuraRealSobolevSource s → Y) (hF : Continuous F)
    (hflow : ∀ a n, 1 ≤ n → ∀ t : ℝ, F (miuraNativeRealActionFlow s a n t) = F a)
    (a b : MiuraRealSobolevSource s)
    (hJ : miuraNativeActionMeanMap s a.val = miuraNativeActionMeanMap s b.val) : F b = F a := by
  let H := miuraNativeNormalizedHomeomorph s hs
  let R := WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2
  let G : (RealCoeff 2 × RealCoeff 2) → Y := fun z => F (H.symm (miuraRealCartesianDecoder z))
  have hG : Continuous G := hF.comp (H.symm.continuous.comp miuraRealCartesianDecoder.continuous)
  have hrot : ∀ z k, k ∉ ({0} : Finset ℤ) → ∀ t : ℝ, G (RealCoeff.actionRotation z k t) = G z := by
    intro z k hk t
    have hk0 : k ≠ 0 := by simpa only [Finset.mem_singleton] using hk
    by_cases hkp : 0 < k
    · have hi : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkp.le
      have hd := miuraNative_decoded_rotation s hs z k.toNat (by omega) t
      rw [hi] at hd
      change F (H.symm (miuraRealCartesianDecoder (RealCoeff.actionRotation z k t))) = _
      rw [hd]
      exact hflow _ k.toNat (by omega) (-t)
    · have hn : k < 0 := by omega
      have hd := WeightedCoeff.positiveCartesianRealDecoder_negative_rotation (Weight.sobolev (1/2)) 2 z k hn t
      have he : miuraRealCartesianDecoder (RealCoeff.actionRotation z k t) = miuraRealCartesianDecoder z :=
        Subtype.ext hd
      change F (H.symm (miuraRealCartesianDecoder (RealCoeff.actionRotation z k t))) = _
      rw [he]
  have he : miuraPositiveCartesianActionMean (H a).val = miuraPositiveCartesianActionMean (H b).val := by
    simp only [H,miuraNativeNormalizedHomeomorph_apply]
    exact (miuraNormalizedCartesian_actionMean s a.val (fun j => a.property j)).trans
      ((congrArg (miuraNativeActionMeanEquiv s) hJ).trans
        (miuraNormalizedCartesian_actionMean s b.val (fun j => b.property j)).symm)
  have hm : (H a).val.2 = (H b).val.2 := congrArg (fun J : MiuraActionMeanTarget => J.2) he
  have hr (n : ℤ) (_hn : 0 < n) :
      ((H a).val.1.1.val.val n)^2+((H a).val.1.2.val.val n)^2 =
        ((H b).val.1.1.val.val n)^2+((H b).val.1.2.val.val n)^2 := by
    have h := congrArg (fun J : MiuraActionMeanTarget => J.1.val n) he
    simp only [miuraPositiveCartesianActionMean,miuraL2CartesianActions_apply] at h
    linear_combination 2*h
  have ha (n : ℤ) : RealCoeff.pairAction (R (H a).val) n = RealCoeff.pairAction (R (H b).val) n :=
    WeightedCoeff.pairAction_realParameters_eq_of_radii (Weight.sobolev (1/2)) 2 _ _
      (H a).property.1 (H b).property.1 hm hr n
  have hh : ∀ n ∈ ({0} : Finset ℤ), (R (H a).val).1 n = (R (H b).val).1 n ∧
      (R (H a).val).2 n = (R (H b).val).2 n := by
    intro n hn
    have hn0 : n = 0 := Finset.mem_singleton.mp hn
    subst n
    rw [(WeightedCoeff.positiveCartesianRealParameters_zero _ _ (H a).val).1,
      (WeightedCoeff.positiveCartesianRealParameters_zero _ _ (H b).val).1,
      (WeightedCoeff.positiveCartesianRealParameters_zero _ _ (H a).val).2,
      (WeightedCoeff.positiveCartesianRealParameters_zero _ _ (H b).val).2,hm]
    exact ⟨rfl,rfl⟩
  have hrec (c : MiuraRealSobolevSource s) : G (R (H c).val) = F c := by
    change F (H.symm (miuraRealCartesianDecoder (R (H c).val))) = F c
    rw [miuraRealCartesianDecoder_parameters,Homeomorph.symm_apply_apply]
  have h := RealCoeff.eq_of_continuous_tail_rotation_invariant (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    {0} G hG hrot _ _ ha hh
  rwa [hrec,hrec] at h

/-- A global factor through the actual full native actions and signed
mean exists for every continuous invariant of the complete physical flows. -/
theorem exists_miuraContinuousObservable_action_factor (s : ℕ) (hs : 1 ≤ s)
    (F : MiuraRealSobolevSource s → Y) (hF : Continuous F)
    (hflow : ∀ a n, 1 ≤ n → ∀ t : ℝ, F (miuraNativeRealActionFlow s a n t) = F a) :
    ∃ f : MiuraNativeActionMeanTarget s → Y, ∀ a : MiuraRealSobolevSource s,
      f (miuraNativeActionMeanMap s a.val) = F a := by
  classical
  let f : MiuraNativeActionMeanTarget s → Y := fun q =>
    if h : ∃ a : MiuraRealSobolevSource s, miuraNativeActionMeanMap s a.val = q then F h.choose else F 0
  refine ⟨f,fun a => ?_⟩
  dsimp only [f]
  rw [dif_pos (show ∃ b : MiuraRealSobolevSource s, miuraNativeActionMeanMap s b.val = miuraNativeActionMeanMap s a.val from ⟨a,rfl⟩)]
  exact miuraContinuousObservable_eq_of_actionMean_eq s hs F hF hflow a _
    (Exists.choose_spec (show ∃ b : MiuraRealSobolevSource s, miuraNativeActionMeanMap s b.val = miuraNativeActionMeanMap s a.val from ⟨a,rfl⟩)).symm

end NLS.MKdV
