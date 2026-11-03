import NLS.MKdV.MiuraCartesianFiberRotations
import NLS.SequenceSpaces.ClosedTailRotationSaturation

/-! # Global phase saturation of attained physical action fibers

Every real native Cartesian pair with prescribed attained physical radii
and signed mean has a physical original L2 preimage. That preimage can be
chosen to retain the entire original NLS action sequence of the initial
profile. This does not assert injectivity or identify the whole physical
action fiber with a single joint NLS action fiber.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

/-- The compact joint fiber's normalized image contains its entire real
tail action torus with the mean head fixed. -/
theorem real_tail_torus_mem_jointFiber_image (a : MiuraRealL2)
    (w : RealCoeff 2 × RealCoeff 2)
    (ha : ∀ n, RealCoeff.pairAction (miuraRealCartesianParameters a) n = RealCoeff.pairAction w n)
    (hh : (miuraRealCartesianParameters a).1 0 = w.1 0 ∧
      (miuraRealCartesianParameters a).2 0 = w.2 0) :
    w ∈ miuraRealCartesianParameters '' miuraJointActionFiber a := by
  let K := miuraRealCartesianParameters '' miuraJointActionFiber a
  have hK : IsClosed K :=
    ((isCompact_miuraJointActionFiber a).image continuous_miuraRealCartesianParameters).isClosed
  have hrot : ∀ x ∈ K, ∀ k ∉ ({0} : Finset ℤ), ∀ t : ℝ, RealCoeff.actionRotation x k t ∈ K := by
    rintro x ⟨b,hb,rfl⟩ k hk t
    have hk0 : k ≠ 0 := by simpa only [Finset.mem_singleton] using hk
    by_cases hkp : 0 < k
    · have hi : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hkp.le
      have hn : 1 ≤ k.toNat := by omega
      refine ⟨miuraRealL2ActionRotation b k.toNat (-t),
        miuraRealL2ActionRotation_mem_jointFiber a b hb k.toNat hn (-t),?_⟩
      simpa only [hi,neg_neg] using miuraRealCartesianParameters_actionRotation b k.toNat hn (-t)
    · have hneg : k < 0 := by omega
      have he := WeightedCoeff.actionRotation_positiveCartesianRealParameters_negative
        (Weight.sobolev (1/2)) 2 (miuraPositiveCartesianMap b.val) k hneg t
      change RealCoeff.actionRotation (miuraRealCartesianParameters b) k t = miuraRealCartesianParameters b at he
      rw [he]
      exact ⟨b,hb,rfl⟩
  apply RealCoeff.mem_of_isClosed_tail_rotation_invariant (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    {0} K hK hrot (miuraRealCartesianParameters a) ⟨a,⟨rfl,rfl⟩,rfl⟩ w ha
  intro n hn
  have hn0 : n = 0 := Finset.mem_singleton.mp hn
  simpa only [hn0] using hh

/-- Every full phase configuration at attained physical actions and mean
is realized globally, retaining every original signed NLS action. -/
theorem exists_miura_jointFiber_preimage_of_Cartesian_radii (a : MiuraRealL2)
    (z : MiuraPositiveCartesianTarget) (hz : z ∈ miuraCartesianRealSubmodule)
    (hJ : miuraPositiveCartesianActionMean z = miuraRealL2ActionMeanMap a) :
    ∃ b ∈ miuraJointActionFiber a, miuraPositiveCartesianMap b.val = z := by
  let R := WeightedCoeff.positiveCartesianRealParameters (Weight.sobolev (1/2)) 2
  have hMa := miuraPositiveCartesianMap_physicalReal a
  have he : miuraPositiveCartesianActionMean (miuraPositiveCartesianMap a.val) =
      miuraPositiveCartesianActionMean z := (miuraPositiveCartesianActionMean_map a.val a.property).trans hJ.symm
  have hm : (miuraPositiveCartesianMap a.val).2 = z.2 := congrArg (fun b : MiuraActionMeanTarget => b.2) he
  have hr (n : ℤ) (_hn : 0 < n) :
      ((miuraPositiveCartesianMap a.val).1.1.val.val n)^2+
        ((miuraPositiveCartesianMap a.val).1.2.val.val n)^2 = (z.1.1.val.val n)^2+(z.1.2.val.val n)^2 := by
    have h := congrArg (fun b : MiuraActionMeanTarget => b.1.val n) he
    simp only [miuraPositiveCartesianActionMean,miuraL2CartesianActions_apply] at h
    linear_combination 2*h
  have ha (n : ℤ) : RealCoeff.pairAction (miuraRealCartesianParameters a) n = RealCoeff.pairAction (R z) n :=
    WeightedCoeff.pairAction_realParameters_eq_of_radii (Weight.sobolev (1/2)) 2 _ z
      hMa.1 hz.1 hm hr n
  have hh : (miuraRealCartesianParameters a).1 0 = (R z).1 0 ∧
      (miuraRealCartesianParameters a).2 0 = (R z).2 0 := by
    constructor
    · change (R (miuraPositiveCartesianMap a.val)).1 0 = (R z).1 0
      rw [(WeightedCoeff.positiveCartesianRealParameters_zero (Weight.sobolev (1/2)) 2 (miuraPositiveCartesianMap a.val)).1,
        (WeightedCoeff.positiveCartesianRealParameters_zero (Weight.sobolev (1/2)) 2 z).1,hm]
    · change (R (miuraPositiveCartesianMap a.val)).2 0 = (R z).2 0
      rw [(WeightedCoeff.positiveCartesianRealParameters_zero (Weight.sobolev (1/2)) 2 (miuraPositiveCartesianMap a.val)).2,
        (WeightedCoeff.positiveCartesianRealParameters_zero (Weight.sobolev (1/2)) 2 z).2]
  obtain ⟨b,hb,hbR⟩ := real_tail_torus_mem_jointFiber_image a (R z) ha hh
  refine ⟨b,hb,?_⟩
  have hMb := miuraPositiveCartesianMap_physicalReal b
  exact WeightedCoeff.positiveCartesianRealParameters_injective_on_real (Weight.sobolev (1/2)) 2
    (miuraPositiveCartesianMap b.val) z hMb.1 hMb.2 hz.1 hz.2 hbR

def miuraCartesianPhaseFiber (a : MiuraRealL2) : Set MiuraPositiveCartesianTarget :=
  {z | z ∈ miuraCartesianRealSubmodule ∧ miuraPositiveCartesianActionMean z = miuraRealL2ActionMeanMap a}

/-- The image of the compact joint physical/NLS action fiber is exactly
the complete native Cartesian phase fiber, with its actual signed mean. -/
theorem miuraJointActionFiber_Cartesian_image (a : MiuraRealL2) :
    miuraRealPositiveCartesianMap '' miuraJointActionFiber a = miuraCartesianPhaseFiber a := by
  apply Subset.antisymm
  · rintro _ ⟨b,hb,rfl⟩
    exact ⟨miuraPositiveCartesianMap_physicalReal b,
      (miuraPositiveCartesianActionMean_map b.val b.property).trans hb.1⟩
  · intro z hz
    obtain ⟨b,hb,he⟩ := exists_miura_jointFiber_preimage_of_Cartesian_radii a z hz.1 hz.2
    exact ⟨b,hb,he⟩

theorem isCompact_miuraCartesianPhaseFiber (a : MiuraRealL2) : IsCompact (miuraCartesianPhaseFiber a) := by
  rw [← miuraJointActionFiber_Cartesian_image]
  exact (isCompact_miuraJointActionFiber a).image continuous_miuraRealPositiveCartesianMap

end NLS.MKdV
