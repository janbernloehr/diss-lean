import NLS.MKdV.MiuraRealSobolevCartesianCompatibility

/-! # The complex native Cartesian germ commutes with the original L² inclusions -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevPositiveCartesianMap_eval_sequence (s : ℕ) (b : ScalarSobolev s) (n : ℤ) (hn : 0 < n) :
    miuraSobolevPositiveEval s n (miuraSobolevPositiveCartesianMap s b) =
      ((miuraSobolevCartesianSequence s b).1.val n,(miuraSobolevCartesianSequence s b).2.val n) := by
  change ((WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s b).1).val.val n,
    (WeightedCoeff.positiveProjection (miuraCartesianWeight s) 2 (miuraSobolevCartesianSequence s b).2).val.val n) = _
  rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hn,if_pos hn]

theorem miuraPositiveCartesianMap_eval_sequence (b : Coeff 2) (n : ℤ) (hn : 0 < n) :
    miuraPositiveCartesianEval n (miuraPositiveCartesianMap b) =
      ((miuraL2CartesianSequence b).1.val n,(miuraL2CartesianSequence b).2.val n) := by
  change ((WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence b).1).val.val n,
    (WeightedCoeff.positiveProjection (Weight.sobolev (1/2)) 2 (miuraL2CartesianSequence b).2).val.val n) = _
  rw [WeightedCoeff.positiveProjection_apply,WeightedCoeff.positiveProjection_apply,if_pos hn,if_pos hn]

theorem miuraSobolevCartesianMap_L2_of_sequence (s : ℕ) (b : ScalarSobolev s)
    (hseq : ∀ n, ((miuraSobolevCartesianSequence s b).1.val n,(miuraSobolevCartesianSequence s b).2.val n) =
      ((miuraL2CartesianSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b)).1.val n,
       (miuraL2CartesianSequence (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b)).2.val n)) :
    miuraPositiveSobolevL2CartesianInclusion s (miuraSobolevPositiveCartesianMap s b) =
      miuraPositiveCartesianMap (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b) := by
  apply WeightedCoeff.positivePairMean_ext
  · intro n hn
    change miuraPositiveCartesianEval n (miuraPositiveSobolevL2CartesianInclusion s
      (miuraSobolevPositiveCartesianMap s b)) = miuraPositiveCartesianEval n (miuraPositiveCartesianMap _)
    rw [miuraPositiveSobolevL2CartesianInclusion_eval,
      miuraSobolevPositiveCartesianMap_eval_sequence s b n hn,miuraPositiveCartesianMap_eval_sequence _ n hn]
    exact hseq n
  · rw [miuraPositiveSobolevL2CartesianInclusion_mean]
    change b.val 0 = hierarchySobolevJetL2 s 0 (Nat.zero_le s) b 0
    simp only [hierarchySobolevJetL2_apply,pow_zero,one_mul]

theorem miuraSobolevCartesianSequence_coefficients_eventually (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∀ᶠ b in 𝓝 a, ∀ n : ℤ,
      ((miuraSobolevCartesianSequence s b).1.val n,(miuraSobolevCartesianSequence s b).2.val n) =
        miuraL2CartesianCoefficient (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b) n := by
  obtain ⟨U,hU,haU,_,hcoord⟩ := exists_local_miuraSobolevCartesianSequence_analytic s a ha
  exact Filter.mem_of_superset (hU.mem_nhds haU) (fun b hb => hcoord b hb)

theorem miuraL2CartesianSequence_coefficients_eventually (a : Coeff 2)
    (ha : ∀ j, a j = conj (a (-j))) :
    ∀ᶠ b in 𝓝 a, ∀ n : ℤ,
      ((miuraL2CartesianSequence b).1.val n,(miuraL2CartesianSequence b).2.val n) =
        miuraL2CartesianCoefficient b n := by
  obtain ⟨U,hU,haU,_,hcoord⟩ := exists_local_miuraL2CartesianSequence_analytic a ha
  exact Filter.mem_of_superset (hU.mem_nhds haU) (fun b hb => hcoord b hb)

theorem miuraSobolevL2Inclusion_real (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
  intro j
  simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j

theorem miuraSobolevCartesianMap_L2_eventually (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (fun b => miuraPositiveSobolevL2CartesianInclusion s (miuraSobolevPositiveCartesianMap s b)) =ᶠ[𝓝 a]
      (fun b => miuraPositiveCartesianMap (hierarchySobolevJetL2 s 0 (Nat.zero_le s) b)) := by
  have hnative := miuraSobolevCartesianSequence_coefficients_eventually s a ha
  have hl2 := ((hierarchySobolevJetL2 s 0 (Nat.zero_le s)).continuous.continuousAt.tendsto).eventually
    (miuraL2CartesianSequence_coefficients_eventually _ (miuraSobolevL2Inclusion_real s a ha))
  filter_upwards [hnative,hl2] with b hb hc
  exact miuraSobolevCartesianMap_L2_of_sequence s b (fun n => (hb n).trans (hc n).symm)

theorem miuraSobolevCartesianJacobian_L2 (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    (miuraPositiveSobolevL2CartesianInclusion s).comp (fderiv ℂ (miuraSobolevPositiveCartesianMap s) a) =
      (fderiv ℂ miuraPositiveCartesianMap (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a)).comp
        (hierarchySobolevJetL2 s 0 (Nat.zero_le s)) := by
  have hr : ∀ j, hierarchySobolevJetL2 s 0 (Nat.zero_le s) a j =
      conj (hierarchySobolevJetL2 s 0 (Nat.zero_le s) a (-j)) := by
    intro j
    simpa only [hierarchySobolevJetL2_apply,pow_zero,one_mul] using ha j
  have hn := (miuraPositiveSobolevL2CartesianInclusion s).hasFDerivAt.comp a
    (analyticAt_miuraSobolevPositiveCartesianMap s a ha).differentiableAt.hasFDerivAt
  have hl := (analyticAt_miuraPositiveCartesianMap _ hr).differentiableAt.hasFDerivAt.comp a
    (hierarchySobolevJetL2 s 0 (Nat.zero_le s)).hasFDerivAt
  exact hn.fderiv.symm.trans ((miuraSobolevCartesianMap_L2_eventually s a ha).fderiv_eq.trans hl.fderiv)

end NLS.MKdV
