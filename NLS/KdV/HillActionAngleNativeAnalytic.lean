import NLS.KdV.HillActionAngleNativeDomain
import NLS.SequenceSpaces.PositiveWeightedAnalyticRealization
import NLS.SequenceSpaces.PairNorm

/-! FULL native Banach-source analyticity of the ACTUAL Cartesian
sequence map into the literal positive-index minus-half weighted Hilbert PAIR target.
Literal positive coordinates, real values and action identities are retained.
Gardner canonicality and global Birkhoff bijectivity are separate. -/
noncomputable section
open Set Metric Complex NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV

theorem analyticOnNhd_hillHminusActionAngleXSequence :
    AnalyticOnNhd ℂ hillHminusActionAngleXSequence hillHminusActionAngleNativeDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact (WeightedCoeff.analytic_positive_realization_of_bound (Weight.positiveSobolev (-1/2))
    (fun a n => hillHminusActionAngleX n a) B.source_open
    (fun n => (analyticOnNhd_hillHminusActionAngle_on_energy_domain n).1.mono B.subset)
    B.bound (fun a ha => ⟨hillHminusActionAngleXSequence a,
      (fun k => (B.coordinates a ha k).1),(B.norm_bound a ha).1⟩)) q hB

theorem analyticOnNhd_hillHminusActionAngleYSequence :
    AnalyticOnNhd ℂ hillHminusActionAngleYSequence hillHminusActionAngleNativeDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact (WeightedCoeff.analytic_positive_realization_of_bound (Weight.positiveSobolev (-1/2))
    (fun a n => hillHminusActionAngleY n a) B.source_open
    (fun n => (analyticOnNhd_hillHminusActionAngle_on_energy_domain n).2.mono B.subset)
    B.bound (fun a ha => ⟨hillHminusActionAngleYSequence a,
      (fun k => (B.coordinates a ha k).2),(B.norm_bound a ha).2⟩)) q hB

def hillHminusNativeCartesianMap (q : PeriodOneHminusOne) : WeightedCoeffPair (Weight.positiveSobolev (-1/2)) 2 :=
  (WeightedCoeffPair.toMax (Weight.positiveSobolev (-1/2)) 2).symm
    (hillHminusActionAngleXSequence q,hillHminusActionAngleYSequence q)

theorem analyticOnNhd_hillHminusNativeCartesianMap :
    AnalyticOnNhd ℂ hillHminusNativeCartesianMap hillHminusActionAngleNativeDomain := by
  intro q hq
  exact ((WeightedCoeffPair.toMax (Weight.positiveSobolev (-1/2)) 2).symm.toContinuousLinearMap.analyticAt _).comp
    ((analyticOnNhd_hillHminusActionAngleXSequence q hq).prod
      (analyticOnNhd_hillHminusActionAngleYSequence q hq))

theorem hillHminusNativeCartesianMap_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusNativeCartesianMap q).fst.val ((n:ℕ):ℤ) = hillHminusActionAngleX n q ∧
      (hillHminusNativeCartesianMap q).snd.val ((n:ℕ):ℤ) = hillHminusActionAngleY n q :=
  hillHminusActionAngle_sequences_positive q hq n

theorem hillHminusNativeCartesianMap_nonpositive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (k : ℤ) (hk : k ≤ 0) :
    (hillHminusNativeCartesianMap q).fst.val k = 0 ∧ (hillHminusNativeCartesianMap q).snd.val k = 0 :=
  hillHminusActionAngle_sequences_nonpositive q hq k hk

theorem hillHminusNativeCartesianMap_real (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (k : ℤ) :
    ((hillHminusNativeCartesianMap q).fst.val k).im = 0 ∧
      ((hillHminusNativeCartesianMap q).snd.val k).im = 0 := by
  have hq := real_mem_hillHminusActionAngleNativeDomain q hr
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨n,rfl⟩ := hk
    change ((hillHminusActionAngleXSequence q).val ((n:ℕ):ℤ)).im = 0 ∧
      ((hillHminusActionAngleYSequence q).val ((n:ℕ):ℤ)).im = 0
    have h := hillHminusActionAngle_sequences_positive q hq n
    rw [h.1,h.2]
    exact hillHminusActionAngle_real n q hr
  · change ((hillHminusActionAngleXSequence q).val k).im = 0 ∧
      ((hillHminusActionAngleYSequence q).val k).im = 0
    have h := hillHminusActionAngle_sequences_coordinates q hq k
    simp only [h.1,h.2,positiveScalarExtension_zero_of_not_mem_range _ k hk,Complex.zero_im,and_self]

theorem hillHminusNativeCartesianMap_action_identity (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    ((hillHminusNativeCartesianMap q).fst.val ((n:ℕ):ℤ))^2+
      ((hillHminusNativeCartesianMap q).snd.val ((n:ℕ):ℤ))^2 = 2*hillHminusCanonicalAction n q := by
  have h := hillHminusNativeCartesianMap_positive q hq n
  rw [h.1,h.2]
  exact hillHminusActionAngle_sum_squares n q
    (hillHminusActionAngleEnergyDomain_subset (hillHminusActionAngleNativeDomain_subset hq)).1

theorem exists_locally_uniform_hillHminusNativeCartesianMap_norm_bound :
    ∀ q ∈ hillHminusActionAngleNativeDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleNativeDomain ∧
      ∃ C : ℝ, 0 < C ∧ ∀ a ∈ U, ‖hillHminusNativeCartesianMap a‖ ≤ C := by
  intro q hq
  obtain ⟨U,hU,hqU,hUD,M,hM,hbound⟩ := exists_locally_uniform_actionAngle_native_norm_bound q hq
  let K := (2:ℝ)^(1/(2:ℝ≥0∞).toReal)
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨U,hU,hqU,hUD,K*M,mul_pos hK hM,?_⟩
  intro a ha
  have h := hbound a ha
  have hp : ‖(hillHminusActionAngleXSequence a,hillHminusActionAngleYSequence a)‖ ≤ M := max_le h.1 h.2
  exact (WeightedCoeffPair.norm_toMax_symm_le (by norm_num) (Weight.positiveSobolev (-1/2)) _).trans
    (mul_le_mul_of_nonneg_left hp hK.le)

end NLS.KdV
