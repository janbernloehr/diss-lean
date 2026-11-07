import NLS.KdV.HillComplexProductConvergence
import NLS.KdV.HillEnergyProductSimpleComplexZeros
import NLS.KdV.HillPlacedEnergySequenceInjective

/-! ONE common OPEN CONNECTED complex domain of the ENTIRE real form
retains the fine original energy-gap estimate and has distinct actual
energy labels before ALL numerator indices. The proved nonzero analytic
product scalar then gives ALL complex zeros, their simplicity, and
nonvanishing at the filled omitted midpoint. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusSimpleZeroSequenceBall where
  parent : HillHminusEnergyGapOffsetBall
  injective : ∀ q ∈ parent.source, ∀ n : ℕ+,
    Function.Injective (fun m : ℕ+ => hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q))

namespace HillHminusSimpleZeroSequenceBall

def source (B : HillHminusSimpleZeroSequenceBall) : Set PeriodOneHminusOne := B.parent.source

theorem source_open (B : HillHminusSimpleZeroSequenceBall) : IsOpen B.source := B.parent.source_open

end HillHminusSimpleZeroSequenceBall

theorem exists_hillHminusSimpleZeroSequenceBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusSimpleZeroSequenceBall, B.parent.center = q ∧ q ∈ B.source := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  obtain ⟨rF,C,hrF,hC,hU,hbound⟩ := P.exists_common_actual_zero_uniform_squared_energy_gap_offset q hq hr
  obtain ⟨rP,hrP,_,hperiod⟩ := P.exists_common_canonical_zero_sequence_period_ball q hq hr
  let r := min rF rP
  have hrpos : 0 < r := lt_min hrF hrP
  let A : HillHminusEnergyGapOffsetBall := {
    center := q
    center_real := hr
    radius := r
    radius_pos := hrpos
    subset := (ball_subset_ball (min_le_left _ _)).trans hU
    bound := C
    bound_nonneg := hC
    offset := fun y hy n m => hbound y (ball_subset_ball (min_le_left _ _) hy) n m }
  refine ⟨⟨A,?_⟩,rfl,mem_ball_self hrpos⟩
  intro y hy n
  exact P.actual_complex_zero_energySequence_injective y n (hperiod y (ball_subset_ball (min_le_right _ _) hy) n).1

def hillHminusSimpleZeroSequenceDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusSimpleZeroSequenceBall, B.source

theorem isOpen_hillHminusSimpleZeroSequenceDomain : IsOpen hillHminusSimpleZeroSequenceDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusSimpleZeroSequenceDomain_subset_fineDomain :
    hillHminusSimpleZeroSequenceDomain ⊆ hillHminusFineZeroSequenceDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨B.parent,hB⟩

theorem hillHminusSimpleZeroSequenceDomain_subset_zeroDomain :
    hillHminusSimpleZeroSequenceDomain ⊆ hillHminusCanonicalZeroSequenceDomain :=
  hillHminusSimpleZeroSequenceDomain_subset_fineDomain.trans (hillHminusFineZeroSequenceDomain_subset.trans inter_subset_left)

theorem real_mem_hillHminusSimpleZeroSequenceDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusSimpleZeroSequenceDomain := by
  obtain ⟨B,_,hB⟩ := exists_hillHminusSimpleZeroSequenceBall q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusSimpleZeroSequenceDomain : IsConnected hillHminusSimpleZeroSequenceDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusSimpleZeroSequenceBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.parent.center B.parent.center_real (mem_ball_self B.parent.radius_pos)
      (convex_ball B.parent.center B.parent.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusSimpleZeroSequenceBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusSimpleZeroSequenceBall, S ∪ B.source) = hillHminusSimpleZeroSequenceDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusSimpleZeroSequenceDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusSimpleZeroSequenceDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem hillHminusCanonicalEnergyZeros_injective_of_simpleDomain (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) (n : ℕ+) :
    Function.Injective (fun m : ℕ+ => hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q)) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.injective q hB n

theorem hillHminusCanonicalPsi_complex_simple_zeros (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) (n : ℕ+) (E : ℂ)
    (hE : hillHminusCanonicalPsi n (E,q) = 0) :
    deriv (fun z : ℂ => hillHminusCanonicalPsi n (z,q)) E ≠ 0 := by
  have hU := hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hq
  obtain ⟨m,hmn,he⟩ := (hillHminusCanonicalPsi_complex_zero_iff n q hU E).mp hE
  have hinj := hillHminusCanonicalEnergyZeros_injective_of_simpleDomain q hq n
  have hD : deriv (fun z : ℂ => hillEnergySequenceProduct n (z,hillHminusCanonicalZeroSequence n q))
      (hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q)) ≠ 0 :=
    hillEnergySequenceProduct_energy_deriv_ne_zero_of_injective n m hmn (hillHminusCanonicalZeroSequence n q) hinj
  have hP : deriv (fun z : ℂ => hillHminusCanonicalZeroProduct n (z,q)) E ≠ 0 := by
    change deriv (fun z : ℂ => hillEnergySequenceProduct n (z,hillHminusCanonicalZeroSequence n q)) E ≠ 0
    rw [he]
    exact hD
  rw [hillHminusCanonicalPsi_energy_deriv_eq_scalar_mul_product n q hU E]
  exact mul_ne_zero (hillHminusCanonicalPsiProductScalar_ne_zero n q hU) hP

theorem hillHminusCanonicalPsi_complex_zero_iff_unique_index (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) (n : ℕ+) (E : ℂ) :
    hillHminusCanonicalPsi n (E,q) = 0 ↔ ∃! m : ℕ+, m ≠ n ∧
      E = hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q) := by
  rw [hillHminusCanonicalPsi_complex_zero_iff n q (hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hq) E]
  constructor
  · rintro ⟨m,hmn,he⟩
    refine ⟨m,⟨hmn,he⟩,?_⟩
    intro k hk
    exact hillHminusCanonicalEnergyZeros_injective_of_simpleDomain q hq n (hk.2.symm.trans he)
  · exact ExistsUnique.exists

theorem hillHminusCanonicalPsi_omitted_midpoint_ne_zero (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusSimpleZeroSequenceDomain) (n : ℕ+) :
    hillHminusCanonicalPsi n (hillHminusCanonicalEnergyMidpoint n q,q) ≠ 0 := by
  intro hz
  obtain ⟨m,hmn,he⟩ := (hillHminusCanonicalPsi_complex_zero_iff n q
    (hillHminusSimpleZeroSequenceDomain_subset_zeroDomain hq) _).mp hz
  exact hmn (hillHminusCanonicalEnergyZeros_injective_of_simpleDomain q hq n he).symm

theorem exists_locally_uniform_simpleDomain_squared_energy_gap_offset
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusSimpleZeroSequenceDomain) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ball q r ⊆ hillHminusSimpleZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n m : ℕ+,
        ‖hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n y)-hillHminusCanonicalEnergyMidpoint m y‖ ≤
          C*‖hillHminusCanonicalGapSquare m y‖/(m:ℝ) := by
  obtain ⟨r,C,hr,hC,_,hbound⟩ := exists_locally_uniform_hillHminus_zero_squared_energy_gap_offset q
    (hillHminusSimpleZeroSequenceDomain_subset_fineDomain hq)
  obtain ⟨s,hs,hball⟩ := Metric.isOpen_iff.mp isOpen_hillHminusSimpleZeroSequenceDomain q hq
  exact ⟨min r s,C,lt_min hr hs,hC,(ball_subset_ball (min_le_right _ _)).trans hball,
    fun y hy n m => hbound y (ball_subset_ball (min_le_left _ _) hy) n m⟩

end NLS.KdV
