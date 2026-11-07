import NLS.KdV.HillActualZeroUniformEnergyGapOffset

/-! ONE OPEN CONNECTED complex native neighborhood of the ENTIRE real
Hminus-one form has the actual original Hill energy zero estimate
O(gamma_m^2/m), locally uniformly at EVERY complex source and uniformly
before ALL numerator and gap indices. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusEnergyGapOffsetBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusCanonicalZeroSequenceDomain ∩ hillHminusCanonicalGapDomain
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  offset : ∀ q ∈ ball center radius, ∀ n m : ℕ+,
    ‖hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q)-hillHminusCanonicalEnergyMidpoint m q‖ ≤
      bound*‖hillHminusCanonicalGapSquare m q‖/(m:ℝ)

namespace HillHminusEnergyGapOffsetBall

def source (B : HillHminusEnergyGapOffsetBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillHminusEnergyGapOffsetBall) : IsOpen B.source := isOpen_ball

end HillHminusEnergyGapOffsetBall

theorem exists_hillHminusEnergyGapOffsetBall (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusEnergyGapOffsetBall, B.center = q ∧ q ∈ B.source := by
  obtain ⟨P,hP,_⟩ := exists_hillProductEquationPatch q hq
  obtain ⟨r,C,hr,hC,hU,hbound⟩ := P.exists_common_actual_zero_uniform_squared_energy_gap_offset q hP hq
  exact ⟨⟨q,hq,r,hr,hU,C,hC,hbound⟩,rfl,mem_ball_self hr⟩

def hillHminusFineZeroSequenceDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusEnergyGapOffsetBall, B.source

theorem isOpen_hillHminusFineZeroSequenceDomain : IsOpen hillHminusFineZeroSequenceDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusFineZeroSequenceDomain_subset :
    hillHminusFineZeroSequenceDomain ⊆ hillHminusCanonicalZeroSequenceDomain ∩ hillHminusCanonicalGapDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem real_mem_hillHminusFineZeroSequenceDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusFineZeroSequenceDomain := by
  obtain ⟨B,_,hB⟩ := exists_hillHminusEnergyGapOffsetBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusFineZeroSequenceDomain : IsConnected hillHminusFineZeroSequenceDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusEnergyGapOffsetBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusEnergyGapOffsetBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusEnergyGapOffsetBall, S ∪ B.source) = hillHminusFineZeroSequenceDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusFineZeroSequenceDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusFineZeroSequenceDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem exists_locally_uniform_hillHminus_zero_squared_energy_gap_offset
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusFineZeroSequenceDomain) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ball q r ⊆ hillHminusFineZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n m : ℕ+,
        ‖hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n y)-hillHminusCanonicalEnergyMidpoint m y‖ ≤
          C*‖hillHminusCanonicalGapSquare m y‖/(m:ℝ) := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp B.source_open q hB
  exact ⟨r,B.bound,hr,B.bound_nonneg,(fun y hy => mem_iUnion.mpr ⟨B,hball hy⟩),
    fun y hy n m => B.offset y (hball hy) n m⟩

end NLS.KdV
