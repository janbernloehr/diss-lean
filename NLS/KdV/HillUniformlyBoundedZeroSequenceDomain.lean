import NLS.KdV.HillCommonZeroSequenceStability
import NLS.ComplexAnalysis.BanachTaylorBounds

/-! Shrink the common analytic zero-sequence domain so that the ENTIRE
family is locally uniformly bounded at EVERY complex source. The domain
is still OPEN CONNECTED and contains the ENTIRE real Hminus-one form.
Cauchy also bounds the FULL Frechet derivatives before ALL indices. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

structure HillHminusBoundedZeroSequenceBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusCanonicalZeroSequenceDomain
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  bounded : ∀ q ∈ ball center radius, ∀ n : ℕ+, ‖hillHminusCanonicalZeroSequence n q‖ ≤ bound

namespace HillHminusBoundedZeroSequenceBall

def source (B : HillHminusBoundedZeroSequenceBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillHminusBoundedZeroSequenceBall) : IsOpen B.source := isOpen_ball

end HillHminusBoundedZeroSequenceBall

theorem exists_hillHminusBoundedZeroSequenceBall (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ B : HillHminusBoundedZeroSequenceBall, B.center = q ∧ q ∈ B.source := by
  obtain ⟨r,_,M,hr,_,hM,hU,hbound⟩ := exists_common_canonical_zero_sequence_control q hq
  exact ⟨⟨q,hq,r,hr,hU,M,hM,fun y hy n => (hbound y hy n).2⟩,rfl,mem_ball_self hr⟩

def hillHminusUniformZeroSequenceDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillHminusBoundedZeroSequenceBall, B.source

theorem isOpen_hillHminusUniformZeroSequenceDomain : IsOpen hillHminusUniformZeroSequenceDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem hillHminusUniformZeroSequenceDomain_subset :
    hillHminusUniformZeroSequenceDomain ⊆ hillHminusCanonicalZeroSequenceDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem real_mem_hillHminusUniformZeroSequenceDomain (q : PeriodOneHminusOne)
    (hq : IsRealPeriodOneHminusOne q) : q ∈ hillHminusUniformZeroSequenceDomain := by
  obtain ⟨B,_,hB⟩ := exists_hillHminusBoundedZeroSequenceBall q hq
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem isConnected_hillHminusUniformZeroSequenceDomain : IsConnected hillHminusUniformZeroSequenceDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillHminusBoundedZeroSequenceBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball B.center B.radius).isPreconnected
  have hcommon : (⋂ B : HillHminusBoundedZeroSequenceBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillHminusBoundedZeroSequenceBall, S ∪ B.source) = hillHminusUniformZeroSequenceDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusUniformZeroSequenceDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusUniformZeroSequenceDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

theorem exists_locally_uniform_hillHminusZeroSequence_norm_bound
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusUniformZeroSequenceDomain) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ball q r ⊆ hillHminusUniformZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+, ‖hillHminusCanonicalZeroSequence n y‖ ≤ M := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp B.source_open q hB
  exact ⟨r,B.bound,hr,B.bound_nonneg,(fun y hy => mem_iUnion.mpr ⟨B,hball hy⟩),
    fun y hy n => B.bounded y (hball hy) n⟩

theorem exists_locally_uniform_hillHminusZeroSequence_fderiv_bound
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusUniformZeroSequenceDomain) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ ball q r ⊆ hillHminusUniformZeroSequenceDomain ∧
      ∀ y ∈ ball q r, ∀ n : ℕ+, ‖fderiv ℂ (hillHminusCanonicalZeroSequence n) y‖ ≤ C := by
  obtain ⟨R,M,hR,hM,hU,hbound⟩ := exists_locally_uniform_hillHminusZeroSequence_norm_bound q hq
  refine ⟨R/2,4*M/R,half_pos hR,by positivity,(ball_subset_ball (by linarith)).trans hU,?_⟩
  intro y hy n
  have hf : DifferentiableOn ℂ (hillHminusCanonicalZeroSequence n) (ball q R) :=
    ((analyticOnNhd_hillHminusCanonicalZeroSequence n).mono (hU.trans hillHminusUniformZeroSequenceDomain_subset)).differentiableOn
  have hd := norm_fderiv_le_of_ball_bound (hillHminusCanonicalZeroSequence n) q y (R/2) (R/2) M
    (half_pos hR) (by simpa only [add_halves] using hf)
    (by simpa only [add_halves] using fun z hz => hbound z hz n) hy
  apply hd.trans_eq
  field_simp
  ring

end NLS.KdV
