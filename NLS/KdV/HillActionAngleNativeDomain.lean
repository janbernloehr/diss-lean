import NLS.KdV.HillActionAngleNativeRealization
import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! Actual minus-half weighted Cartesian sequences on ONE open connected
native complex neighborhood of the ENTIRE real H-minus-one form.
Local realizations prove membership, exact coefficients and norm bounds. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusActionAngleXSequence (q : PeriodOneHminusOne) : WeightedCoeff (Weight.positiveSobolev (-1/2)) 2 :=
  WeightedCoeff.ofFunctionOrZero (Weight.positiveSobolev (-1/2)) 2
    (positiveScalarExtension (fun n => hillHminusActionAngleX n q))

def hillHminusActionAngleYSequence (q : PeriodOneHminusOne) : WeightedCoeff (Weight.positiveSobolev (-1/2)) 2 :=
  WeightedCoeff.ofFunctionOrZero (Weight.positiveSobolev (-1/2)) 2
    (positiveScalarExtension (fun n => hillHminusActionAngleY n q))

structure HillActionAngleNativeBall where
  center : PeriodOneHminusOne
  center_real : IsRealPeriodOneHminusOne center
  radius : ℝ
  radius_pos : 0 < radius
  subset : ball center radius ⊆ hillHminusActionAngleEnergyDomain
  bound : ℝ
  bound_pos : 0 < bound
  coordinates : ∀ q ∈ ball center radius, ∀ k,
    (hillHminusActionAngleXSequence q).val k = positiveScalarExtension (fun n => hillHminusActionAngleX n q) k ∧
    (hillHminusActionAngleYSequence q).val k = positiveScalarExtension (fun n => hillHminusActionAngleY n q) k
  norm_bound : ∀ q ∈ ball center radius,
    ‖hillHminusActionAngleXSequence q‖ ≤ bound ∧ ‖hillHminusActionAngleYSequence q‖ ≤ bound

namespace HillActionAngleNativeBall

def source (B : HillActionAngleNativeBall) : Set PeriodOneHminusOne := ball B.center B.radius

theorem source_open (B : HillActionAngleNativeBall) : IsOpen B.source := isOpen_ball

end HillActionAngleNativeBall

theorem exists_hillActionAngleNativeBall (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) :
    ∃ B : HillActionAngleNativeBall, q ∈ B.source := by
  obtain ⟨U,hU,hqU,hUD,M,hM,hreal⟩ := exists_local_uniform_actionAngle_native_realizations q hr
  obtain ⟨r,hrpos,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hqU)
  have hdata (a : PeriodOneHminusOne) (ha : a ∈ ball q r) :
      (∀ k, (hillHminusActionAngleXSequence a).val k = positiveScalarExtension (fun n => hillHminusActionAngleX n a) k ∧
        (hillHminusActionAngleYSequence a).val k = positiveScalarExtension (fun n => hillHminusActionAngleY n a) k) ∧
      (‖hillHminusActionAngleXSequence a‖ ≤ M ∧ ‖hillHminusActionAngleYSequence a‖ ≤ M) := by
    obtain ⟨⟨x,hx,hnx⟩,⟨y,hy,hny⟩⟩ := hreal a (hball ha)
    have heX : hillHminusActionAngleXSequence a = x := WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ x hx
    have heY : hillHminusActionAngleYSequence a = y := WeightedCoeff.ofFunctionOrZero_eq_of_coordinates _ _ y hy
    rw [heX,heY]
    exact ⟨fun k => ⟨hx k,hy k⟩,hnx,hny⟩
  exact ⟨⟨q,hr,r,hrpos,(fun a ha => hUD (hball ha)),M,hM,
    (fun a ha => (hdata a ha).1),(fun a ha => (hdata a ha).2)⟩,mem_ball_self hrpos⟩

def hillHminusActionAngleNativeDomain : Set PeriodOneHminusOne :=
  ⋃ B : HillActionAngleNativeBall, B.source

theorem isOpen_hillHminusActionAngleNativeDomain : IsOpen hillHminusActionAngleNativeDomain :=
  isOpen_iUnion (fun B => B.source_open)

theorem real_mem_hillHminusActionAngleNativeDomain (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) : q ∈ hillHminusActionAngleNativeDomain := by
  obtain ⟨B,hB⟩ := exists_hillActionAngleNativeBall q hr
  exact mem_iUnion.mpr ⟨B,hB⟩

theorem hillHminusActionAngleNativeDomain_subset :
    hillHminusActionAngleNativeDomain ⊆ hillHminusActionAngleEnergyDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.subset hB

theorem hillHminusActionAngle_sequences_coordinates (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (k : ℤ) :
    (hillHminusActionAngleXSequence q).val k = positiveScalarExtension (fun n => hillHminusActionAngleX n q) k ∧
    (hillHminusActionAngleYSequence q).val k = positiveScalarExtension (fun n => hillHminusActionAngleY n q) k := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact B.coordinates q hB k

theorem hillHminusActionAngle_sequences_positive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (n : ℕ+) :
    (hillHminusActionAngleXSequence q).val ((n:ℕ):ℤ) = hillHminusActionAngleX n q ∧
    (hillHminusActionAngleYSequence q).val ((n:ℕ):ℤ) = hillHminusActionAngleY n q := by
  simpa only [positiveScalarExtension_apply] using hillHminusActionAngle_sequences_coordinates q hq ((n:ℕ):ℤ)

theorem hillHminusActionAngle_sequences_nonpositive (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAngleNativeDomain) (k : ℤ) (hk : k ≤ 0) :
    (hillHminusActionAngleXSequence q).val k = 0 ∧ (hillHminusActionAngleYSequence q).val k = 0 := by
  have hn : k ∉ range positiveEmbedding := by
    rintro ⟨n,hn⟩
    have hp : (0:ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
    change ((n:ℕ):ℤ) = k at hn
    omega
  simpa only [positiveScalarExtension_zero_of_not_mem_range _ k hn] using
    hillHminusActionAngle_sequences_coordinates q hq k

theorem exists_locally_uniform_actionAngle_native_norm_bound :
    ∀ q ∈ hillHminusActionAngleNativeDomain, ∃ U : Set PeriodOneHminusOne,
      IsOpen U ∧ q ∈ U ∧ U ⊆ hillHminusActionAngleNativeDomain ∧
      ∃ M : ℝ, 0 < M ∧ ∀ a ∈ U,
        ‖hillHminusActionAngleXSequence a‖ ≤ M ∧ ‖hillHminusActionAngleYSequence a‖ ≤ M := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact ⟨B.source,B.source_open,hB,(fun _ h => mem_iUnion.mpr ⟨B,h⟩),B.bound,B.bound_pos,B.norm_bound⟩

theorem isConnected_hillHminusActionAngleNativeDomain : IsConnected hillHminusActionAngleNativeDomain := by
  let S : Set PeriodOneHminusOne := {q | IsRealPeriodOneHminusOne q}
  have hS : IsPreconnected S := isPreconnected_real_periodOneHminus
  have hzero : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have hpre (B : HillActionAngleNativeBall) : IsPreconnected (S ∪ B.source) :=
    hS.union B.center B.center_real (mem_ball_self B.radius_pos) (convex_ball _ _).isPreconnected
  have hcommon : (⋂ B : HillActionAngleNativeBall, S ∪ B.source).Nonempty :=
    ⟨0,mem_iInter.mpr (fun _ => Or.inl hzero)⟩
  have he : (⋃ B : HillActionAngleNativeBall, S ∪ B.source) = hillHminusActionAngleNativeDomain := by
    ext q
    constructor
    · intro hq
      obtain ⟨B,hqS | hqB⟩ := mem_iUnion.mp hq
      · exact real_mem_hillHminusActionAngleNativeDomain q hqS
      · exact mem_iUnion.mpr ⟨B,hqB⟩
    · intro hq
      obtain ⟨B,hqB⟩ := mem_iUnion.mp hq
      exact mem_iUnion.mpr ⟨B,Or.inr hqB⟩
  refine ⟨⟨0,real_mem_hillHminusActionAngleNativeDomain 0 hzero⟩,?_⟩
  rw [← he]
  exact isPreconnected_iUnion hcommon hpre

end NLS.KdV
