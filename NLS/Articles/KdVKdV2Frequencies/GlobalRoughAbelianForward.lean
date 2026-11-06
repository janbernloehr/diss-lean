import NLS.Articles.KdVKdV2Frequencies.PhysicallyOrientedRoughPackets
import NLS.ComplexAnalysis.AnalyticOpenGluing
import NLS.KdV.HillAbelianSignedPhysicalRecovery

/-! # One actual analytic forward map around the entire real rough space

Canonically oriented packets glue on their ENTIRE complex overlaps.
The resulting ONE signed map retains all original physical coordinates,
and the SAME local actual data at every real rough base.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV NLS.ComplexAnalysis

structure GlobalRoughAbelianForwardData where
  chart : (q0 : PeriodOneRealHminusOne) → PhysicallyOrientedRoughPacketAt q0.val
  positive : PeriodOneHminusOne → Coeff 2
  positive_analytic : AnalyticOnNhd ℂ positive (⋃ q0, ball q0.val (chart q0).data.radius)
  positive_local : ∀ q0, EqOn positive (chart q0).positive (ball q0.val (chart q0).data.radius)

/-- A single native complex analytic forward packet exists on an OPEN
neighborhood of the ENTIRE real HminusOne space, with canonical physical
orientation and all actual local charts retained. No inverse is asserted. -/
theorem nonempty_globalRoughAbelianForwardData : Nonempty GlobalRoughAbelianForwardData := by
  classical
  let D := fun q0 : PeriodOneRealHminusOne =>
    Classical.choice (nonempty_physicallyOrientedRoughPacketAt q0.val q0.property)
  obtain ⟨G,hGa,hG⟩ := exists_analytic_open_gluing
    (fun q0 : PeriodOneRealHminusOne => ball q0.val (D q0).data.radius)
    (fun _ => isOpen_ball) (fun q0 => (D q0).positive)
    (fun q0 => (D q0).positive_analytic)
    (fun q0 q1 => (D q0).positive_overlap (D q1) q0.property q1.property)
  exact ⟨⟨D,G,hGa,hG⟩⟩

namespace GlobalRoughAbelianForwardData

def domain (D : GlobalRoughAbelianForwardData) : Set PeriodOneHminusOne :=
  ⋃ q0, ball q0.val (D.chart q0).data.radius

def signed (D : GlobalRoughAbelianForwardData) :
    PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
  WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) D.positive

theorem domain_open (D : GlobalRoughAbelianForwardData) : IsOpen D.domain :=
  isOpen_iUnion (fun _ => isOpen_ball)

theorem real_mem_domain (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : q ∈ D.domain :=
  mem_iUnion.mpr ⟨⟨q,hr⟩,mem_ball_self (D.chart ⟨q,hr⟩).data.radius_pos⟩

theorem chart_subset_domain (D : GlobalRoughAbelianForwardData) (q0 : PeriodOneRealHminusOne) :
    ball q0.val (D.chart q0).data.radius ⊆ D.domain :=
  fun _ h => mem_iUnion.mpr ⟨q0,h⟩

private theorem conjugation_mem_ball (q0 : PeriodOneRealHminusOne)
    (q : PeriodOneHminusOne) (r : ℝ) (hq : q ∈ ball q0.val r) :
    periodOneHminusConjugation q ∈ ball q0.val r := by
  have hJ := (periodOneHminusConjugation_fixed_iff q0.val).mpr q0.property
  have he : periodOneHminusConjugation q-q0.val = periodOneHminusConjugation (q-q0.val) := by
    rw [periodOneHminusConjugation_sub,hJ]
  rw [mem_ball,dist_eq_norm,he,norm_periodOneHminusConjugation]
  exact mem_ball_iff_norm.mp hq

theorem conjugation_mem_domain (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q ∈ D.domain) : periodOneHminusConjugation q ∈ D.domain := by
  obtain ⟨q0,hq0⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨q0,conjugation_mem_ball q0 q _ hq0⟩

theorem positive_zero (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q ∈ D.domain) (j : ℤ) (hj : j ≤ 0) : D.positive q j = 0 := by
  obtain ⟨q0,hq0⟩ := mem_iUnion.mp hq
  rw [D.positive_local q0 hq0]
  exact (D.chart q0).positive_zero q hq0 j hj

/-- Exact original physical values at EVERY physical source, without
an L2 norm bound, gap condition, or source mean restriction. -/
theorem positive_physical (D : GlobalRoughAbelianForwardData)
    (p : RealPeriodOneHillPotential) (n : ℕ+) :
    D.positive (hillPhysicalHminusEmbedding p).val (n : ℤ) =
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
        (Real.sqrt (1+(n : ℝ)) : ℂ) := by
  let q0 : PeriodOneRealHminusOne := hillPhysicalHminusEmbedding p
  have hp : q0.val ∈ ball q0.val (D.chart q0).data.radius := mem_ball_self (D.chart q0).data.radius_pos
  rw [D.positive_local q0 hp]
  exact (D.chart q0).physical p hp n

theorem signed_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℂ D.signed D.domain := by
  intro q hq
  exact WeightedCoeff.analyticOnNhd_signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2))
    (Weight.sobolev_neg (-1)) D.positive D.domain D.positive_analytic q
      ⟨hq,D.conjugation_mem_domain q hq⟩

/-- The SAME global signed map equals the actual signed packet on each
ENTIRE original complex ball, with its original signs and actual data. -/
theorem signed_local (D : GlobalRoughAbelianForwardData) (q0 : PeriodOneRealHminusOne) :
    EqOn D.signed (D.chart q0).signed (ball q0.val (D.chart q0).data.radius) := by
  intro q hq
  apply Subtype.ext
  funext n
  simp only [signed,PhysicallyOrientedRoughPacketAt.signed,RoughAbelianFourierDataAt.signedPacket,
    WeightedCoeff.signedTargetLift_apply,
    WeightedCoeff.normalizedSignedCompletion_apply _ (Weight.sobolev_neg (-1))]
  have hJq := conjugation_mem_ball q0 q (D.chart q0).data.radius hq
  change (D.positive q n+conj (D.positive (periodOneHminusConjugation q) (-n)))/_ = _
  rw [D.positive_local q0 hq,D.positive_local q0 hJq]
  rfl

theorem signed_zero (D : GlobalRoughAbelianForwardData)
    (q : PeriodOneHminusOne) (hq : q ∈ D.domain) : (D.signed q).val 0 = 0 := by
  obtain ⟨q0,hq0⟩ := mem_iUnion.mp hq
  rw [D.signed_local q0 hq0]
  exact ((D.chart q0).data.signedPacket_analytic_bounded q0.property (D.chart q0).signs).2 q hq0 |>.2

end GlobalRoughAbelianForwardData
end NLS.Articles.KdVKdV2Frequencies
