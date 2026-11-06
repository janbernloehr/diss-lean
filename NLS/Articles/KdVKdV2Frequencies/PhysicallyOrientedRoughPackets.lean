import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseMeanZeroPrincipalEquiv
import NLS.KdV.HillPhysicalAbelianSignCalibration

/-! # Canonically oriented actual packets at every real rough base

One fixed infinite sign selection gives exact ORIGINAL physical recovery
on the entire rough ball, including closed gaps. These oriented packets
agree exactly on their entire complex chart overlaps.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

structure PhysicallyOrientedRoughPacketAt (q0 : PeriodOneHminusOne) where
  data : RoughAbelianFourierDataAt q0
  signs : ℤ → Bool
  physical : ∀ p : RealPeriodOneHillPotential,
    (hillPhysicalHminusEmbedding p).val ∈ ball q0 data.radius → ∀ n : ℕ+,
    data.positivePacket signs (hillPhysicalHminusEmbedding p).val (n : ℤ) =
      hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n n.pos/
        (Real.sqrt (1+(n : ℝ)) : ℂ)

/-- The real rough center may be non-L2. Signs are chosen BEFORE all
physical sources, indices and native orders, on the whole original ball. -/
theorem nonempty_physicallyOrientedRoughPacketAt
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    Nonempty (PhysicallyOrientedRoughPacketAt q0) := by
  obtain ⟨D⟩ := nonempty_roughAbelianFourierDataAt q0 hr0
  obtain ⟨e,_he0,he⟩ := exists_physical_signChange_rough_packet q0 D.radius D.packet
    D.packet_analytic (fun q hq => (D.packet_data q hq).2.2) D.physical_squares
  exact ⟨⟨D,e,he⟩⟩

namespace PhysicallyOrientedRoughPacketAt
variable {q0 q1 : PeriodOneHminusOne}

def positive (D : PhysicallyOrientedRoughPacketAt q0) : PeriodOneHminusOne → Coeff 2 :=
  D.data.positivePacket D.signs

def signed (D : PhysicallyOrientedRoughPacketAt q0) :
    PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
  D.data.signedPacket D.signs

theorem positive_analytic (D : PhysicallyOrientedRoughPacketAt q0) :
    AnalyticOnNhd ℂ D.positive (ball q0 D.data.radius) := fun q hq =>
  ((Coeff.signChange D.signs).analyticAt _).comp (D.data.packet_analytic q hq)

theorem positive_zero (D : PhysicallyOrientedRoughPacketAt q0)
    (q : PeriodOneHminusOne) (hq : q ∈ ball q0 D.data.radius) (j : ℤ) (hj : j ≤ 0) :
    D.positive q j = 0 := by
  change Coeff.signChange D.signs (D.data.packet q) j = 0
  rw [Coeff.signChange_apply,(D.data.packet_data q hq).2.2 j hj]
  simp only [neg_zero,ite_self]

theorem positive_bound (D : PhysicallyOrientedRoughPacketAt q0)
    (q : PeriodOneHminusOne) (hq : q ∈ ball q0 D.data.radius) :
    ‖D.positive q‖ ≤ D.data.packet_bound := by
  simpa only [positive,RoughAbelianFourierDataAt.positivePacket,Coeff.norm_signChange] using
    (D.data.packet_data q hq).2.1

/-- Exact equality, with canonical physical orientation, at EVERY complex
point of the full overlap. No new signs or smaller radii are chosen. -/
theorem positive_overlap
    (D : PhysicallyOrientedRoughPacketAt q0) (E : PhysicallyOrientedRoughPacketAt q1)
    (hr0 : IsRealPeriodOneHminusOne q0) (hr1 : IsRealPeriodOneHminusOne q1) :
    EqOn D.positive E.positive (ball q0 D.data.radius ∩ ball q1 E.data.radius) := by
  apply eqOn_rough_real_centered_ball_inter_of_physical_eq q0 q1 hr0 hr1
    D.data.radius E.data.radius D.positive E.positive D.positive_analytic E.positive_analytic
  intro p hp
  ext j
  by_cases hj : 0 < j
  · let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n : ℤ) = j := by change (j.toNat : ℤ) = j; omega
    rw [←hn]
    exact (D.physical p hp.1 n).trans (E.physical p hp.2 n).symm
  · rw [D.positive_zero _ hp.1 j (by omega),E.positive_zero _ hp.2 j (by omega)]

end PhysicallyOrientedRoughPacketAt
end NLS.Articles.KdVKdV2Frequencies
