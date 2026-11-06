import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianFourierGerms
import NLS.KdV.HillArbitraryRoughAbelianSigns
import NLS.SequenceSpaces.ConstantSignPacketTransport

/-! # Exact constant-sign compatibility on actual complex chart overlaps

Any two actual rough packets at real centers agree up to ONE fixed
infinite coordinate sign selection on their ENTIRE complex overlap.
The signs precede source points and all stronger Sobolev topologies.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

theorem exists_arbitrary_base_packet_overlap_signs
    (q0 q1 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0)
    (hr1 : IsRealPeriodOneHminusOne q1)
    (D : RoughAbelianFourierDataAt q0) (E : RoughAbelianFourierDataAt q1) :
    ∃ e : ℤ → Bool, ∀ q ∈ ball q0 D.radius ∩ ball q1 E.radius,
      E.packet q = Coeff.signChange e (D.packet q) := by
  let U := ball q0 D.radius ∩ ball q1 E.radius
  by_cases hne : U.Nonempty
  · obtain ⟨q,hq,hqr⟩ := real_point_of_inter_real_centered_rough_balls q0 q1 hr0 hr1 D.radius E.radius hne
    apply Coeff.exists_constant_signChange_of_eqOn_or_neg U E.packet D.packet
    intro j
    by_cases hj : 0 < j
    · let n := Coeff.positivePoleIndex j hj
      have hn : (n : ℤ) = j := by exact_mod_cast Coeff.positivePoleIndex_real j hj
      have hf : AnalyticOnNhd ℂ (fun p => E.packet p (n : ℤ)) U := fun p hp =>
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (E.packet_analytic p hp.2)
      have hg : AnalyticOnNhd ℂ (fun p => D.packet p (n : ℤ)) U := fun p hp =>
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (n : ℤ)).analyticAt _).comp (D.packet_analytic p hp.1)
      have H := eqOn_or_neg_rough_domain_of_physical_abelian_sq U (isOpen_ball.inter isOpen_ball)
        ((convex_ball q0 D.radius).inter (convex_ball q1 E.radius)).isPreconnected q hq hqr n
        (fun p => E.packet p (n : ℤ)) (fun p => D.packet p (n : ℤ)) hf hg (by
          intro p hp hw
          exact (E.physical_squares p hp.2 n hw).trans (D.physical_squares p hp.1 n hw).symm)
      simpa only [EqOn,hn] using H
    · exact Or.inl (fun q hq => by
        rw [(E.packet_data q hq.2).2.2 j (by omega),(D.packet_data q hq.1).2.2 j (by omega)])
  · exact ⟨fun _ => false,fun q hq => (hne ⟨q,hq⟩).elim⟩

end NLS.Articles.KdVKdV2Frequencies
