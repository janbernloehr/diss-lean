import NLS.Articles.KdVKdV2Frequencies.ArbitraryBasePacketCompatibility
import NLS.SequenceSpaces.SobolevSignedRealCompactGermAt

/-! # Full signed native Fourier germs at every real rough base

One actual packet and constant signs precede all Sobolev orders. Every
native complex germ includes EXACTLY to its same weak signed completion,
with the full positive and reflected Fourier principal plus compact.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
variable {q0 : PeriodOneHminusOne}

def packetPositiveFourierPrincipalAt (D : RoughAbelianFourierDataAt q0) (e : ℤ → Bool)
    (t : ℝ) (ht : 0 ≤ t) (p : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] Coeff 2 :=
  (Coeff.signChange e).comp (D.chart.nativeAbelianFourierPrincipal D.symbol t ht p)

def packetSignedFourierPrincipalAt (D : RoughAbelianFourierDataAt q0) (e : ℤ → Bool)
    (t : ℝ) (ht : 0 ≤ t) (p : WeightedCoeff (Weight.sobolev (t-1)) 2) :
    WeightedCoeff (Weight.sobolev (t-1)) 2 →L[ℂ] WeightedCoeff (Weight.sobolev (t-1/2)) 2 :=
  WeightedCoeff.nativeSignedPrincipal (Weight.sobolev (t-1)) (Weight.sobolev (t-1/2))
    (Weight.sobolev_neg (t-1)) (packetPositiveFourierPrincipalAt D e t ht p)
    (packetPositiveFourierPrincipalAt D e t ht
      (WeightedCoeff.conjugateReflection (Weight.sobolev (t-1)) (Weight.sobolev_neg (t-1)) p))

namespace RoughAbelianFourierDataAt

def positivePacket (D : RoughAbelianFourierDataAt q0) (e : ℤ → Bool)
    (q : PeriodOneHminusOne) : Coeff 2 := Coeff.signChange e (D.packet q)

def signedPacket (D : RoughAbelianFourierDataAt q0) (e : ℤ → Bool) :
    PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2 :=
  WeightedCoeff.signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2)) (D.positivePacket e)

private theorem conjugation_mem_ball (hr0 : IsRealPeriodOneHminusOne q0)
    (q : PeriodOneHminusOne) (r : ℝ) (hq : q ∈ ball q0 r) :
    periodOneHminusConjugation q ∈ ball q0 r := by
  have hJ := (periodOneHminusConjugation_fixed_iff q0).mpr hr0
  have he : periodOneHminusConjugation q-q0 = periodOneHminusConjugation (q-q0) := by
    rw [periodOneHminusConjugation_sub,hJ]
  rw [mem_ball,dist_eq_norm,he,norm_periodOneHminusConjugation]
  exact mem_ball_iff_norm.mp hq

theorem signedPacket_analytic_bounded (D : RoughAbelianFourierDataAt q0)
    (hr0 : IsRealPeriodOneHminusOne q0) (e : ℤ → Bool) :
    AnalyticOnNhd ℂ (D.signedPacket e) (ball q0 D.radius) ∧
      ∀ q ∈ ball q0 D.radius, ‖D.signedPacket e q‖ ≤ 2*D.packet_bound ∧
        (D.signedPacket e q).val 0 = 0 := by
  have hYa : AnalyticOnNhd ℂ (D.positivePacket e) (ball q0 D.radius) := fun q hq =>
    ((Coeff.signChange e).analyticAt _).comp (D.packet_analytic q hq)
  have hYbound (q : PeriodOneHminusOne) (hq : q ∈ ball q0 D.radius) :
      ‖D.positivePacket e q‖ ≤ D.packet_bound := by
    simpa only [positivePacket,Coeff.norm_signChange] using (D.packet_data q hq).2.1
  have hYzero (q : PeriodOneHminusOne) (hq : q ∈ ball q0 D.radius) : D.positivePacket e q 0 = 0 := by
    simp only [positivePacket,Coeff.signChange_apply,(D.packet_data q hq).2.2 0 le_rfl,
      neg_zero,ite_self]
  refine ⟨?_,?_⟩
  · intro q hq
    exact WeightedCoeff.analyticOnNhd_signedTargetLift (Weight.sobolev (-1)) (Weight.sobolev (-1/2))
      (Weight.sobolev_neg (-1)) (D.positivePacket e) (ball q0 D.radius) hYa q
      ⟨hq,conjugation_mem_ball hr0 q D.radius hq⟩
  · intro q hq
    have hJq := conjugation_mem_ball hr0 q D.radius hq
    constructor
    · rw [signedPacket,WeightedCoeff.norm_signedTargetLift]
      exact WeightedCoeff.norm_normalizedSignedCompletion_le (Weight.sobolev (-1))
        (Weight.sobolev_neg (-1)) (D.positivePacket e) q D.packet_bound
        (hYbound q hq) (hYbound _ hJq)
    · rw [signedPacket,WeightedCoeff.signedTargetLift_apply,
        WeightedCoeff.normalizedSignedCompletion_apply _ (Weight.sobolev_neg (-1)),hYzero q hq]
      have hYJ : D.positivePacket e
          (WeightedCoeff.conjugateReflection (Weight.sobolev (-1))
            (Weight.sobolev_neg (-1)) q) 0 = 0 := hYzero _ hJq
      simp only [neg_zero,hYJ,map_zero,add_zero,zero_div]

theorem exists_native_signed_packet_fourier_germ
    (D : RoughAbelianFourierDataAt q0) (hr0 : IsRealPeriodOneHminusOne q0) (e : ℤ → Bool)
    (t : ℝ) (ht : 0 ≤ t) (q : WeightedCoeff (Weight.sobolev (t-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q))
    (hq : periodOneSobolevImageInclusion t ht q ∈ ball q0 D.radius) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q ∈ V ∧
      (∀ p ∈ V, WeightedCoeff.conjugateReflection (Weight.sobolev (t-1))
        (Weight.sobolev_neg (t-1)) p ∈ V) ∧
      ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
        0 ≤ C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p ∈ V,
          periodOneSobolevImageInclusion t ht p ∈ ball q0 D.radius ∧ ‖g p‖ ≤ C ∧
          WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ) ≤ t-1/2) (g p) =
            D.signedPacket e (periodOneSobolevImageInclusion t ht p) ∧ (g p).val 0 = 0 ∧
          (IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p) →
            IsCompactOperator (fderiv ℂ g p-packetSignedFourierPrincipalAt D e t ht p)) := by
  obtain ⟨U,hU,hqU,M,F,hM,hFa,hdata⟩ := D.exists_native_packet_fourier_germ t ht q hqr hq
  let H := fun p => Coeff.signChange e (F p)
  have hHa : AnalyticOnNhd ℂ H U := fun p hp => ((Coeff.signChange e).analyticAt _).comp (hFa p hp)
  have hHd : ∀ p ∈ U, periodOneSobolevImageInclusion t ht p ∈ ball q0 D.radius ∧
      ‖H p‖ ≤ M ∧ ∀ n : ℤ, H p n =
        (Weight.sobolev t n : ℂ)*D.positivePacket e (periodOneSobolevImageInclusion t ht p) n := by
    intro p hp
    refine ⟨(hdata p hp).1,?_,?_⟩
    · simpa only [H,Coeff.norm_signChange] using (hdata p hp).2.1
    · intro n
      exact Coeff.signChange_weighted_packet e F
        (fun p => D.packet (periodOneSobolevImageInclusion t ht p))
        (fun n => (Weight.sobolev t n : ℂ)) p (hdata p hp).2.2.1 n
  have hc : ∀ p ∈ U, IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht p) →
      IsCompactOperator (fderiv ℂ H p-packetPositiveFourierPrincipalAt D e t ht p) := by
    intro p hp hpr
    exact Coeff.isCompactOperator_fderiv_signChange_sub e F p (hFa p hp).differentiableAt _
      ((hdata p hp).2.2.2 hpr)
  obtain ⟨V,hV,hqV,_hVU,hJ,C,g,hC,hga,hd⟩ :=
    exists_sobolev_signedTargetLift_real_compact_germ_at t ht (D.positivePacket e) q0 D.radius q hqr
      U hU hqU M hM H hHa hHd (packetPositiveFourierPrincipalAt D e t ht) hc
  refine ⟨V,hV,hqV,hJ,C,g,hC,hga,?_⟩
  intro p hp
  have hzero := congrArg (fun z : WeightedCoeff (Weight.sobolev (-1/2)) 2 => z.val 0) (hd p hp).2.2.1
  rw [WeightedCoeff.sobolevInclusion_apply] at hzero
  exact ⟨(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.1,
    hzero.trans ((D.signedPacket_analytic_bounded hr0 e).2 _ (hd p hp).1).2,(hd p hp).2.2.2⟩

end RoughAbelianFourierDataAt
end NLS.Articles.KdVKdV2Frequencies
