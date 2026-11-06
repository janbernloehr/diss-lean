import NLS.Articles.KdVKdV2Frequencies.NativeRoughAllSobolevInverse
import NLS.Articles.KdVKdV2Frequencies.ActualSignedSobolevRestriction

/-! # All stronger forward charts attached to the SAME actual rough inverse

One actual signed Z and inverse R retain exact complex right-inverse
identities, all real Sobolev membership endpoints, original physical L2
representatives, GLOBAL physical coordinates and exact mass. The SAME Z
now has genuine complex H^s-to-h^(s+1/2) analytic germs for ALL s>=-1
at every eligible real source in one common rough ball. Stronger inverse
analyticity and arbitrary-base/global rough inversion remain separate.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The SAME actual full signed forward/inverse family retains its exact
inverse and physical identities, and ALL stronger complex analytic forward
Sobolev germs, before every order and real source/target of arbitrary support. -/
theorem exists_hillHminus_native_all_sobolev_forward_inverse :
    ∃ η : ℝ, ∃ Z : PeriodOneHminusOne → WeightedCoeff (Weight.sobolev (-1/2)) 2,
      ∃ W : Set (DeletedCoeff 2 0), ∃ R : DeletedCoeff 2 0 → PeriodOneHminusOne,
      0<η ∧ AnalyticOnNhd ℂ Z (ball (0 : PeriodOneHminusOne) η) ∧ Z 0=0 ∧
      (∀ p : RealPeriodOneHillPotential,
        (hillPhysicalHminusEmbedding p).val∈ball (0 : PeriodOneHminusOne) η → ∀ j : ℤ,
        (Z (hillPhysicalHminusEmbedding p).val).val j=
          hillAbelianRawCoordinateSequence SpectralWeight.one (hillUnitRealSourceUnembed p) j) ∧
      IsOpen W ∧ 0∈W ∧ AnalyticOnNhd ℂ R W ∧ R 0=0 ∧
      (∀ b∈W, (R b).val 0=0 ∧ R b∈ball (0 : PeriodOneHminusOne) η ∧
        Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b) ∧
      (∀ b∈W, deletedL2Conjugation b=b → IsRealPeriodOneHminusOne (R b)) ∧
      (∀ b∈W, deletedL2Conjugation b=b → ∀ s : ℝ, -1≤s →
        (Memℓp (fun j => (Weight.sobolev s j : ℂ)*(R b).val j) 2 ↔
          Memℓp (fun j => (Weight.sobolev (s+1/2) j : ℂ)*
            (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2)) ∧
      (∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
        IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion t ht q) →
        periodOneSobolevImageInclusion t ht q∈ball (0 : PeriodOneHminusOne) η →
        ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
          ∃ C : ℝ, ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev (t-1/2)) 2,
            0≤C ∧ AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
              periodOneSobolevImageInclusion t ht p∈ball (0 : PeriodOneHminusOne) η ∧ ‖g p‖≤C ∧
              WeightedCoeff.sobolevInclusion (by linarith : (-1/2 : ℝ)≤t-1/2) (g p)=
                Z (periodOneSobolevImageInclusion t ht p)) ∧
      ∀ b∈W, deletedL2Conjugation b=b →
        (Memℓp (R b).val 2 ↔ Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2) ∧
        (Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2 →
          ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val=R b ∧
            (∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val (n : ℤ)) ∧
            ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
              ‖(WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val ((k+1 : ℕ) : ℤ)‖^2) := by
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hZphys,hW,h0W,hRa,hR0,hRdata,hRreal,hSob,hendpoint⟩ :=
    exists_hillHminus_native_real_target_all_sobolev_inverse
  obtain ⟨ρ,hρ,hρη,hforward⟩ := exists_hillHminus_actual_signed_sobolev_restrictions η hη Z hZa hZphys
  let W' : Set (DeletedCoeff 2 0) := W∩R ⁻¹' ball (0 : PeriodOneHminusOne) ρ
  have hW' : IsOpen W' := hRa.continuousOn.isOpen_inter_preimage hW isOpen_ball
  have h0W' : (0 : DeletedCoeff 2 0)∈W' := by
    refine ⟨h0W,?_⟩
    change R 0∈ball (0 : PeriodOneHminusOne) ρ
    rw [hR0]
    exact mem_ball_self hρ
  have hsub : W'⊆W := inter_subset_left
  have hsource : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η := ball_subset_ball hρη
  have hdata (b : DeletedCoeff 2 0) (hb : b∈W') :
      (R b).val 0=0 ∧ R b∈ball (0 : PeriodOneHminusOne) ρ ∧
        Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b :=
    ⟨(hRdata b (hsub hb)).1,hb.2,(hRdata b (hsub hb)).2.2⟩
  exact ⟨ρ,Z,W',R,hρ,hZa.mono hsource,hZ0,(fun p hp => hZphys p (hsource hp)),
    hW',h0W',hRa.mono hsub,hR0,hdata,(fun b hb => hRreal b (hsub hb)),
    (fun b hb => hSob b (hsub hb)),hforward,(fun b hb => hendpoint b (hsub hb))⟩

end NLS.Articles.KdVKdV2Frequencies
