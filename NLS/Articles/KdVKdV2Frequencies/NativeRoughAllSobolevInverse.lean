import NLS.Articles.KdVKdV2Frequencies.NativeRoughEndpointInverse
import NLS.Articles.KdVKdV2Frequencies.RoughAbelianSobolevCriterion

/-! # The SAME actual rough inverse has every exact Sobolev endpoint

A single open real-preserving target neighborhood works before ALL real
orders s>=-1 and EVERY real target of arbitrary support. The actual rough
inverse belongs to H^s exactly when its literal signed target belongs to
h^(s+1/2). The original exact L2 endpoint and physical Birkhoff/mass
identification are retained. Analyticity here has H-minus-one values;
stronger Sobolev-topology analyticity remains a separate assertion.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- ONE actual analytic rough inverse has ALL native Sobolev endpoints
for EVERY real target in its open neighborhood, including infinite support.
The chart and target neighborhood are chosen before ALL orders and targets. -/
theorem exists_hillHminus_native_real_target_all_sobolev_inverse :
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
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hZp,hW,h0W,hRa,hR0,hRdata,hRreal,hendpoint⟩ :=
    exists_hillHminus_native_real_target_L2_endpoint_inverse
  obtain ⟨ρ,hρ,hρη,hcrit⟩ := exists_hillHminus_actual_abelian_sobolev_criterion η hη Z hZa hZp
  let W' : Set (DeletedCoeff 2 0) := W ∩ R ⁻¹' ball (0 : PeriodOneHminusOne) ρ
  have hW' : IsOpen W' := hRa.continuousOn.isOpen_inter_preimage hW isOpen_ball
  have h0W' : (0 : DeletedCoeff 2 0)∈W' := by
    refine ⟨h0W,?_⟩
    change R 0∈ball (0 : PeriodOneHminusOne) ρ
    rw [hR0]
    exact mem_ball_self hρ
  have hsub : W'⊆W := inter_subset_left
  have hsource : ball (0 : PeriodOneHminusOne) ρ⊆ball (0 : PeriodOneHminusOne) η :=
    ball_subset_ball hρη
  have hdata (b : DeletedCoeff 2 0) (hb : b∈W') :
      (R b).val 0=0 ∧ R b∈ball (0 : PeriodOneHminusOne) ρ ∧
        Z (R b)=WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b :=
    ⟨(hRdata b (hsub hb)).1,hb.2,(hRdata b (hsub hb)).2.2⟩
  refine ⟨ρ,Z,W',R,hρ,hZa.mono hsource,hZ0,(fun p hp => hZp p (hsource hp)),
    hW',h0W',hRa.mono hsub,hR0,hdata,(fun b hb => hRreal b (hsub hb)),?_,?_⟩
  · intro b hb hbr s hs
    have hreal := hRreal b (hsub hb) hbr
    have hlift := meanZeroWeightedLift_real (Weight.sobolev (-1/2)) (Weight.sobolev_neg (-1/2)) b hbr
    have hnorm (j : ℤ) : ‖(Z (R b)).val (-j)‖=‖(Z (R b)).val j‖ := by
      rw [(hdata b hb).2.2,hlift.2 j,norm_conj]
    have H := hcrit (R b) hb.2 hreal (hdata b hb).1 hnorm s hs
    rwa [(hdata b hb).2.2] at H
  · intro b hb hbr
    exact hendpoint b (hsub hb) hbr

end NLS.Articles.KdVKdV2Frequencies
