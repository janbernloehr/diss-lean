import NLS.Articles.KdVKdV2Frequencies.NativeRoughAllSobolevForwardInverse
import NLS.Articles.KdVKdV2Frequencies.ActualSobolevInverseGerms

/-! # All native analytic inverse germs of the SAME actual rough inverse

Every existing exact inverse, real Sobolev membership, physical L2,
global-coordinate and mass identity is retained for the SAME Z,R.
The inverse now has native complex H^s-valued germs at zero for ALL
s>=-1, on order-dependent open h^(s+1/2) target neighborhoods.
Arbitrary-base and global strong analyticity remain separate obligations.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The SAME actual family retains all earlier exact endpoint and physical
identities and ALL native complex analytic inverse germs at zero. -/
theorem exists_hillHminus_native_all_sobolev_analytic_inverse :
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
      (∀ b∈W, deletedL2Conjugation b=b →
        (Memℓp (R b).val 2 ↔ Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2) ∧
        (Memℓp (fun j => (Weight.sobolev (1/2) j : ℂ)*
          (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val j) 2 →
          ∃ p : hillRealMeanZeroSourceSubmodule, hillOriginalHminusSource p.val.val=R b ∧
            (∀ n : ℕ+, hillOriginalBirkhoffAbelianCoordinate p n=
              (WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val (n : ℤ)) ∧
            ‖p‖^2=∑' k : ℕ, (4*Real.pi*(k+1 : ℕ))*
              ‖(WeightedCoeff.meanZeroWeightedLiftCLM (Weight.sobolev (-1/2)) b).val ((k+1 : ℕ) : ℤ)‖^2)) ∧
      HasAllSobolevInverseGerms Z W R := by
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hphys,hW,h0W,hRa,hR0,hRdata,hreal,hSob,hforward,hendpoint⟩ :=
    exists_hillHminus_native_all_sobolev_forward_inverse
  have hgerm : HasAllSobolevInverseGerms Z W R :=
    exists_actual_rough_inverse_all_sobolev_germs η hη Z hZa hZ0 hphys W hW h0W R
      hRa.continuousOn hR0 (fun b hb => ⟨(hRdata b hb).1,(hRdata b hb).2.2⟩)
  exact ⟨η,Z,W,R,hη,hZa,hZ0,hphys,hW,h0W,hRa,hR0,hRdata,hreal,hSob,hforward,hendpoint,hgerm⟩

end NLS.Articles.KdVKdV2Frequencies
