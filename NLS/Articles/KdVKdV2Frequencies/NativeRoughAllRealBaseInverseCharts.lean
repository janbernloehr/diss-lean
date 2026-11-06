import NLS.Articles.KdVKdV2Frequencies.NativeRoughSignedFourierForwardInverse
import NLS.Articles.KdVKdV2Frequencies.ActualNativeAnalyticInverseCharts

/-! # All actual native Jacobian units and real-base inverse charts for SAME Z,R

The original weak inverse and every earlier physical identity are retained.
The SAME signed coordinate map now has invertible native mean-zero
Jacobians and genuine complex analytic inverse charts at all eligible
real native bases in one common rough ball, before every Sobolev order.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV

/-- The SAME actual signed Z,R retain EVERY earlier inverse and physical
identity, now with ALL native Jacobian units and all eligible real-base
complex analytic inverse charts in ONE common rough ball. -/
theorem exists_hillHminus_native_all_real_base_inverse_charts :
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
      HasAllSobolevInverseGerms Z W R ∧
      HasSignedAbelianCompactGerms η Z ∧ HasSignedAbelianFourierGerms η Z ∧
      HasAllNativeJacobianUnits η Z ∧ HasAllNativeAnalyticInverseCharts η Z := by
  obtain ⟨η,Z,W,R,hη,hZa,hZ0,hphys,hW,h0W,hRa,hR0,hRdata,hreal,hSob,hforward,hendpoint,hAll,hCompact,hFourier⟩ :=
    exists_hillHminus_native_signed_fourier_forward_inverse
  have hUnits := exists_actual_all_native_jacobian_units η hη Z hZa hphys
  exact ⟨η,Z,W,R,hη,hZa,hZ0,hphys,hW,h0W,hRa,hR0,hRdata,hreal,hSob,hforward,hendpoint,hAll,hCompact,hFourier,
    hUnits,hUnits.analytic_inverse_charts⟩

end NLS.Articles.KdVKdV2Frequencies
