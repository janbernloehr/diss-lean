import NLS.SequenceSpaces.SobolevConvolutionBounds
import NLS.KdV.HillHminusRetainedMiuraEtaChart
import NLS.ComplexAnalysis.BoundedAnalyticGerm

/-! The nonlinear correction of the SAME retained Miura lift is analytic
and bounded in native H1 on one ORIGINAL complex L2 neighborhood. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_native_l2_miura_nonlinear (P : HillHminusPsiChart)
    (hstrong : HasAllNativeMiuraGerms P)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈P.miura.domain) :
    ∃ W : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen W ∧ q∈W ∧
      ∃ C : ℝ,∃ T : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
        0≤C ∧ AnalyticOnNhd ℂ T W ∧ ∀ p∈W,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈P.miura.domain ∧ ‖T p‖≤C ∧
          ∀ n : ℤ,(T p).val n=(2*(Real.pi:ℂ)*I)*P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) p) n-
            ∑' j : ℤ,P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) p) (n-j)*
              P.miura.lift (periodOneSobolevImageInclusion 1 (by norm_num) p) j := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,g,hga,hg⟩ := hstrong 1 (by norm_num) q hq
  let T := fun p => (2*(Real.pi:ℂ)*I) • g p-
    WeightedCoeff.sobolevConvolutionCLM (by norm_num : (2:ℝ≥0∞)≠⊤) (g p) (g p)
  have hTa : AnalyticOnNhd ℂ T V := (hga.const_smul (c := 2*(Real.pi:ℂ)*I)).sub
    (fun p hp => ((WeightedCoeff.sobolevConvolutionCLM (by norm_num : (2:ℝ≥0∞)≠⊤)).analyticAt_bilinear _).comp₂
      (hga p hp) (hga p hp))
  obtain ⟨W,hW,hqW,hWV,C,hC,hTWa,hTb⟩ := NLS.ComplexAnalysis.exists_bounded_analytic_germ V hV q hqV T hTa
  refine ⟨W,hW,hqW,C,T,hC,hTWa,?_⟩
  intro p hp
  have hgc (n : ℤ) : (g p).val n=P.miura.lift (L p) n := by
    simpa only [WeightedCoeff.sobolevToL2_apply,L] using congrArg (fun z : Coeff 2 => z n) (hg p (hWV hp)).2
  refine ⟨(hg p (hWV hp)).1,hTb p hp,?_⟩
  intro n
  simp only [T,WeightedCoeff.sub_val,WeightedCoeff.smul_val,
    WeightedCoeff.sobolevConvolutionCLM_apply,sobolevConvolution_apply]
  simp_rw [hgc]
  rfl

end NLS.KdV.HillHminusPsiChart
