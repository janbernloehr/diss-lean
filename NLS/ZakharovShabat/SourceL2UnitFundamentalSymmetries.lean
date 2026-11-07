import NLS.ZakharovShabat.SourceL2MonodromySymmetries
import NLS.ZakharovShabat.ClassicalFundamentalMatrixSymmetries
import NLS.ZakharovShabat.DiscriminantMatrixSymmetries

/-! # Full unit-interval matrix symmetries at original complex Hilbert sources -/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

private theorem continuous_source_unit_matrix (z : ℂ) (t : Icc (0:ℝ) 1) :
    Continuous (fun φ : CoeffPair 2 => l2FundamentalMatrix (sourcePhysicalL2 φ) z t) := by
  have hm : Continuous (fun φ : CoeffPair 2 => ((z,sourcePhysicalL2 φ),t)) :=
    (continuous_const.prodMk sourcePhysicalL2.continuous).prodMk continuous_const
  have h := continuous_l2FundamentalMatrix_time_joint.comp hm
  exact h

private theorem continuous_source_monodromy (z : ℂ) :
    Continuous (fun φ : CoeffPair 2 => l2Monodromy (sourcePhysicalL2 φ) z) := by
  have hm : Continuous (fun φ : CoeffPair 2 => (z,sourcePhysicalL2 φ)) :=
    continuous_const.prodMk sourcePhysicalL2.continuous
  have h := continuous_l2Monodromy_joint.comp hm
  exact h

theorem l2FundamentalMatrix_sourceComponentSwap (φ : CoeffPair 2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2FundamentalMatrix (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) t =
      componentSwapMatrix (l2FundamentalMatrix (sourcePhysicalL2 φ) z t) := by
  have hf := (continuous_source_unit_matrix (-z) t).comp sourceComponentSwap.continuous
  have h0 := continuous_source_unit_matrix z t
  have hg : Continuous (fun ψ : CoeffPair 2 => componentSwapMatrix (l2FundamentalMatrix (sourcePhysicalL2 ψ) z t)) := by
    unfold componentSwapMatrix
    fun_prop
  apply congrFun (CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _ hf hg _) φ
  intro a
  simp only [Function.comp_apply]
  rw [sourceComponentSwap_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
    finiteSourceCurve_componentSwap,l2FundamentalMatrix_of_continuous,l2FundamentalMatrix_of_continuous]
  exact classicalFundamentalMatrix_componentSwap (finiteSourceCurve a) z t

theorem l2FundamentalMatrix_sourceReciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (φ : CoeffPair 2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2FundamentalMatrix (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z t =
      reciprocalScalingMatrix c (l2FundamentalMatrix (sourcePhysicalL2 φ) z t) := by
  have hf := (continuous_source_unit_matrix z t).comp (sourceReciprocalScaling c).continuous
  have h0 := continuous_source_unit_matrix z t
  have hg : Continuous (fun ψ : CoeffPair 2 => reciprocalScalingMatrix c (l2FundamentalMatrix (sourcePhysicalL2 ψ) z t)) := by
    unfold reciprocalScalingMatrix
    fun_prop
  apply congrFun (CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _ hf hg _) φ
  intro a
  simp only [Function.comp_apply]
  rw [sourceReciprocalScaling_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
    finiteSourceCurve_reciprocalScaling,l2FundamentalMatrix_of_continuous,l2FundamentalMatrix_of_continuous]
  exact classicalFundamentalMatrix_reciprocalScaling c hc (finiteSourceCurve a) z t

theorem l2FundamentalMatrix_sourceSpatialReflection (φ : CoeffPair 2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2FundamentalMatrix (sourcePhysicalL2 (sourceSpatialReflection φ)) z t =
      spatialReflectionFundamentalMatrix (l2Monodromy (sourcePhysicalL2 φ) z)
        (l2FundamentalMatrix (sourcePhysicalL2 φ) z
          ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩) := by
  have hf := (continuous_source_unit_matrix z t).comp sourceSpatialReflection.continuous
  have hm := continuous_source_monodromy z
  have ht := continuous_source_unit_matrix z ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
  have hg : Continuous (fun ψ : CoeffPair 2 => spatialReflectionFundamentalMatrix
      (l2Monodromy (sourcePhysicalL2 ψ) z) (l2FundamentalMatrix (sourcePhysicalL2 ψ) z
        ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩)) := by
    unfold spatialReflectionFundamentalMatrix
    fun_prop
  apply congrFun (CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _ hf hg _) φ
  intro a
  simp only [Function.comp_apply]
  rw [sourceSpatialReflection_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
    finiteSourceCurve_reflected,l2FundamentalMatrix_of_continuous,l2FundamentalMatrix_of_continuous,
    l2Monodromy_of_continuous]
  exact classicalFundamentalMatrix_spatialReflection (finiteSourceCurve a) z t

end NLS.ZakharovShabat
