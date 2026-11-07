import NLS.FunctionalAnalysis.FloquetPeriodUniqueness
import NLS.ZakharovShabat.FundamentalMatrixGaugeAlgebra
import NLS.ZakharovShabat.SourceL2UnitFundamentalSymmetries

/-! # The original L2 fundamental matrix symmetries at every real time

The unit identities extend by exact invertible Floquet transport. No spatial
regularity, reality, generic monodromy entry or choice of eigenvectors is used.
All positive and negative periods, including every seam, are covered.
-/
noncomputable section
open Set Complex Matrix NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

theorem l2WholeLineFundamentalMatrix_on_unit (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2WholeLineFundamentalMatrix u z t = l2FundamentalMatrix u z t := by
  simpa only [Int.cast_zero,zero_add,sub_zero,_root_.zpow_zero,Units.val_one,Matrix.mul_one]
    using l2WholeLineFundamentalMatrix_on_period u z 0 t (by simpa only [Int.cast_zero,zero_add] using t.property)

theorem l2WholeLineFundamentalMatrix_add_one (u : IntervalPairL2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix u z (x+1) = l2WholeLineFundamentalMatrix u z x*l2Monodromy u z := by
  simpa only [Int.cast_one,_root_.zpow_one,coe_l2MonodromyUnit]
    using l2WholeLineFundamentalMatrix_add_int u z x 1

theorem l2WholeLineFundamentalMatrix_sourceComponentSwap (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) x =
      componentSwapMatrix (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x) := by
  apply congrFun (floquet_eq_of_unit_period _ _
    (l2MonodromyUnit (sourcePhysicalL2 (sourceComponentSwap φ)) (-z)) ?_ ?_ ?_) x
  · intro y
    exact l2WholeLineFundamentalMatrix_add_one _ _ y
  · intro y
    change componentSwapMatrix (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (y+1)) =
      componentSwapMatrix (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z y)*
        l2Monodromy (sourcePhysicalL2 (sourceComponentSwap φ)) (-z)
    rw [l2WholeLineFundamentalMatrix_add_one,l2Monodromy_sourceComponentSwap]
    exact componentSwapMatrix_mul _ _
  · intro t
    rw [l2WholeLineFundamentalMatrix_on_unit,l2WholeLineFundamentalMatrix_on_unit,
      l2FundamentalMatrix_sourceComponentSwap]

theorem l2WholeLineFundamentalMatrix_sourceReciprocalScaling (c : ℂ) (hc : c ≠ 0)
    (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z x =
      reciprocalScalingMatrix c (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x) := by
  apply congrFun (floquet_eq_of_unit_period _ _
    (l2MonodromyUnit (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z) ?_ ?_ ?_) x
  · intro y
    exact l2WholeLineFundamentalMatrix_add_one _ _ y
  · intro y
    change reciprocalScalingMatrix c (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (y+1)) =
      reciprocalScalingMatrix c (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z y)*
        l2Monodromy (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z
    rw [l2WholeLineFundamentalMatrix_add_one,l2Monodromy_sourceReciprocalScaling c hc]
    exact reciprocalScalingMatrix_mul c hc _ _
  · intro t
    rw [l2WholeLineFundamentalMatrix_on_unit,l2WholeLineFundamentalMatrix_on_unit,
      l2FundamentalMatrix_sourceReciprocalScaling c hc]

theorem l2WholeLineFundamentalMatrix_sourceSpatialReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceSpatialReflection φ)) z x =
      spatialReflectionFundamentalMatrix (l2Monodromy (sourcePhysicalL2 φ) z)
        (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-x)) := by
  apply congrFun (floquet_eq_of_unit_period _ _
    (l2MonodromyUnit (sourcePhysicalL2 (sourceSpatialReflection φ)) z) ?_ ?_ ?_) x
  · intro y
    exact l2WholeLineFundamentalMatrix_add_one _ _ y
  · intro y
    change spatialReflectionFundamentalMatrix (l2Monodromy (sourcePhysicalL2 φ) z)
        (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-(y+1))) =
      spatialReflectionFundamentalMatrix (l2Monodromy (sourcePhysicalL2 φ) z)
        (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-y))*
          l2Monodromy (sourcePhysicalL2 (sourceSpatialReflection φ)) z
    have ht : l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-y) =
        l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (-y)*l2Monodromy (sourcePhysicalL2 φ) z := by
      simpa only [neg_add_eq_sub] using l2WholeLineFundamentalMatrix_add_one (sourcePhysicalL2 φ) z (-y)
    rw [show (1:ℝ)-(y+1) = -y by ring,ht,l2Monodromy_sourceSpatialReflection]
    have h := spatialReflectionFundamentalMatrix_floquet (l2Monodromy (sourcePhysicalL2 φ) z)
      (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (-y))
    simpa only [det_l2Monodromy,one_smul,spatialReflectionMonodromyMatrix] using h.symm
  · intro t
    let s : Icc (0:ℝ) 1 := ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
    change l2WholeLineFundamentalMatrix _ _ t = spatialReflectionFundamentalMatrix _
      (l2WholeLineFundamentalMatrix _ _ s)
    rw [l2WholeLineFundamentalMatrix_on_unit,l2WholeLineFundamentalMatrix_on_unit,
      l2FundamentalMatrix_sourceSpatialReflection]

theorem l2WholeLineFundamentalMatrix_sourceMidpointReflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) x =
      !![-1,0;0,1]*l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-x)*
        (l2Monodromy (sourcePhysicalL2 φ) z)⁻¹*!![-1,0;0,1] := by
  change l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceComponentSwap (sourceSpatialReflection φ))) (-z) x = _
  rw [l2WholeLineFundamentalMatrix_sourceComponentSwap,l2WholeLineFundamentalMatrix_sourceSpatialReflection,
    componentSwap_spatialReflectionFundamentalMatrix_eq_inverse _ _ (det_l2Monodromy _ _)]

end NLS.ZakharovShabat
