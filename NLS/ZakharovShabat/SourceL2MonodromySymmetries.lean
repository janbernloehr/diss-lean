import NLS.ZakharovShabat.SourceReciprocalScaling
import NLS.ZakharovShabat.L2SourceCharacteristics
import NLS.ZakharovShabat.L2WholeLineFundamentalJoint

/-! # Actual Hilbert monodromy under P, pure T and arbitrary reciprocal scaling

The finite Fourier identities are physical normalized IVP identities. Their
unique continuous extension gives every matrix entry at every original
complex L2 source and every spectral parameter, including zero.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

private theorem continuous_sourceL2Monodromy (z : ℂ) :
    Continuous (fun φ : CoeffPair 2 => l2Monodromy (sourcePhysicalL2 φ) z) := by
  have hm : Continuous (fun ψ : CoeffPair 2 => (z,sourcePhysicalL2 ψ)) :=
    continuous_const.prodMk sourcePhysicalL2.continuous
  have h := continuous_l2Monodromy_joint.comp hm
  exact h

private theorem monodromy_symmetry_of_finite
    (A : CoeffPair 2 →L[ℂ] CoeffPair 2) (z w : ℂ)
    (F : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ) (hF : Continuous F)
    (hfinite : ∀ a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ),
      l2Monodromy (sourcePhysicalL2 (A (CoeffPair.ofFinsupp a))) w =
        F (l2Monodromy (sourcePhysicalL2 (CoeffPair.ofFinsupp a)) z))
    (φ : CoeffPair 2) :
    l2Monodromy (sourcePhysicalL2 (A φ)) w = F (l2Monodromy (sourcePhysicalL2 φ) z) := by
  have he := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _
    ((continuous_sourceL2Monodromy w).comp A.continuous) (hF.comp (continuous_sourceL2Monodromy z)) hfinite
  exact congrFun he φ

theorem l2Monodromy_sourceComponentSwap (φ : CoeffPair 2) (z : ℂ) :
    l2Monodromy (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) =
      !![(l2Monodromy (sourcePhysicalL2 φ) z) 1 1,-(l2Monodromy (sourcePhysicalL2 φ) z) 1 0;
        -(l2Monodromy (sourcePhysicalL2 φ) z) 0 1,(l2Monodromy (sourcePhysicalL2 φ) z) 0 0] := by
  apply monodromy_symmetry_of_finite sourceComponentSwap.toContinuousLinearEquiv.toContinuousLinearMap
    z (-z) (fun M => !![M 1 1,-M 1 0;-M 0 1,M 0 0]) (by fun_prop) _ φ
  intro a
  change l2Monodromy (sourcePhysicalL2 (sourceComponentSwap (CoeffPair.ofFinsupp a))) (-z) = _
  rw [sourceComponentSwap_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
    finiteSourceCurve_componentSwap,l2Monodromy_of_continuous,l2Monodromy_of_continuous,
    classicalMonodromy_componentSwap]

theorem l2Monodromy_sourceSpatialReflection (φ : CoeffPair 2) (z : ℂ) :
    l2Monodromy (sourcePhysicalL2 (sourceSpatialReflection φ)) z =
      !![(l2Monodromy (sourcePhysicalL2 φ) z) 0 0,-(l2Monodromy (sourcePhysicalL2 φ) z) 1 0;
        -(l2Monodromy (sourcePhysicalL2 φ) z) 0 1,(l2Monodromy (sourcePhysicalL2 φ) z) 1 1] := by
  apply monodromy_symmetry_of_finite sourceSpatialReflection.toContinuousLinearEquiv.toContinuousLinearMap
    z z (fun M => !![M 0 0,-M 1 0;-M 0 1,M 1 1]) (by fun_prop) _ φ
  intro a
  change l2Monodromy (sourcePhysicalL2 (sourceSpatialReflection (CoeffPair.ofFinsupp a))) z = _
  rw [sourceSpatialReflection_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
    finiteSourceCurve_reflected,l2Monodromy_of_continuous,l2Monodromy_of_continuous,
    classicalMonodromy_spatialReflection]

theorem l2Monodromy_sourceMidpointReflection (φ : CoeffPair 2) (z : ℂ) :
    l2Monodromy (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) =
      !![(l2Monodromy (sourcePhysicalL2 φ) z) 1 1,(l2Monodromy (sourcePhysicalL2 φ) z) 0 1;
        (l2Monodromy (sourcePhysicalL2 φ) z) 1 0,(l2Monodromy (sourcePhysicalL2 φ) z) 0 0] := by
  change l2Monodromy (sourcePhysicalL2 (sourceComponentSwap (sourceSpatialReflection φ))) (-z) = _
  rw [l2Monodromy_sourceComponentSwap,l2Monodromy_sourceSpatialReflection]
  simp

theorem l2Monodromy_sourceReciprocalScaling (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair 2) (z : ℂ) :
    l2Monodromy (sourcePhysicalL2 (sourceReciprocalScaling c φ)) z =
      !![(l2Monodromy (sourcePhysicalL2 φ) z) 0 0,c*(l2Monodromy (sourcePhysicalL2 φ) z) 0 1;
        c⁻¹*(l2Monodromy (sourcePhysicalL2 φ) z) 1 0,(l2Monodromy (sourcePhysicalL2 φ) z) 1 1] := by
  apply monodromy_symmetry_of_finite (sourceReciprocalScaling c) z z
    (fun M => !![M 0 0,c*M 0 1;c⁻¹*M 1 0,M 1 1]) (by fun_prop) _ φ
  intro a
  rw [sourceReciprocalScaling_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
    finiteSourceCurve_reciprocalScaling,l2Monodromy_of_continuous,l2Monodromy_of_continuous]
  exact classicalFundamentalMatrix_reciprocalScaling c hc (finiteSourceCurve a) z ⟨1,by norm_num⟩

end NLS.ZakharovShabat
