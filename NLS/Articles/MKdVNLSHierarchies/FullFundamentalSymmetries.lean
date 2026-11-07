import NLS.ZakharovShabat.SourceL2WholeLineFundamentalSymmetries
import NLS.Articles.MKdVNLSHierarchies.FullSpectralSymmetries

/-! # Lemma 13's full matrix identities for the Section 2 operator

Every real spatial point, every spectral parameter and every original
complex H0 source is covered, hence in particular the original real-type
H0 sources. The matrices are the actual physical normalized solutions.
The separate component-swapped local operator line in Appendix A requires
its explicit convention adapter; it is not silently identified here.
-/
noncomputable section
open Set Complex Matrix NLS.ZakharovShabat
namespace NLS.Articles.MKdVNLSHierarchies

def fundamentalPhaseGauge (α : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![exp ((α:ℂ)*I/2),0;0,(exp ((α:ℂ)*I/2))⁻¹]

theorem fundamentalPhaseGauge_entries (α : ℝ) :
    fundamentalPhaseGauge α = !![exp ((α:ℂ)*I/2),0;0,exp (-((α:ℂ)*I/2))] := by
  simp only [fundamentalPhaseGauge,exp_neg]

theorem lemma13_componentSwap (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceComponentSwap φ)) (-z) x =
      !![0,1;-1,0]*l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x*
        (!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ := by
  rw [l2WholeLineFundamentalMatrix_sourceComponentSwap,componentSwapMatrix_eq_conjugate]

theorem lemma13_phase (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourcePhaseRotation α φ)) z x =
      fundamentalPhaseGauge α*l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x*
        (fundamentalPhaseGauge α)⁻¹ := by
  change l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceReciprocalScaling (exp ((α:ℂ)*I)) φ)) z x = _
  rw [l2WholeLineFundamentalMatrix_sourceReciprocalScaling _ (exp_ne_zero _)]
  have he : exp ((α:ℂ)*I/2)*exp ((α:ℂ)*I/2) = exp ((α:ℂ)*I) := by
    rw [← exp_add]
    congr 1
    ring
  have h := reciprocalScalingMatrix_eq_diagonal_conjugate (exp ((α:ℂ)*I/2)) (exp_ne_zero _)
    (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x)
  rw [he] at h
  exact h

theorem lemma13_phase_entries (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourcePhaseRotation α φ)) z x =
      !![(l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x) 0 0,
          exp ((α:ℂ)*I)*(l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x) 0 1;
         exp (-((α:ℂ)*I))*(l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x) 1 0,
          (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z x) 1 1] := by
  change l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceReciprocalScaling (exp ((α:ℂ)*I)) φ)) z x = _
  rw [l2WholeLineFundamentalMatrix_sourceReciprocalScaling _ (exp_ne_zero _)]
  simp only [reciprocalScalingMatrix,exp_neg]

theorem lemma13_reflection (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    l2WholeLineFundamentalMatrix (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) x =
      !![0,1;1,0]*!![0,1;-1,0]*l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-x)*
        (l2Monodromy (sourcePhysicalL2 φ) z)⁻¹*(!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹*!![0,1;1,0] := by
  have hl : (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℂ)*!![0,1;-1,0] = !![-1,0;0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  have hr : ((!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹)*!![0,1;1,0] = !![-1,0;0,1] := by
    rw [inverse_fin_two_of_det_one _ (by norm_num [Matrix.det_fin_two])]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply,Fin.sum_univ_two]
  rw [l2WholeLineFundamentalMatrix_sourceMidpointReflection]
  calc
    _ = (!![0,1;1,0]*!![0,1;-1,0])*l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) z (1-x)*
        (l2Monodromy (sourcePhysicalL2 φ) z)⁻¹*
          ((!![0,1;-1,0] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹*!![0,1;1,0]) := by rw [hl,hr]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem lemma13_reflected_monodromy (φ : CoeffPair 2) (z : ℂ) :
    l2Monodromy (sourcePhysicalL2 (sourceMidpointReflection φ)) (-z) =
      !![(l2Monodromy (sourcePhysicalL2 φ) z) 1 1,(l2Monodromy (sourcePhysicalL2 φ) z) 0 1;
         (l2Monodromy (sourcePhysicalL2 φ) z) 1 0,(l2Monodromy (sourcePhysicalL2 φ) z) 0 0] :=
  l2Monodromy_sourceMidpointReflection φ z

end NLS.Articles.MKdVNLSHierarchies
