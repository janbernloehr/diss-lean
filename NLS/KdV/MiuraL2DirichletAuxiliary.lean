import NLS.KdV.HillMiuraL2Discriminant
import NLS.MKdV.QuasiHillL2WeakSolution
import NLS.MKdV.QuasiHillL2InitialValue
import NLS.ZakharovShabat.SourceAuxiliaryCharacteristicNormalization
import NLS.ZakharovShabat.L2FundamentalInitialValue

/-! Exact original auxiliary Dirac normalization of the rough scalar
Dirichlet characteristic. The identity includes z=0 without division by z;
the actual auxiliary Dirichlet endpoint signs are retained. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

/-- The diagonal coefficient source has its literal equal-component
physical unit-period L2 representative. -/
theorem hillMiuraDiagonal_physical_representative (u : Coeff 2) :
    intervalL2Representative (sourcePhysicalL2 (hillMiuraDiagonal u)) =
      fun x => (unitL2SynthesisEquiv u x,unitL2SynthesisEquiv u x) := by
  rw [← sourcePhysicalL2Equiv_apply]
  change (fun x => (unitL2SynthesisEquiv (hillMiuraDiagonal u).fst x,
    unitL2SynthesisEquiv (hillMiuraDiagonal u).snd x)) = _
  rw [hillMiuraDiagonal_fst,hillMiuraDiagonal_snd]

/-- The actual physical L2 Dirac solution gives the actual rough scalar
solution by the original Miura state map. No injectivity at zero is needed. -/
theorem quasiHillL2SolutionCurve_eq_transformedDirac
    (u : Coeff 2) (z : ℂ) (v : ℂ × ℂ) :
    quasiHillL2SolutionCurve u (z^2) (miuraStateMap 0 z v) =
      ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) (miuraStateMap 0 z)
        (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z v) := by
  let W := ContinuousLinearMap.compLeftContinuous ℂ (Icc (0:ℝ) 1) (miuraStateMap 0 z)
    (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z v)
  have hW : AbsolutelyContinuousOnInterval (extend W) 0 1 :=
    absolutelyContinuousOnInterval_clm
      (absolutelyContinuousOnInterval_l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z v)
      ((miuraStateMap 0 z).restrictScalars ℝ)
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend W)
      (quasiHillCoefficient (unitL2SynthesisEquiv u x) (z^2) (extend W x)) x := by
    filter_upwards [ae_hasDerivAt_l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z v]
      with x hx
    have h := ((miuraStateMap 0 z).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt x hx
    change HasDerivAt
      (fun y => miuraStateMap 0 z (extend (l2SolutionCurve _ _ _) y))
      (miuraStateMap 0 z (classicalODECoefficient
        (intervalL2Representative (sourcePhysicalL2 (hillMiuraDiagonal u)) x) z
        (extend (l2SolutionCurve _ _ _) x))) x at h
    rw [hillMiuraDiagonal_physical_representative,← quasiHillCoefficient_intertwine] at h
    exact h
  have he := quasiHillL2SolutionCurve_unique_of_ac u (z^2) W hW hd
  have hi : W ⟨0,by constructor <;> norm_num⟩ = miuraStateMap 0 z v := by
    change miuraStateMap 0 z (l2SolutionCurve _ _ _ ⟨0,by constructor <;> norm_num⟩) = _
    rw [l2SolutionCurve_zero]
  rw [hi] at he
  exact he.symm

/-- The original auxiliary Dirichlet characteristic is exactly z times
the scalar Dirichlet characteristic at energy z squared, for every complex
L2 lift and every complex z. In particular no additional scalar zero at
energy zero is introduced by the Dirac characteristic's zero at z=0. -/
theorem auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet (u : Coeff 2) (z : ℂ) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) z = z*quasiHillL2Dirichlet u (z^2) := by
  have hi : miuraStateMap 0 z (1,I) = (-2*I*z) • ((0,1) : ℂ × ℂ) := by
    apply Prod.ext <;> simp only [miuraStateMap_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring_nf
    all_goals simp [I_sq]
    all_goals ring
  have he := congrArg (fun F : Curve (ℂ × ℂ) =>
    (F ⟨1,by constructor <;> norm_num⟩).1)
      (quasiHillL2SolutionCurve_eq_transformedDirac u z (1,I))
  rw [hi,quasiHillL2SolutionCurve_smul] at he
  change (-2*I*z)*quasiHillL2Dirichlet u (z^2) =
    (l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)
      ⟨1,by constructor <;> norm_num⟩).1+
    I*(l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)
      ⟨1,by constructor <;> norm_num⟩).2 at he
  rw [l2SolutionCurve_linearCombination] at he
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul] at he
  rw [sourceAuxiliaryCharacteristic_eq_l2_monodromy]
  let a := l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,0)
    ⟨1,by constructor <;> norm_num⟩
  let b := l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (0,1)
    ⟨1,by constructor <;> norm_num⟩
  change (-2*I*z)*quasiHillL2Dirichlet u (z^2) = a.1+I*b.1+I*(a.2+I*b.2) at he
  simp only [BoundaryCondition.extensionSign,one_mul]
  change (b.2-a.1-I*(a.2+b.1))/(2*I) = z*quasiHillL2Dirichlet u (z^2)
  apply (div_eq_iff (mul_ne_zero (by norm_num) I_ne_zero)).mpr
  linear_combination (norm := (ring_nf; simp [I_sq])) he

/-- Away from zero frequency the actual auxiliary and scalar Dirichlet
zero criteria coincide, with the original physical diagonal potential. -/
theorem auxiliaryDirichlet_eq_zero_iff_quasiHillL2Dirichlet
    (u : Coeff 2) (z : ℂ) (hz : z ≠ 0) :
    auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
      (hillMiuraDiagonal u) z = 0 ↔ quasiHillL2Dirichlet u (z^2) = 0 := by
  rw [auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet,mul_eq_zero]
  exact or_iff_right hz

end NLS.KdV
