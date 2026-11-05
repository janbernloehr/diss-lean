import NLS.KdV.MiuraL2DirichletAuxiliary
import NLS.MKdV.QuasiHillL2NormingTrace
import NLS.ZakharovShabat.SourcePhaseHilbertMonodromy
import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential

noncomputable section
set_option autoImplicit false
open Set Complex NLS.LinearVolterra NLS.ZakharovShabat NLS.MKdV
namespace NLS.KdV

/-- Entire even descent recovers the original trace at every squared
frequency, independent of the square-root branch. -/
theorem hillMiuraL2Discriminant_square (u : Coeff 2) (z : ℂ) :
    hillMiuraL2Discriminant u (z^2)=hillMiuraFrequencyTrace u z := by
  unfold hillMiuraL2Discriminant
  have hs := ComplexAnalysis.complex_sqrt_sq (z^2)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with he | he
  · rw [he]
  · rw [he,hillMiuraFrequencyTrace_even]

/-- The physical terminal quasi-derivative is the correctly signed
Floquet expression of the phase-rotated ORIGINAL source. This retains
its normalization before imposing any Dirichlet root condition. -/
theorem quasiHillL2DirichletTerminal_sourcePhase (u : Coeff 2) (z : ℂ) (hz : z≠0) :
    2*quasiHillL2DirichletTerminal u (z^2)=
      l2Discriminant (sourcePhysicalL2 (sourcePhase (hillMiuraDiagonal u))) z+
        sourceAntiDiscriminantCandidate (by simp) (by norm_num)
          (sourcePhase (hillMiuraDiagonal u)) z := by
  have hi : miuraStateMap 0 z (1,I)=(-2*I*z) • ((0,1):ℂ × ℂ) := by
    apply Prod.ext <;> simp only [miuraStateMap_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    all_goals ring_nf
    all_goals simp [I_sq]
    all_goals ring
  have he := congrArg (fun F : Curve (ℂ × ℂ) =>
    (F ⟨1,by constructor <;> norm_num⟩).2)
      (quasiHillL2SolutionCurve_eq_transformedDirac u z (1,I))
  rw [hi,quasiHillL2SolutionCurve_smul] at he
  change (-2*I*z)*quasiHillL2DirichletTerminal u (z^2)=
    0*((l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)
      ⟨1,by constructor <;> norm_num⟩).1+
      I*(l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)
      ⟨1,by constructor <;> norm_num⟩).2)-I*z*((l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)
      ⟨1,by constructor <;> norm_num⟩).1-
      I*(l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,I)
      ⟨1,by constructor <;> norm_num⟩).2) at he
  simp only [zero_mul,zero_sub,neg_mul] at he
  rw [l2SolutionCurve_linearCombination] at he
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul] at he
  rw [l2Discriminant_sourcePhase,sourceAntiDiscriminant_sourcePhase_eq_l2]
  change 2*quasiHillL2DirichletTerminal u (z^2)=
    (l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z).trace+
      I*((l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z) 0 1-
        (l2Monodromy (sourcePhysicalL2 (hillMiuraDiagonal u)) z) 1 0)
  rw [Matrix.trace_fin_two]
  let a := l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (1,0)
    ⟨1,by constructor <;> norm_num⟩
  let b := l2SolutionCurve (sourcePhysicalL2 (hillMiuraDiagonal u)) z (0,1)
    ⟨1,by constructor <;> norm_num⟩
  change -(2*I*z*quasiHillL2DirichletTerminal u (z^2))=
    -(I*z*(a.1+I*b.1-I*(a.2+I*b.2))) at he
  change 2*quasiHillL2DirichletTerminal u (z^2)=a.1+b.2+I*(b.1-a.2)
  apply mul_left_cancel₀ (show -I*z≠0 from mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz)
  linear_combination (norm := (ring_nf; simp)) he

/-- Exact comparison with the original energy trace and the ORIGINAL
Hill sheet sign, at every nonzero frequency and every complex L2 lift. -/
theorem sourceAntiDiscriminant_sourcePhase_miura (u : Coeff 2) (z : ℂ) (hz : z≠0) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num)
      (sourcePhase (hillMiuraDiagonal u)) z=
        2*quasiHillL2DirichletTerminal u (z^2)-hillMiuraL2Discriminant u (z^2) := by
  have h := quasiHillL2DirichletTerminal_sourcePhase u z hz
  rw [l2Discriminant_sourcePhase,← canonicalDiscriminant_eq_l2_source] at h
  rw [hillMiuraL2Discriminant_square,hillMiuraFrequencyTrace]
  linear_combination -h

end NLS.KdV
