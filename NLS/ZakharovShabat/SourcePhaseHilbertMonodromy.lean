import NLS.ZakharovShabat.SourcePhaseCompatibility
import NLS.ZakharovShabat.ClassicalPhaseMonodromy
import NLS.ZakharovShabat.L2SourceCharacteristics

noncomputable section
set_option autoImplicit false
open Set Complex Matrix NLS.LinearVolterra
open scoped Matrix.Norms.Elementwise
namespace NLS.ZakharovShabat

/-- The actual source phase retains finite Fourier inputs. -/
theorem sourcePhase_ofFinsupp (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    sourcePhase (CoeffPair.ofFinsupp (p := 2) a) =
      CoeffPair.ofFinsupp (I • a.1,-I • a.2) := by
  apply (CoeffPair.toMax 2).injective
  change (I • Coeff.ofFinsupp a.1,-I • Coeff.ofFinsupp a.2) =
    (Coeff.ofFinsupp (I • a.1),Coeff.ofFinsupp (-I • a.2))
  simp only [map_smul]

/-- On finite Fourier inputs the source rotation is the physical rotation. -/
theorem finiteSourceCurve_sourcePhase (a : (ℤ →₀ ℂ) × (ℤ →₀ ℂ)) :
    finiteSourceCurve (I • a.1,-I • a.2) = classicalSourcePhase (finiteSourceCurve a) := by
  have hs (c : ℂ) (b : ℤ →₀ ℂ) (t : ℝ) :
      Fourier.polynomial (c • b) t=c*Fourier.polynomial b t := by
    unfold Fourier.polynomial
    rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
    simp only [Finsupp.sum,Finset.mul_sum,mul_assoc]
  ext t <;> simp only [finiteSourceCurve,BoundaryCondition.periodOnePair,
    ContinuousMap.coe_mk,classicalSourcePhase_apply,hs,neg_mul]

/-- Exact phase conjugation of the actual monodromy for every complex
Hilbert source. No continuous representative is assumed. -/
theorem l2Monodromy_sourcePhase (φ : CoeffPair 2) (z : ℂ) :
    l2Monodromy (sourcePhysicalL2 (sourcePhase φ)) z =
      !![(l2Monodromy (sourcePhysicalL2 φ) z) 0 0,
        I*(l2Monodromy (sourcePhysicalL2 φ) z) 0 1;
        -I*(l2Monodromy (sourcePhysicalL2 φ) z) 1 0,
        (l2Monodromy (sourcePhysicalL2 φ) z) 1 1] := by
  have hj : Continuous (fun q : ℂ × IntervalPairL2 => l2Monodromy q.2 q.1) :=
    analyticOnNhd_l2Monodromy_joint.continuous
  have hm : Continuous (fun ψ : CoeffPair 2 => (z,sourcePhysicalL2 ψ)) :=
    continuous_const.prodMk sourcePhysicalL2.continuous
  have hc : Continuous (fun ψ : CoeffPair 2 => l2Monodromy (sourcePhysicalL2 ψ) z) := by
    have h := hj.comp hm
    exact h
  have hr : Continuous (fun ψ : CoeffPair 2 =>
      !![(l2Monodromy (sourcePhysicalL2 ψ) z) 0 0,
        I*(l2Monodromy (sourcePhysicalL2 ψ) z) 0 1;
        -I*(l2Monodromy (sourcePhysicalL2 ψ) z) 1 0,
        (l2Monodromy (sourcePhysicalL2 ψ) z) 1 1]) := by
    fun_prop
  have he := CoeffPair.eq_of_continuous_of_finsupp (p := 2) (by simp) _ _
    (hc.comp sourcePhase.continuous) hr (fun a => by
      dsimp only [Function.comp_apply]
      rw [sourcePhase_ofFinsupp,sourcePhysicalL2_ofFinsupp,sourcePhysicalL2_ofFinsupp,
        finiteSourceCurve_sourcePhase,l2Monodromy_of_continuous,l2Monodromy_of_continuous]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [classicalMonodromy_phase_zero_zero,classicalMonodromy_phase_zero_one,
          classicalMonodromy_phase_one_zero,classicalMonodromy_phase_one_one])
  exact congrFun he φ

/-- The rotated source anti-discriminant has the exact off-diagonal sign
in the physical Hilbert monodromy. -/
theorem sourceAntiDiscriminant_sourcePhase_eq_l2 (φ : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCandidate (by simp) (by norm_num) (sourcePhase φ) z =
      I*((l2Monodromy (sourcePhysicalL2 φ) z) 0 1-
        (l2Monodromy (sourcePhysicalL2 φ) z) 1 0) := by
  rw [sourceAntiDiscriminantCandidate_eq_l2,l2AntiDiscriminant,l2Monodromy_sourcePhase]
  simp
  ring

/-- The actual Hilbert trace is unchanged by the source phase. -/
theorem l2Discriminant_sourcePhase (φ : CoeffPair 2) (z : ℂ) :
    l2Discriminant (sourcePhysicalL2 (sourcePhase φ)) z =
      l2Discriminant (sourcePhysicalL2 φ) z := by
  rw [l2Discriminant,l2Monodromy_sourcePhase]
  simp [Matrix.trace_fin_two,l2Discriminant]

end NLS.ZakharovShabat
