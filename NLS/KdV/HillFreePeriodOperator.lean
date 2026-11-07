import NLS.KdV.HillFreePeriodJacobian
import NLS.KdV.MiuraHillPsiNumerators

/-! The free PERIOD derivative rows are exactly the coordinate rows
of the identity on the original positive inverse-index l2 space.
One bounded inverse, of norm one, works before ALL numerator indices.
Identifying a derivative of a nonlinear l2-valued period map still
requires the missing uniform output bounds and map assembly. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.LpSequence

theorem positiveL2_nontrivial : Nontrivial (lp (fun _ : ℕ+ => ℂ) 2) := by
  refine ⟨⟨lp.single 2 (1:ℕ+) 1,0,?_⟩⟩
  intro h
  have hv := congrArg (fun a : lp (fun _ : ℕ+ => ℂ) 2 => a (1:ℕ+)) h
  norm_num [lp.single_apply,Pi.single_apply] at hv

end NLS.LpSequence
namespace NLS.KdV

theorem nonempty_hillFreePeriodCircle (m : ℕ+) :
    Nonempty (SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) := by
  obtain ⟨A⟩ := nonempty_miuraHillPsiFamily
  let u : PeriodOneRealL2 := ⟨0,by intro k; simp⟩
  have h := A.nonempty_periodCircle 0 (A.real_mem_source u) m
  simpa only [map_zero] using h

def hillFreePeriodCircle (m : ℕ+) :
    SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ) :=
  Classical.choice (nonempty_hillFreePeriodCircle m)

theorem hillFreePeriodEquationRow_fderiv_eq_eval (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ)) :
    fderiv ℂ (hillFreePeriodEquationRow n m D) 0 = lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
  intro r
  let L := (fderiv ℂ (hillFreePeriodEquationRow n m D) 0).comp
    (lp.singleContinuousLinearMap ℂ (fun _ : ℕ+ => ℂ) 2 r)
  let K := (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).comp
    (lp.singleContinuousLinearMap ℂ (fun _ : ℕ+ => ℂ) 2 r)
  have he : L 1 = K 1 := by
    change fderiv ℂ (hillFreePeriodEquationRow n m D) 0 (lp.single 2 r 1) =
      (lp.single 2 r 1 : lp (fun _ : ℕ+ => ℂ) 2) m
    rw [hillFreePeriodEquationRow_fderiv_single]
    simp only [lp.single_apply,Pi.single_apply]
  apply ContinuousLinearMap.ext
  intro z
  change L z = K z
  calc
    L z = z • L 1 := by rw [← map_smul]; simp only [smul_eq_mul,mul_one]
    _ = z • K 1 := by rw [he]
    _ = K z := by rw [← map_smul]; simp only [smul_eq_mul,mul_one]

def hillFreePeriodJacobianOperator : lp (fun _ : ℕ+ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  ContinuousLinearMap.id ℂ _

def hillFreePeriodJacobianEquiv : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2 :=
  ContinuousLinearEquiv.refl ℂ _

theorem hillFreePeriodJacobianOperator_rows (n m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (0:CoeffPair 2) ((m:ℕ):ℤ))
    (h : lp (fun _ : ℕ+ => ℂ) 2) :
    fderiv ℂ (hillFreePeriodEquationRow n m D) 0 h = hillFreePeriodJacobianOperator h m := by
  rw [hillFreePeriodEquationRow_fderiv_eq_eval]
  rfl

theorem hillFreePeriodJacobianEquiv_apply (h : lp (fun _ : ℕ+ => ℂ) 2) :
    hillFreePeriodJacobianEquiv h = hillFreePeriodJacobianOperator h := rfl

theorem norm_hillFreePeriodJacobianOperator : ‖hillFreePeriodJacobianOperator‖ = 1 := by
  let := LpSequence.positiveL2_nontrivial
  exact ContinuousLinearMap.norm_id

theorem norm_hillFreePeriodJacobianInverse : ‖hillFreePeriodJacobianEquiv.symm.toContinuousLinearMap‖ = 1 := by
  let := LpSequence.positiveL2_nontrivial
  change ‖ContinuousLinearMap.id ℂ (lp (fun _ : ℕ+ => ℂ) 2)‖ = 1
  exact ContinuousLinearMap.norm_id

end NLS.KdV
