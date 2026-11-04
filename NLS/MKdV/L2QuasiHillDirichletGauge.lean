import NLS.MKdV.L2QuasiHillUniqueness
import NLS.MKdV.L2QuasiHillRegularity
import NLS.MKdV.L2QuasiHillInitialLinearity
import NLS.ZakharovShabat.L2SeparatedCharacteristics

/-! # The actual rough Hill Dirichlet problem in standard NLS boundary coordinates

The phase-rotated profile (i*u,-i*u) makes f1-f2 the scalar position.
The state map (f1-f2,-i*z*(f1+f2)) intertwines the actual integral
equations. The source-normalized Dirichlet characteristic is exactly
z times the normalized scalar characteristic at energy z^2.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def intervalL2DirichletMiura : IntervalL2 →L[ℂ] IntervalPairL2 :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2).symm.toContinuousLinearMap.comp
    ((I • ContinuousLinearMap.id ℂ IntervalL2).prod ((-I) • ContinuousLinearMap.id ℂ IntervalL2))

theorem intervalL2DirichletMiura_representative (u : IntervalL2) :
    intervalL2Representative (intervalL2DirichletMiura u)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (fun t => (I*u t,-I*u t)) := by
  filter_upwards [Lp.coeFn_smul I u,Lp.coeFn_smul (-I) u] with t h1 h2
  change ((I • u) t,((-I) • u) t) = _
  rw [h1,h2]
  rfl

def dirichletMiuraState (z : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ-ContinuousLinearMap.snd ℂ ℂ ℂ).prod
    ((-I*z) • (ContinuousLinearMap.fst ℂ ℂ ℂ+ContinuousLinearMap.snd ℂ ℂ ℂ))

@[simp] theorem dirichletMiuraState_apply (z : ℂ) (v : ℂ × ℂ) :
    dirichletMiuraState z v = (v.1-v.2,-I*z*(v.1+v.2)) := rfl

theorem dirichletMiuraState_intertwine (u z : ℂ) (v : ℂ × ℂ) :
    quasiHillCoefficient u (z^2) (dirichletMiuraState z v) =
      dirichletMiuraState z (classicalODECoefficient (I*u,-I*u) z v) := by
  apply Prod.ext <;> simp only [quasiHillCoefficient_apply,dirichletMiuraState_apply,
    classicalODECoefficient_apply] <;> ring_nf <;> simp [I_sq]
  all_goals ring

theorem l2QuasiHillSolution_eq_dirichletMiura (u : IntervalL2) (z : ℂ) (v : ℂ × ℂ) :
    l2QuasiHillSolution u (z^2) (dirichletMiuraState z v) =
      (ContinuousLinearMap.compLeftContinuous ℂ (Icc (0 : ℝ) 1) (dirichletMiuraState z))
        (l2SolutionCurve (intervalL2DirichletMiura u) z v) := by
  symm
  apply l2QuasiHillSolution_unique_integral
  intro t
  let F := l2SolutionCurve (intervalL2DirichletMiura u) z v
  have hi := intervalIntegrable_l2ODECoefficient (intervalL2DirichletMiura u) z F t
  have he := congrArg (dirichletMiuraState z)
    (l2SolutionCurve_eq_integral (intervalL2DirichletMiura u) z v t)
  rw [map_add,← (dirichletMiuraState z).intervalIntegral_comp_comm hi] at he
  change dirichletMiuraState z (F t) = dirichletMiuraState z v+_ at he
  change dirichletMiuraState z (F t) = _
  rw [he]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (intervalL2DirichletMiura_representative u)] with s hs
  rw [hs,← dirichletMiuraState_intertwine]
  rfl

theorem l2SeparatedCharacteristic_dirichletMiura (u : IntervalL2) (z : ℂ) :
    l2SeparatedCharacteristic .dirichlet (intervalL2DirichletMiura u) z =
      z*extend (l2QuasiHillPosition u (z^2) (0,1)) 1 := by
  let t : Icc (0 : ℝ) 1 := ⟨1,by constructor <;> norm_num⟩
  let F := l2SolutionCurve (intervalL2DirichletMiura u) z (1,1)
  have he := congrArg (fun f : Curve (ℂ × ℂ) => (f t).1)
    (l2QuasiHillSolution_eq_dirichletMiura u z (1,1))
  have hinit : dirichletMiuraState z (1,1) = (-2*I*z) • ((0,1) : ℂ × ℂ) := by
    apply Prod.ext <;> simp only [dirichletMiuraState_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
    <;> ring
  rw [hinit] at he
  have hlin := congrArg (fun f : Curve (ℂ × ℂ) => (f t).1)
    (l2QuasiHillSolution_smul_initial u (z^2) (-2*I*z) (0,1))
  have hpos : (-2*I*z)*extend (l2QuasiHillPosition u (z^2) (0,1)) 1 = (F t).1-(F t).2 := by
    rw [hlin] at he
    rw [extend_coe _ t]
    exact he
  unfold l2SeparatedCharacteristic
  dsimp only [F] at hpos
  rw [l2SolutionCurve_linearCombination (intervalL2DirichletMiura u) z (1,1)] at hpos
  simp only [l2Monodromy,l2FundamentalMatrix,BoundaryCondition.extensionSign,
    ContinuousMap.add_apply,ContinuousMap.smul_apply,Prod.fst_add,Prod.snd_add,
    Prod.smul_fst,Prod.smul_snd,smul_eq_mul,one_mul,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hpos ⊢
  apply (div_eq_iff (mul_ne_zero (by norm_num) I_ne_zero)).mpr
  linear_combination hpos

end NLS.MKdV
