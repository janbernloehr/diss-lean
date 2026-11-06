import NLS.MKdV.QuasiHillL2DirichletCriterion

/-! The physical Lagrange identity for complex L2 Miura lifts. The identity
is proved from absolute continuity and the literal almost-everywhere ODE.
In particular the fundamental determinant is one, including at zero energy. -/
noncomputable section
open Set Complex MeasureTheory Filter Topology NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- The scalar Lagrange identity for any two actual physical weak states
at different complex energies, with no derivative of the L2 lift. -/
theorem quasiHillL2_lagrange_identity (u : Coeff 2) (lambda mu : ℂ)
    (w v : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2Solution u lambda w)
    (hv : IsQuasiHillL2Solution u mu v) :
    (∫ x in (0:ℝ)..1, (lambda-mu)*(extend w x).1*(extend v x).1) =
      ((extend w 1).1*(extend v 1).2-(extend w 1).2*(extend v 1).1)-
        ((extend w 0).1*(extend v 0).2-(extend w 0).2*(extend v 0).1) := by
  have hw1 := absolutelyContinuousOnInterval_clm hw.1 (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hw2 := absolutelyContinuousOnInterval_clm hw.1 (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hv1 := absolutelyContinuousOnInterval_clm hv.1 (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hv2 := absolutelyContinuousOnInterval_clm hv.1 (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hac : AbsolutelyContinuousOnInterval (fun x : ℝ =>
      (extend w x).1*(extend v x).2-(extend w x).2*(extend v x).1) 0 1 := by
    simpa only [Pi.smul_def,smul_eq_mul,Pi.sub_apply,Pi.mul_apply] using!
      (hw1.smul hv2).sub (hw2.smul hv1)
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt
      (fun y => (extend w y).1*(extend v y).2-(extend w y).2*(extend v y).1)
      ((lambda-mu)*(extend w x).1*(extend v x).1) x := by
    filter_upwards [hw.2,hv.2] with x hx hy
    have h1 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
    have h2 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
    have h3 := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hy
    have h4 := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hy
    convert! (h1.mul h4).sub (h2.mul h3) using 1
    change (lambda-mu)*(extend w x).1*(extend v x).1 =
      ((unitL2SynthesisEquiv u x)*(extend w x).1+(extend w x).2)*(extend v x).2+
        (extend w x).1*(-mu*(extend v x).1-(unitL2SynthesisEquiv u x)*(extend v x).2)-
        ((-lambda*(extend w x).1-(unitL2SynthesisEquiv u x)*(extend w x).2)*(extend v x).1+
          (extend w x).2*((unitL2SynthesisEquiv u x)*(extend v x).1+(extend v x).2))
    ring
  have hd' : ∀ᵐ x : ℝ, x ∈ uIcc (0:ℝ) 1 → HasDerivAt
      (fun y => (extend w y).1*(extend v y).2-(extend w y).2*(extend v y).1)
      ((lambda-mu)*(extend w x).1*(extend v x).1) x := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hd
    filter_upwards [hd,(show ∀ᵐ x : ℝ, x ≠ (0:ℝ) by simp [ae_iff])] with x hx hx0
    intro hxi
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hxi
    exact hx ⟨lt_of_le_of_ne hxi.1 (Ne.symm hx0),hxi.2⟩
  have hi : IntervalIntegrable
      (fun x : ℝ => (lambda-mu)*(extend w x).1*(extend v x).1) volume 0 1 :=
    ((continuous_const.mul (continuous_fst.comp (continuous_extend w))).mul
      (continuous_fst.comp (continuous_extend v))).intervalIntegrable _ _
  exact integral_eq_sub_of_ac_of_ae_hasDerivAt hac hi hd'

/-- The actual rough scalar fundamental matrix has determinant one. -/
theorem quasiHillL2_fundamental_determinant (u : Coeff 2) (lambda : ℂ) :
    let a := quasiHillL2SolutionCurve u lambda (1,0) ⟨1,by constructor <;> norm_num⟩
    let b := quasiHillL2SolutionCurve u lambda (0,1) ⟨1,by constructor <;> norm_num⟩
    a.1*b.2-a.2*b.1 = 1 := by
  let w := quasiHillL2SolutionCurve u lambda (1,0)
  let v := quasiHillL2SolutionCurve u lambda (0,1)
  have he := quasiHillL2_lagrange_identity u lambda lambda w v
    (isQuasiHillL2Solution_solutionCurve u lambda (1,0))
    (isQuasiHillL2Solution_solutionCurve u lambda (0,1))
  have h0w : extend w 0 = (1,0) := by
    change extend w (⟨0,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1).val = _
    rw [extend_coe]
    exact quasiHillL2SolutionCurve_zero u lambda (1,0)
  have h0v : extend v 0 = (0,1) := by
    change extend v (⟨0,by constructor <;> norm_num⟩ : Icc (0:ℝ) 1).val = _
    rw [extend_coe]
    exact quasiHillL2SolutionCurve_zero u lambda (0,1)
  have h1w : extend w 1 = w ⟨1,by constructor <;> norm_num⟩ :=
    extend_coe w ⟨1,by constructor <;> norm_num⟩
  have h1v : extend v 1 = v ⟨1,by constructor <;> norm_num⟩ :=
    extend_coe v ⟨1,by constructor <;> norm_num⟩
  simp only [sub_self,zero_mul,intervalIntegral.integral_zero,h0w,h0v,
    h1w,h1v,mul_one,mul_zero,sub_zero] at he
  exact sub_eq_zero.mp he.symm

/-- At a characteristic zero, the normalized eigenfunction has nonzero
terminal quasi-derivative. No division by frequency or energy is used. -/
theorem quasiHillL2Dirichlet_terminal_snd_ne_zero (u : Coeff 2) (lambda : ℂ)
    (hz : quasiHillL2Dirichlet u lambda = 0) :
    (quasiHillL2SolutionCurve u lambda (0,1) ⟨1,by constructor <;> norm_num⟩).2 ≠ 0 := by
  intro hn
  have he := quasiHillL2_fundamental_determinant u lambda
  dsimp only at he
  change (quasiHillL2SolutionCurve u lambda (0,1) ⟨1,by constructor <;> norm_num⟩).1 = 0 at hz
  rw [hz,hn,mul_zero,mul_zero,sub_zero] at he
  exact zero_ne_one he

end NLS.MKdV
