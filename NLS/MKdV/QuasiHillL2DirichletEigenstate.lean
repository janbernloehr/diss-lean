import NLS.MKdV.QuasiHillL2DirichletCriterion

/-! Scalar nontriviality and uniqueness of the normalized rough Dirichlet
eigenstate. A nonzero first-order state cannot have identically zero position. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier NLS.ZakharovShabat
namespace NLS.MKdV

/-- The physical weak equation forces the entire state to vanish if
its scalar position vanishes. No pointwise trace of the L2 lift is needed. -/
theorem quasiHillL2Solution_eq_zero_of_fst_eq_zero (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2Solution u lambda w)
    (hz : ∀ t, (w t).1 = 0) : w = 0 := by
  have hf : (fun x : ℝ => (extend w x).1) = fun _ => (0:ℂ) :=
    funext fun x => hz _
  have hae : extend w =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] (fun _ => 0) := by
    filter_upwards [hw.2] with x hx
    have hd0 : HasDerivAt (fun y : ℝ => (extend w y).1) 0 x := by
      rw [hf]
      exact hasDerivAt_const x (0:ℂ)
    have hdx : HasDerivAt (fun y : ℝ => (extend w y).1)
        (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x)).1 x :=
      (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
    have he := hdx.unique hd0
    have h1 : (extend w x).1 = 0 := congrFun hf x
    have h2 : (extend w x).2 = 0 := by
      simpa only [quasiHillCoefficient_apply,h1,mul_zero,zero_add] using he
    exact Prod.ext h1 h2
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hae
  have he := Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0:ℝ) ≠ 1) hae
    (continuous_extend w).continuousOn continuous_const.continuousOn
  apply ContinuousMap.ext
  intro t
  simpa only [extend_coe,ContinuousMap.zero_apply] using he t.property

/-- Nonzero physical weak states have nonzero scalar position somewhere
on the original closed unit interval, and conversely. -/
theorem quasiHillL2Solution_ne_zero_iff_fst (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2Solution u lambda w) :
    w ≠ 0 ↔ ∃ t : Icc (0:ℝ) 1, (w t).1 ≠ 0 := by
  constructor
  · intro hn
    by_contra! hz
    exact hn (quasiHillL2Solution_eq_zero_of_fst_eq_zero u lambda w hw hz)
  · rintro ⟨t,ht⟩ rfl
    exact ht rfl

/-- Every actual Dirichlet state has a unique scalar coefficient in the
normalized column. This explicitly describes its geometric eigenspace. -/
theorem existsUnique_quasiHillL2Dirichlet_scalar (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2DirichletState u lambda w) :
    ∃! c : ℂ, w = c • quasiHillL2SolutionCurve u lambda (0,1) := by
  obtain ⟨c,he,_⟩ := (isQuasiHillL2DirichletState_iff_scalar u lambda w).mp hw
  refine ⟨c,he,?_⟩
  intro d hd
  have h := congrArg (fun f : Curve (ℂ × ℂ) =>
    (f ⟨0,by constructor <;> norm_num⟩).2) (hd.symm.trans he)
  simpa only [ContinuousMap.smul_apply,quasiHillL2SolutionCurve_zero,
    Prod.smul_snd,smul_eq_mul,mul_one] using h

/-- A characteristic zero is exactly a nontrivial scalar solution of
the physical quasi-derivative Dirichlet boundary problem. -/
theorem quasiHillL2Dirichlet_eq_zero_iff_exists_eigenstate (u : Coeff 2) (lambda : ℂ) :
    quasiHillL2Dirichlet u lambda = 0 ↔ ∃ w : Curve (ℂ × ℂ),
      IsQuasiHillL2DirichletState u lambda w ∧ ∃ t : Icc (0:ℝ) 1, (w t).1 ≠ 0 := by
  constructor
  · intro h
    obtain ⟨w,hw,hn⟩ := (quasiHillL2Dirichlet_eq_zero_iff_exists_state u lambda).mp h
    exact ⟨w,hw,(quasiHillL2Solution_ne_zero_iff_fst u lambda w hw.1).mp hn⟩
  · rintro ⟨w,hw,hn⟩
    exact (quasiHillL2Dirichlet_eq_zero_iff_exists_state u lambda).mpr
      ⟨w,hw,(quasiHillL2Solution_ne_zero_iff_fst u lambda w hw.1).mpr hn⟩

end NLS.MKdV
