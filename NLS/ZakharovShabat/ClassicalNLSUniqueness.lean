import NLS.ZakharovShabat.ClassicalNLSDifferenceEstimate
import NLS.Fourier.ContinuousSynthesis
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Uniqueness of smooth periodic NLS trajectories

We measure differences in L², while requiring time differentiability in
the uniform norm. This lets the pointwise PDE determine the L² energy
velocity without a separate differentiation-under-the-integral assumption.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
namespace NLS.ZakharovShabat

/-- The scalar NLS velocity retains the spatial period. -/
theorem periodic_scalarClassicalNLSVectorField (u : ℝ → ℂ)
    (hp : Function.Periodic u 1) : Function.Periodic (scalarClassicalNLSVectorField u) 1 := by
  intro x
  simp only [scalarClassicalNLSVectorField,
    periodic_deriv_of_periodic (deriv u) 1 (periodic_deriv_of_periodic u 1 hp) x, hp x]

/-- On period-one functions, normalized period-two Haar integration is
exactly integration over one physical period. -/
theorem integral_circle_eq_unit_of_periodic (f : C(AddCircle (2 : ℝ), ℂ))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    (∫ x, f x ∂AddCircle.haarAddCircle) = ∫ x in (0 : ℝ)..1, f (x : AddCircle (2 : ℝ)) := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (2 : ℝ) 0]
  simp only [zero_add, Complex.real_smul]
  have hc : Continuous (fun x : ℝ => f (x : AddCircle (2 : ℝ))) := f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 2)
  have hshift := hp.intervalIntegral_add_eq 1 0
  norm_num only [one_add_one_eq_two,zero_add] at hshift
  rw [← hsplit,hshift]
  push_cast
  ring

/-- The actual unit-interval pairing agrees with the Hilbert-space pairing. -/
theorem inner_toLp_eq_unit (f g : C(AddCircle (2 : ℝ), ℂ))
    (hf : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1)
    (hg : Function.Periodic (fun x : ℝ => g (x : AddCircle (2 : ℝ))) 1) :
    inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f)
      (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ g) =
      ∫ x in (0 : ℝ)..1, conj (f (x : AddCircle (2 : ℝ)))*g (x : AddCircle (2 : ℝ)) := by
  rw [ContinuousMap.inner_toLp]
  let h : C(AddCircle (2 : ℝ), ℂ) := ⟨fun x => g x*conj (f x), g.continuous.mul f.continuous.star⟩
  have hp : Function.Periodic (fun x : ℝ => h (x : AddCircle (2 : ℝ))) 1 := by
    intro x
    change g ((x+1 : ℝ) : AddCircle (2 : ℝ))*conj (f ((x+1 : ℝ) : AddCircle (2 : ℝ))) = _
    exact congrArg₂ (fun a b : ℂ => a*conj b) (hg x) (hf x)
  change (∫ x, h x ∂AddCircle.haarAddCircle) = _
  rw [integral_circle_eq_unit_of_periodic h hp]
  apply intervalIntegral.integral_congr
  intro x _
  exact mul_comm _ _

/-- The L² norm uses the same physical unit interval as the NLS estimate. -/
theorem norm_toLp_sq_eq_unit (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f‖^2 =
      ∫ x in (0 : ℝ)..1, ‖f (x : AddCircle (2 : ℝ))‖^2 := by
  have hi := inner_toLp_eq_unit f f hf hf
  have hc : Continuous (fun x : ℝ => f (x : AddCircle (2 : ℝ))) := f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))
  have hint : IntervalIntegrable (fun x : ℝ => conj (f (x : AddCircle (2 : ℝ)))*f (x : AddCircle (2 : ℝ))) volume 0 1 :=
    (hc.star.mul hc).intervalIntegrable 0 1
  calc
    _ = (inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f)
        (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ f)).re := norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = _ := by
      rw [hi]
      calc
        _ = ∫ x in (0 : ℝ)..1, (conj (f (x : AddCircle (2 : ℝ)))*f (x : AddCircle (2 : ℝ))).re :=
          (intervalIntegral.intervalIntegral_re hint).symm
        _ = _ := by
          apply intervalIntegral.integral_congr
          intro x _
          dsimp only
          rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- Smooth spatial slices, uniform-norm time differentiability, and the
actual scalar NLS equation. No energy inequality is assumed. -/
structure IsClassicalNLSTrajectory (u : ℝ → C(AddCircle (2 : ℝ), ℂ)) : Prop where
  time_differentiable : Differentiable ℝ u
  spatial_smooth : ∀ time, ContDiff ℝ ∞ (fun x : ℝ => u time (x : AddCircle (2 : ℝ)))
  periodic : ∀ time, Function.Periodic (fun x : ℝ => u time (x : AddCircle (2 : ℝ))) 1
  equation : ∀ (time x : ℝ), deriv u time (x : AddCircle (2 : ℝ)) =
    scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x

/-- Time velocities retain the physical period because they equal the PDE field. -/
theorem IsClassicalNLSTrajectory.velocity_periodic
    {u : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u) (time : ℝ) :
    Function.Periodic (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) 1 := by
  have he : (fun x : ℝ => deriv u time (x : AddCircle (2 : ℝ))) =
      scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) := funext (hu.equation time)
  rw [he]
  exact periodic_scalarClassicalNLSVectorField _ (hu.periodic time)

/-- Squared L² distance of two continuous periodic representatives. -/
def classicalNLSDifferenceEnergy (u v : C(AddCircle (2 : ℝ), ℂ)) : ℝ :=
  ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u-v)‖^2

/-- The energy derivative is derived from uniform-norm differentiability
and the actual PDE; it is not an additional solution hypothesis. -/
theorem IsClassicalNLSTrajectory.hasDerivAt_difference_energy
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (hv : IsClassicalNLSTrajectory v) (time : ℝ) :
    HasDerivAt (fun r => classicalNLSDifferenceEnergy (u r) (v r))
      (2*(∫ x in (0 : ℝ)..1, conj (u time (x : AddCircle (2 : ℝ))-v time (x : AddCircle (2 : ℝ)))*
        (scalarClassicalNLSVectorField (fun y : ℝ => u time (y : AddCircle (2 : ℝ))) x-
         scalarClassicalNLSVectorField (fun y : ℝ => v time (y : AddCircle (2 : ℝ))) x)).re) time := by
  let L := (ContinuousMap.toLp (α := AddCircle (2 : ℝ)) 2 AddCircle.haarAddCircle ℂ (E := ℂ)).restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt time
    (((hu.time_differentiable time).hasDerivAt).sub ((hv.time_differentiable time).hasDerivAt))
  let := InnerProductSpace.rclikeToReal ℂ (Lp ℂ 2 (@AddCircle.haarAddCircle (2 : ℝ) inferInstance))
  have he := hd.norm_sq
  change HasDerivAt (fun r => classicalNLSDifferenceEnergy (u r) (v r))
    (2*(inner ℂ (L (u time-v time)) (L (deriv u time-deriv v time))).re) time at he
  convert he using 1
  congr 1
  change _ = (inner ℂ (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time-v time))
    (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (deriv u time-deriv v time))).re
  rw [inner_toLp_eq_unit _ _ ((hu.periodic time).sub (hv.periodic time))
    ((hu.velocity_periodic time).sub (hv.velocity_periodic time))]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [ContinuousMap.sub_apply]
  rw [hu.equation,hv.equation]

/-- The PDE gives the Grönwall bound for the actual energy derivative. -/
theorem IsClassicalNLSTrajectory.abs_deriv_difference_energy_le
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (hv : IsClassicalNLSTrajectory v) (time M : ℝ) (hM : 0 ≤ M)
    (hum : ‖u time‖ ≤ M) (hvm : ‖v time‖ ≤ M) :
    |deriv (fun r => classicalNLSDifferenceEnergy (u r) (v r)) time| ≤
      12*M^2*classicalNLSDifferenceEnergy (u time) (v time) := by
  rw [(hu.hasDerivAt_difference_energy hv time).deriv]
  unfold classicalNLSDifferenceEnergy
  rw [norm_toLp_sq_eq_unit _ ((hu.periodic time).sub (hv.periodic time))]
  exact abs_scalarClassicalNLS_difference_energy_le _ _ (hu.spatial_smooth time) (hv.spatial_smooth time)
    (hu.periodic time) (hv.periodic time) M hM
    (fun x => ((u time).norm_coe_le_norm _).trans hum)
    (fun x => ((v time).norm_coe_le_norm _).trans hvm)

private theorem energy_zero_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (a b K : ℝ) (ha : f a = 0)
    (hb : ∀ r ∈ Icc (min a b) (max a b), ‖deriv f r‖ ≤ K*‖f r‖) : f b = 0 := by
  by_cases hab : a ≤ b
  · have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      hf.continuous.continuousOn
      (fun r _ => (hf r).hasDerivAt.hasDerivWithinAt) ha
      (fun r hr => hb r (by simpa only [min_eq_left hab,max_eq_right hab] using ⟨hr.1,hr.2.le⟩))
    exact hz b ⟨hab,le_rfl⟩
  · have hba : b ≤ a := le_of_not_ge hab
    have hneg (r : ℝ) : HasDerivAt (fun s => f (-s)) (-deriv f (-r)) r := by
      simpa [Function.comp_def] using! ((hf (-r)).hasDerivAt.comp r (hasDerivAt_neg r))
    have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (hf.continuous.comp continuous_neg).continuousOn
      (fun r _ => (hneg r).hasDerivWithinAt)
      (show f (-(-a)) = 0 by simpa using ha)
      (a := -a) (b := -b) (K := K) (fun r hr => by
        simp only [norm_neg]
        apply hb (-r)
        simp only [min_eq_right hba,max_eq_left hba,mem_Icc]
        constructor <;> linarith [hr.1,hr.2])
    simpa using hz (-b) ⟨by linarith,le_rfl⟩

/-- Classical periodic NLS trajectories with the same value at one time
agree at every real time. The compact-time bound is obtained from continuity;
no uniform bound, energy inequality, or common Fourier support is assumed. -/
theorem IsClassicalNLSTrajectory.eq_of_eq_at
    {u v : ℝ → C(AddCircle (2 : ℝ), ℂ)} (hu : IsClassicalNLSTrajectory u)
    (hv : IsClassicalNLSTrajectory v) (initial : ℝ) (hinit : u initial = v initial) : u = v := by
  funext time
  let e := fun r => classicalNLSDifferenceEnergy (u r) (v r)
  have he : Differentiable ℝ e := fun r => (hu.hasDerivAt_difference_energy hv r).differentiableAt
  obtain ⟨Ru,hRu⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hu.time_differentiable.continuous.continuousOn (s := Icc (min initial time) (max initial time)))
  obtain ⟨Rv,hRv⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hv.time_differentiable.continuous.continuousOn (s := Icc (min initial time) (max initial time)))
  let M := max 0 (max Ru Rv)
  have hM : 0 ≤ M := le_max_left _ _
  have hzero : e time = 0 := energy_zero_of_deriv_bound e he initial time (12*M^2)
    (by simp [e,classicalNLSDifferenceEnergy,hinit]) (fun r hr => by
      have hb := hu.abs_deriv_difference_energy_le hv r M hM
        ((hRu r hr).trans ((le_max_left Ru Rv).trans (le_max_right 0 _)))
        ((hRv r hr).trans ((le_max_right Ru Rv).trans (le_max_right 0 _)))
      have hnonneg : 0 ≤ e r := sq_nonneg _
      simpa only [Real.norm_eq_abs,abs_of_nonneg hnonneg] using hb)
  have hL : ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (u time-v time) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have heq : u time-v time = 0 :=
    ContinuousMap.toLp_injective (p := 2) AddCircle.haarAddCircle (𝕜 := ℂ) (hL.trans (map_zero _).symm)
  exact sub_eq_zero.mp heq

end NLS.ZakharovShabat
