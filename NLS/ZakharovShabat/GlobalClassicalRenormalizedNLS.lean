import NLS.ZakharovShabat.GlobalClassicalNLSExistence

/-! # Global smooth renormalized NLS with its actual initial mass

The physical gauge turns the constructed global ordinary solution into the
unique global renormalized classical solution. Its mass parameter is the
literal mass of the prescribed smooth periodic initial function.
-/
noncomputable section
open Set
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The constructed ordinary solution's initial mass is the prescribed physical integral. -/
theorem globalClassicalNLS_initial_mass (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    classicalNLSMass (globalClassicalNLS f hf hp 0) = ∫ x in (0 : ℝ)..1, ‖f x‖^2 := by
  rw [classicalNLSMass_eq_integral _ ((globalClassicalNLS_isClassical f hf hp).periodic 0)]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [congrFun (globalClassicalNLS_initial f hf hp) x]

/-- The physical mass remains the original prescribed mass for all real times. -/
theorem globalClassicalNLS_mass (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (time : ℝ) :
    classicalNLSMass (globalClassicalNLS f hf hp time) = ∫ x in (0 : ℝ)..1, ‖f x‖^2 :=
  ((globalClassicalNLS_isClassical f hf hp).mass_eq time 0).trans (globalClassicalNLS_initial_mass f hf hp)

/-- The global renormalized solution, with mass fixed by the actual initial function. -/
def globalClassicalRenormalizedNLS (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ℝ → C(AddCircle (2 : ℝ), ℂ) :=
  classicalNLSGauge (∫ x in (0 : ℝ)..1, ‖f x‖^2) (globalClassicalNLS f hf hp)

theorem globalClassicalRenormalizedNLS_initial
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    (fun x : ℝ => globalClassicalRenormalizedNLS f hf hp 0 (x : AddCircle (2 : ℝ))) = f := by
  simpa only [globalClassicalRenormalizedNLS,classicalNLSGauge_zero_time] using globalClassicalNLS_initial f hf hp

theorem globalClassicalRenormalizedNLS_isClassical
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    IsClassicalRenormalizedNLSTrajectory (∫ x in (0 : ℝ)..1, ‖f x‖^2)
      (globalClassicalRenormalizedNLS f hf hp) :=
  (globalClassicalNLS_isClassical f hf hp).gauge _

theorem globalClassicalRenormalizedNLS_mass
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) (time : ℝ) :
    classicalNLSMass (globalClassicalRenormalizedNLS f hf hp time) = ∫ x in (0 : ℝ)..1, ‖f x‖^2 := by
  rw [globalClassicalRenormalizedNLS,classicalNLSMass_gauge]
  exact globalClassicalNLS_mass f hf hp time

/-- Global renormalized classical existence and uniqueness for every smooth
periodic datum, using its actual mass rather than an independent parameter. -/
theorem existsUnique_global_classicalRenormalizedNLS_of_smooth_periodic
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    ∃! u : ℝ → C(AddCircle (2 : ℝ), ℂ),
      (fun x : ℝ => u 0 (x : AddCircle (2 : ℝ))) = f ∧
      IsClassicalRenormalizedNLSTrajectory (∫ x in (0 : ℝ)..1, ‖f x‖^2) u := by
  refine ⟨globalClassicalRenormalizedNLS f hf hp,
    ⟨globalClassicalRenormalizedNLS_initial f hf hp,globalClassicalRenormalizedNLS_isClassical f hf hp⟩,?_⟩
  intro v hv
  apply hv.2.eq_of_eq_at (globalClassicalRenormalizedNLS_isClassical f hf hp) 0
  apply ContinuousMap.ext
  intro x
  exact Quotient.inductionOn x (fun r => (congrFun hv.1 r).trans
    (congrFun (globalClassicalRenormalizedNLS_initial f hf hp) r).symm)

end NLS.ZakharovShabat
