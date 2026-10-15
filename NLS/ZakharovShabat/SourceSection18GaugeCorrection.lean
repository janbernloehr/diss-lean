import NLS.ZakharovShabat.SmoothNLSData

/-!
# The Section 18 physical gauge and a witness against the printed phase

The correct phase is exp(4 i mass t). The constant smooth initial datum
of mass one makes the printed exp(i t) phase fail the actual PDE.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- The constructed smooth renormalized solution is the physical mass gauge
of the constructed ordinary solution. -/
theorem SmoothNLSData.renormalized_eq_physical_gauge (f : SmoothNLSData) :
    f.renormalized = classicalNLSGauge (classicalNLSMass f.value) f.ordinary := by
  rw [classicalNLSMass_eq_integral _ f.periodic]
  rfl

/-- The gauge uses four times the physical mass, that is, four times the squared L² norm. -/
theorem SmoothNLSData.renormalized_phase (f : SmoothNLSData) (time : ℝ) :
    f.renormalized time =
      Complex.exp (((4*classicalNLSMass f.value*time : ℝ) : ℂ)*Complex.I) • f.ordinary time := by
  rw [f.renormalized_eq_physical_gauge]
  rfl

/-- A constructed classical trajectory refutes the printed gauge even at unit mass. -/
theorem original_gauge_printed_phase_counterexample :
    ∃ f : SmoothNLSData, (∀ x, f.value x = 1) ∧ classicalNLSMass f.value = 1 ∧
      ¬ IsClassicalRenormalizedNLSTrajectory (classicalNLSMass f.value)
        (fun time => Complex.exp ((time : ℂ)*Complex.I) • f.ordinary time) := by
  let f : SmoothNLSData := ⟨ContinuousMap.const _ 1,contDiff_const,fun _ => rfl⟩
  have hm : classicalNLSMass f.value = 1 := by
    rw [classicalNLSMass_eq_integral _ f.periodic]
    norm_num [f]
  refine ⟨f,fun _ => rfl,hm,?_⟩
  have he : (fun time : ℝ => Complex.exp ((time : ℂ)*Complex.I) • f.ordinary time) =
      classicalNLSGauge (1/4) f.ordinary := by
    funext time
    simp [classicalNLSGauge,classicalNLSGaugePhase]
  rw [he,hm]
  intro hbad
  have htrue := (f.ordinary_isClassical.gauge (1/4)).equation 0 0
  have hfalse := hbad.equation 0 0
  rw [htrue] at hfalse
  have h := add_left_cancel hfalse
  have hi := congrArg Complex.im h
  norm_num [f,classicalNLSGauge_zero_time,SmoothNLSData.ordinary_zero] at hi

end NLS.ZakharovShabat
