import NLS.ZakharovShabat.GlobalClassicalRenormalizedNLS
import NLS.ZakharovShabat.SmoothPeriodOneSourceExponent

/-! # Smooth data and their constructed classical source curves

Each smooth period-one datum determines both global classical solutions.
The source at time zero is its original Fourier source at every exponent.
-/
noncomputable section
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- A smooth scalar period-one initial function, represented on the period-two circle. -/
structure SmoothNLSData where
  value : C(AddCircle (2 : ℝ), ℂ)
  smooth : ContDiff ℝ ∞ (fun x : ℝ => value (x : AddCircle (2 : ℝ)))
  periodic : Function.Periodic (fun x : ℝ => value (x : AddCircle (2 : ℝ))) 1

namespace SmoothNLSData
variable (f : SmoothNLSData)

/-- The original Fourier source of the prescribed datum. -/
def source (p : ℝ≥0∞) [Fact (1 ≤ p)] : realTypeSourceSubmodule p :=
  smoothPeriodOneSourceAt p f.value f.smooth f.periodic

/-- The constructed global ordinary classical solution. -/
def ordinary : ℝ → C(AddCircle (2 : ℝ), ℂ) :=
  globalClassicalNLS (fun x : ℝ => f.value (x : AddCircle (2 : ℝ))) f.smooth f.periodic

theorem ordinary_isClassical : IsClassicalNLSTrajectory f.ordinary :=
  globalClassicalNLS_isClassical _ f.smooth f.periodic

@[simp] theorem ordinary_zero : f.ordinary 0 = f.value := by
  apply ContinuousMap.ext
  intro x
  exact Quotient.inductionOn x (fun r => congrFun
    (globalClassicalNLS_initial _ f.smooth f.periodic) r)

/-- The constructed global renormalized classical solution with the datum's own mass. -/
def renormalized : ℝ → C(AddCircle (2 : ℝ), ℂ) :=
  globalClassicalRenormalizedNLS (fun x : ℝ => f.value (x : AddCircle (2 : ℝ))) f.smooth f.periodic

theorem renormalized_isClassical :
    IsClassicalRenormalizedNLSTrajectory (classicalNLSMass (f.renormalized 0)) f.renormalized := by
  rw [show classicalNLSMass (f.renormalized 0) =
    ∫ x in (0 : ℝ)..1, ‖f.value (x : AddCircle (2 : ℝ))‖^2 from
      globalClassicalRenormalizedNLS_mass _ f.smooth f.periodic 0]
  exact globalClassicalRenormalizedNLS_isClassical _ f.smooth f.periodic

@[simp] theorem renormalized_zero : f.renormalized 0 = f.value := by
  apply ContinuousMap.ext
  intro x
  exact Quotient.inductionOn x (fun r => congrFun
    (globalClassicalRenormalizedNLS_initial _ f.smooth f.periodic) r)

/-- The ordinary classical solution in the original source norm. -/
def ordinarySource (p : ℝ≥0∞) [Fact (1 ≤ p)] (time : ℝ) : realTypeSourceSubmodule p :=
  smoothPeriodOneSourceAt p (f.ordinary time)
    (f.ordinary_isClassical.spatial_smooth time) (f.ordinary_isClassical.periodic time)

/-- The renormalized classical solution in the original source norm. -/
def renormalizedSource (p : ℝ≥0∞) [Fact (1 ≤ p)] (time : ℝ) : realTypeSourceSubmodule p :=
  smoothPeriodOneSourceAt p (f.renormalized time)
    (f.renormalized_isClassical.spatial_smooth time) (f.renormalized_isClassical.periodic time)

@[simp] theorem ordinarySource_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    f.ordinarySource p 0 = f.source p := by
  unfold ordinarySource
  simp only [ordinary_zero]
  rfl

@[simp] theorem renormalizedSource_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    f.renormalizedSource p 0 = f.source p := by
  unfold renormalizedSource
  simp only [renormalized_zero]
  rfl

end SmoothNLSData
end NLS.ZakharovShabat
