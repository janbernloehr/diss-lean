import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.WeightedSpatialTranslationDerivative

/-! The literal distributional Miura map commutes with actual period-one
spatial translation, with the physical2*pi symbol and the same shift. -/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS

/-- The actual period-one distributional spatial derivative of an L2 input. -/
def periodOneL2SpatialDerivative : Coeff 2 →L[ℂ] PeriodOneHminusOne :=
  periodOneMassOperator 0-periodOneL2Inclusion

theorem periodOneL2SpatialDerivative_apply (u : Coeff 2) (k : ℤ) :
    (periodOneL2SpatialDerivative u).val k=2*I*(Real.pi:ℂ)*k*u k := by
  change (periodOneMassOperator 0 u).val k-(periodOneL2Inclusion u).val k= _
  rw [periodOneMassOperator_apply,periodOneL2Inclusion_apply]
  simp only [periodOneMassSymbol,Nat.cast_zero,zero_add,Complex.ofReal_one]
  ring

theorem periodOneL2Inclusion_spatialTranslation (t : ℝ) (u : Coeff 2) :
    periodOneL2Inclusion (Coeff.spatialTranslation (2*Real.pi) t u)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (periodOneL2Inclusion u) := by
  apply Subtype.ext
  funext k
  simp only [periodOneL2Inclusion_apply,Coeff.spatialTranslation_apply,WeightedCoeff.spatialTranslation_apply]

theorem periodOneL2Constant_spatialTranslation (t : ℝ) (c : ℂ) :
    WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t
      (periodOneL2Inclusion (lp.single 2 0 c))=periodOneL2Inclusion (lp.single 2 0 c) := by
  apply Subtype.ext
  funext k
  by_cases hk : k=0
  · simp [WeightedCoeff.spatialTranslation_apply,periodOneL2Inclusion_apply,hk]
  · simp [WeightedCoeff.spatialTranslation_apply,periodOneL2Inclusion_apply,lp.single_apply,hk]

theorem periodOneMiuraProduct_spatialTranslation (t : ℝ) (u v : Coeff 2) :
    periodOneMiuraProduct (Coeff.spatialTranslation (2*Real.pi) t u)
      (Coeff.spatialTranslation (2*Real.pi) t v)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (periodOneMiuraProduct u v) := by
  apply Subtype.ext
  funext k
  rw [periodOneMiuraProduct_apply,WeightedCoeff.spatialTranslation_apply,periodOneMiuraProduct_apply,← tsum_mul_left]
  apply tsum_congr
  intro j
  simp only [Coeff.spatialTranslation_apply]
  have he := spatialTranslation_phase_add (2*Real.pi) t (k-j) j
  rw [sub_add_cancel] at he
  rw [he]
  ring

theorem periodOneMiura_spatialTranslation (t : ℝ) (u : Coeff 2) :
    periodOneMiura (Coeff.spatialTranslation (2*Real.pi) t u)=
      WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (periodOneMiura u) := by
  apply Subtype.ext
  funext k
  have hp := congrArg (fun q : PeriodOneHminusOne => q.val k) (periodOneMiuraProduct_spatialTranslation t u u)
  simp only [periodOneMiuraProduct_apply,WeightedCoeff.spatialTranslation_apply] at hp
  rw [periodOneMiura_apply,WeightedCoeff.spatialTranslation_apply,periodOneMiura_apply,Coeff.spatialTranslation_apply,hp]
  ring

/-- Every L2 source has a strongly differentiable Hminus-one translation
orbit, retaining the physical2*pi derivative and EVERY real time. -/
theorem hasDerivAt_periodOneL2Inclusion_spatialTranslation (u : Coeff 2) (t : ℝ) :
    HasDerivAt (fun r => WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) r
      (periodOneL2Inclusion u))
      (WeightedCoeff.spatialTranslation (Weight.sobolev (-1)) (2*Real.pi) t (periodOneL2SpatialDerivative u)) t := by
  apply WeightedCoeff.hasDerivAt_spatialTranslation _ (by simp)
  intro n
  rw [periodOneL2SpatialDerivative_apply,periodOneL2Inclusion_apply]
  push_cast
  ring

end NLS
