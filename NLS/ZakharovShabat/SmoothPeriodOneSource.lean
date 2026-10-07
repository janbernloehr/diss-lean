import NLS.Fourier.SobolevIdentification
import NLS.SequenceSpaces.ConjugateReflection
import NLS.ZakharovShabat.SourceClassicalNLSAgreement

/-! # The original H¹ source of a smooth period-one function

Even ambient-circle Fourier modes recover the actual unit-period coefficients.
Their H¹ membership follows from classical Sobolev regularity. Conjugate
reflection supplies the second real component, and synthesis recovers the
original continuous function everywhere.
-/
noncomputable section
open Set Filter Topology MeasureTheory Complex NLS.Fourier
open scoped ENNReal ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- Smooth circle functions satisfy the classical periodic H¹ conditions. -/
theorem hasPeriodicH1Regularity_of_contDiff (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ)))) : HasPeriodicH1Regularity f := by
  refine ⟨(hf.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval,?_⟩
  have hd := (contDiff_infty_iff_deriv.mp hf).2.continuous
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (hd.continuousOn (s := Icc (0 : ℝ) 2))
  apply MemLp.of_bound hd.aestronglyMeasurable R
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hR x ⟨hx.1.le,hx.2⟩

/-- The actual unit-period coefficients retain one full Sobolev derivative. -/
theorem memlp_sobolev_periodOneCoefficient (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : HasPeriodicH1Regularity f)
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    Memℓp (fun n : ℤ => (Weight.sobolev 1 n : ℂ) *
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n) 2 := by
  let c := Coeff.periodHalve (WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 (sobolevCoefficients f hf))
  have he (n : ℤ) : fourierCoeff f (2*n) =
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n := by
    rw [← periodTwoCoefficient_circle]
    exact periodTwoCoefficient_periodic_even _ hp
      ((f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))).intervalIntegrable 0 1) n
  apply (lp.memℓp c).mono'
  intro n
  change ‖(Weight.sobolev 1 n : ℂ)*periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n‖ ≤
    ‖(Weight.sobolev 1 (2*n) : ℂ)*fourierCoeff f (2*n)‖
  rw [he]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev 1).positive n),abs_of_pos ((Weight.sobolev 1).positive (2*n))]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simp only [Weight.sobolev_apply,Real.rpow_one,Int.cast_mul,Int.cast_ofNat,abs_mul,Nat.abs_ofNat]
  linarith [abs_nonneg (n : ℝ)]

/-- Original period-one H¹ coefficients, with no choice of representative. -/
def periodOneH1Coefficients (f : C(AddCircle (2 : ℝ), ℂ)) (hf : HasPeriodicH1Regularity f)
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) : ScalarDomain 2 :=
  ⟨periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))),memlp_sobolev_periodOneCoefficient f hf hp⟩

/-- The real H¹ pair associated to the original physical function. -/
def periodOneH1Source (f : C(AddCircle (2 : ℝ), ℂ)) (hf : HasPeriodicH1Regularity f)
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) : realTypeSobolevSourceLocus :=
  let a := periodOneH1Coefficients f hf hp
  let b := WeightedCoeff.conjugateReflection (Weight.sobolev 1) (by intro n; simp) a
  ⟨(a,b),by
    have h (n : ℤ) : scalarInclusion b n = conj (scalarInclusion a (-n)) := by
      simp only [b,scalarInclusion_apply,WeightedCoeff.conjugateReflection_apply]
    exact h⟩

/-- Reconstruction is pointwise equality of continuous circle functions. -/
theorem periodOneSobolevSynthesis_periodOneH1Source (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : HasPeriodicH1Regularity f)
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    periodOneSobolevSynthesis (periodOneH1Source f hf hp).val.1 = f := by
  have he := periodOneSobolevSynthesis_eq_of_coefficients (periodOneH1Coefficients f hf hp)
    (fun x : ℝ => f (x : AddCircle (2 : ℝ)))
    (f.continuous.comp (AddCircle.continuous_mk' (2 : ℝ))) hp (fun _ => rfl)
  apply ContinuousMap.ext
  intro x
  exact Quotient.inductionOn x (fun r => congrFun he r)

/-- Canonical real H¹ source of arbitrary smooth period-one initial data. -/
def smoothPeriodOneSource (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) : realTypeSobolevSourceLocus :=
  periodOneH1Source f (hasPeriodicH1Regularity_of_contDiff f hf) hp

@[simp] theorem periodOneSobolevSynthesis_smoothPeriodOneSource (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) :
    periodOneSobolevSynthesis (smoothPeriodOneSource f hf hp).val.1 = f :=
  periodOneSobolevSynthesis_periodOneH1Source f _ hp

@[simp] theorem smoothPeriodOneSource_fst (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) (n : ℤ) :
    (smoothPeriodOneSource f hf hp).val.1.val n =
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n := rfl

/-- The coefficient-identical Hilbert source of smooth physical data. -/
def smoothPeriodOneHilbertSource (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) : realTypeSourceSubmodule 2 :=
  ⟨sobolevSourceInclusion (smoothPeriodOneSource f hf hp).val,(smoothPeriodOneSource f hf hp).property⟩

@[simp] theorem smoothPeriodOneHilbertSource_fst (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => f (x : AddCircle (2 : ℝ))))
    (hp : Function.Periodic (fun x : ℝ => f (x : AddCircle (2 : ℝ))) 1) (n : ℤ) :
    (smoothPeriodOneHilbertSource f hf hp).val.fst n =
      periodOneCoefficient (fun x : ℝ => f (x : AddCircle (2 : ℝ))) n := by
  exact sobolevSourceInclusion_fst _ n

end NLS.ZakharovShabat
