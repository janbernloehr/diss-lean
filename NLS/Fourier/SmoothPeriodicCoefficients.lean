import NLS.SequenceSpaces.SobolevAbsoluteSummability
import NLS.Fourier.AbsoluteContinuousCoefficients
import NLS.Fourier.PeriodOneFourierUniqueness

/-! # All Sobolev weights for smooth periodic Fourier coefficients

The derivative coefficient identity and the graph characterization of a
Sobolev derivative give every integer Hilbert order. Inclusion gives real
orders; one extra derivative supplies absolute summability. Even modes then
recover the original unit-period coefficients with their exact normalization.
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace NLS.Fourier

private theorem memLp_two_of_continuous (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (volume.restrict (Ioc 0 2)) := by
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc (0 : ℝ) 2))
  apply MemLp.of_bound hf.aestronglyMeasurable R
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hR x ⟨hx.1.le,hx.2⟩

/-- Every integer Hilbert Sobolev order of a smooth period-two function. -/
theorem memlp_periodTwoCoefficient_nat_sobolev (k : ℕ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2) :
    Memℓp (fun n => (Weight.sobolev k n : ℂ)*periodTwoCoefficient f n) 2 := by
  induction k generalizing f with
  | zero =>
    simpa only [Nat.cast_zero,Weight.sobolev_apply,Real.rpow_zero,Complex.ofReal_one,one_mul] using
      memlp_periodTwoCoefficient (memLp_two_of_continuous f hf.continuous)
  | succ k ih =>
    have hd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
    have hper := ZakharovShabat.periodic_deriv_of_periodic f 2 hp
    have he (n : ℤ) : periodTwoCoefficient (deriv f) n =
        Complex.I*(Real.pi : ℂ)*n*periodTwoCoefficient f n :=
      periodTwoCoefficient_deriv_of_ac_periodic
        ((hf.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval)
        (hd.continuous.intervalIntegrable 0 2) (by simpa only [zero_add] using hp 0) n
    have hder := ih (deriv f) hd hper
    simp only [he] at hder
    simpa only [Nat.cast_add,Nat.cast_one] using
      WeightedCoeff.memlp_sobolev_succ_of_derivative (k : ℝ) (ih f hf hp) hder

/-- Smooth period-two functions have Fourier coefficients in every real
Hilbert Sobolev weight, with no nonnegativity restriction on the order. -/
theorem memlp_periodTwoCoefficient_sobolev_two (s : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*periodTwoCoefficient f n) 2 := by
  obtain ⟨k,hk⟩ := exists_nat_gt s
  let a : WeightedCoeff (Weight.sobolev k) 2 := ⟨periodTwoCoefficient f,memlp_periodTwoCoefficient_nat_sobolev k f hf hp⟩
  have h := (WeightedCoeff.sobolevInclusion hk.le a).property
  change Memℓp (fun n => (Weight.sobolev s n : ℂ)*(WeightedCoeff.sobolevInclusion hk.le a).val n) 2 at h
  convert h using 1
  funext n
  exact congrArg (fun x : ℂ => (Weight.sobolev s n : ℂ)*x)
    (WeightedCoeff.sobolevInclusion_apply hk.le a n).symm

/-- Every real Sobolev weight is absolutely summable for smooth period-two data. -/
theorem memlp_periodTwoCoefficient_sobolev_one (s : ℝ) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 2) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*periodTwoCoefficient f n) 1 :=
  WeightedCoeff.memlp_sobolev_one_of_two_succ s
    (memlp_periodTwoCoefficient_sobolev_two (s+1) f hf hp)

/-- Actual unit-period coefficients of smooth periodic functions have every
nonnegative real absolutely summable Sobolev weight. -/
theorem memlp_periodOneCoefficient_sobolev_one (s : ℝ) (hs : 0 ≤ s) (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*periodOneCoefficient f n) 1 := by
  have hp2 : Function.Periodic f 2 := by simpa using! hp.nat_mul 2
  let a : Coeff 1 := ⟨fun n => (Weight.sobolev s n : ℂ)*periodTwoCoefficient f n,
    memlp_periodTwoCoefficient_sobolev_one s f hf hp2⟩
  apply (lp.memℓp (Coeff.periodHalve a)).mono'
  intro n
  change ‖(Weight.sobolev s n : ℂ)*periodOneCoefficient f n‖ ≤
    ‖(Weight.sobolev s (2*n) : ℂ)*periodTwoCoefficient f (2*n)‖
  rw [periodTwoCoefficient_periodic_even f hp (hf.continuous.intervalIntegrable 0 1)]
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ((Weight.sobolev s).positive _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.rpow_le_rpow (by positivity) _ hs
  simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_nonneg (n : ℝ)]

end NLS.Fourier
