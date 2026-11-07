import NLS.Fourier.UnitIntervalDirichlet
import NLS.Fourier.SignedIntervalH1Extension
import NLS.SequenceSpaces.SobolevEvenSampling

/-! # Exhaustion of the classical zero-endpoint H1 interval domain

No periodicity of an interval input or of its derivative is assumed. Signed
extension with sign one is available because the two endpoint values vanish.
Even sampling recovers precisely the unit-period H1 coefficients. Thus the
zero-trace coefficient domain represents every classical interval H1 function,
and represents it uniquely on the entire closed interval.
-/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.Fourier
open ZakharovShabat

/-- Interval values determine every coefficient of a zero-trace domain vector. -/
theorem unitDirichletRepresentative_injective_on_interval (f g : UnitDirichletH1)
    (h : ∀ x ∈ Icc (0 : ℝ) 1, unitDirichletRepresentative f x = unitDirichletRepresentative g x) :
    f = g := by
  apply Subtype.ext
  apply Subtype.ext
  funext n
  have hae : unitDirichletRepresentative f =ᵐ[volume.restrict (Ioc 0 1)]
      unitDirichletRepresentative g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact h x ⟨hx.1.le, hx.2⟩
  have hc := congrFun (fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) hae) n
  change periodOneCoefficient (unitDirichletRepresentative f) n =
    periodOneCoefficient (unitDirichletRepresentative g) n at hc
  change periodOneCoefficient
    (fun x : ℝ => periodOneSobolevSynthesis f.val (x : AddCircle (2 : ℝ))) n =
      periodOneCoefficient
        (fun x : ℝ => periodOneSobolevSynthesis g.val (x : AddCircle (2 : ℝ))) n at hc
  simpa only [periodOneCoefficient_periodOneSobolevSynthesis] using hc

/-- Every original classical H1 function with zero endpoint values has a unique
coefficient representative in the complete zero-trace domain. -/
theorem existsUnique_unitDirichletRepresentative (f : ℝ → ℂ)
    (hf : HasIntervalH1Regularity f) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    ∃! a : UnitDirichletH1,
      ∀ x ∈ Icc (0 : ℝ) 1, unitDirichletRepresentative a x = f x := by
  have hend : f 1 = wave 0 1 * f 0 := by rw [h0, h1, mul_zero]
  let a := signedSobolevCoefficients 0 f hf hend
  let A := WeightedCoeff.weightEquiv (Weight.sobolev 1) 2 a
  have hA (n : ℤ) : A (2*n) =
      (Weight.sobolev 1 (2*n):ℂ)*((Weight.sobolev 0 n:ℂ)*a.val (2*n)) := by
    simp only [A, WeightedCoeff.weightEquiv_apply, Weight.sobolev_apply, Real.rpow_zero, Real.rpow_one, Complex.ofReal_one, one_mul]
  obtain ⟨b, hb, _⟩ := Coeff.exists_sobolev_even_sample_le A
    (fun n => a.val (2*n)) 0 1 (by norm_num) hA
  have hc : Memℓp (fun n : ℤ => (Weight.sobolev 1 n:ℂ)*a.val (2*n)) 2 := by
    have he : (fun n : ℤ => (Weight.sobolev 1 n:ℂ)*a.val (2*n)) = fun n => b n := by
      funext n
      simpa only [zero_add] using (hb n).symm
    rw [he]
    exact lp.memℓp b
  let c : ScalarDomain 2 := ⟨fun n => a.val (2*n), hc⟩
  have hdouble : Coeff.periodDoubleSobolev c = a := by
    apply Subtype.ext
    funext n
    by_cases hn : n % 2 = 0
    · have he : n = 2*(n/2) := by omega
      rw [he, Coeff.periodDoubleSobolev_apply, Coeff.periodDouble_even, scalarInclusion_apply]
    · have he : n = 2*(n/2)+1 := by omega
      rw [he, Coeff.periodDoubleSobolev_apply, Coeff.periodDouble_odd]
      exact (signedSobolevCoefficients_parity 0 f hf hend _ (by omega)).symm
  have hrec (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      periodOneSobolevSynthesis c (x : AddCircle (2 : ℝ)) = f x := by
    rw [periodOneSobolevSynthesis_eq, hdouble]
    exact (sobolevSynthesis_signedSobolevCoefficients 0 f hf hend
      ⟨hx.1, hx.2.trans (by norm_num)⟩).trans (signedDouble_left _ _ hx.2)
  have htrace : c ∈ unitDirichletSubspace := by
    exact (hrec 0 (by constructor <;> norm_num)).trans h0
  let v : UnitDirichletH1 := ⟨c, htrace⟩
  refine ⟨v, hrec, ?_⟩
  intro w hw
  apply unitDirichletRepresentative_injective_on_interval w v
  intro x hx
  exact (hw x hx).trans (hrec x hx).symm

/-- Every coefficient representative satisfies precisely the classical interval
regularity and both zero endpoint conditions. -/
theorem unitDirichletRepresentative_mem_domain (a : UnitDirichletH1) :
    HasIntervalH1Regularity (unitDirichletRepresentative a) ∧
      unitDirichletRepresentative a 0 = 0 ∧ unitDirichletRepresentative a 1 = 0 :=
  ⟨⟨absolutelyContinuous_unitDirichletRepresentative a,
    memLp_deriv_unitDirichletRepresentative a⟩,
    unitDirichletRepresentative_zero a, unitDirichletRepresentative_one a⟩

end NLS.Fourier
