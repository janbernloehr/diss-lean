import NLS.SequenceSpaces.WeightedFiniteCoefficients
import NLS.ZakharovShabat.SourceLemma4_3
import NLS.SequenceSpaces.SobolevEmbedding
import NLS.Fourier.PeriodicFourierLebesgueSpace

/-! # Smooth input can lose one derivative under interval reflection

The paragraph before Lemma 4.3 warns that even a smooth period-one
potential need not have a one-derivative reflected extension. The actual
constant input (0,1) proves this for both boundary signs and every finite
Banach exponent. Its weighted second-component coefficients belong to
the infinity space, which is kept separate from the finite-exponent claim.
-/
noncomputable section
open NLS.Fourier
open scoped ENNReal SchwartzMap ContDiff
namespace NLS.Fourier

/-- A one-derivative reciprocal odd tail cannot lie in any finite Banach exponent. -/
theorem not_memlp_overlap_zero_sobolev_one {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    ¬Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*overlap 0 n) p := by
  intro h
  let a : WeightedCoeff (Weight.sobolev 1) p := ⟨overlap 0,h⟩
  have hm : Memℓp (fun n => WeightedCoeff.sobolevToL1CLM p hp a n) 1 :=
    (WeightedCoeff.sobolevToL1CLM p hp a).property
  apply not_memlp_overlap_zero_one
  simpa only [WeightedCoeff.sobolevToL1CLM_apply] using hm

/-- At infinity the same weighted coefficients are bounded. -/
theorem memlp_overlap_zero_sobolev_one_top :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*overlap 0 n) ⊤ := by
  apply memℓp_infty
  refine ⟨2,?_⟩
  rintro _ ⟨n,rfl⟩
  change ‖(Weight.sobolev 1 n : ℂ)*overlap 0 n‖ ≤ 2
  rw [norm_mul]
  have hw : ‖(Weight.sobolev 1 n : ℂ)‖ = 1+|(n : ℝ)| := by
    rw [Weight.sobolev_apply,Real.rpow_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1+|(n : ℝ)|)]
  rw [hw]
  calc
    _ ≤ (1+|(n : ℝ)|)*(2*(1+|(n : ℝ)|)⁻¹) :=
      mul_le_mul_of_nonneg_left (norm_overlap_zero_le n) (by positivity)
    _ = 2 := by field_simp

/-- The exact Banach-exponent range at Sobolev order one. -/
theorem memlp_overlap_zero_sobolev_one_iff {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*overlap 0 n) p ↔ p = ⊤ := by
  constructor
  · intro h
    by_contra hp
    exact not_memlp_overlap_zero_sobolev_one hp h
  · rintro rfl
    exact memlp_overlap_zero_sobolev_one_top

end NLS.Fourier
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical example is smooth and period one before reflection. -/
theorem reflection_oneSided_source_regular :
    ContDiff ℝ ∞ (fun _ : ℝ => ((0 : ℂ),(1 : ℂ))) ∧
      Function.Periodic (fun _ : ℝ => ((0 : ℂ),(1 : ℂ))) 1 :=
  ⟨contDiff_const,fun _ => rfl⟩

/-- Actual normalized Fourier integrals detect the loss of one derivative. -/
theorem intervalExtension_oneSided_sobolev_one_iff (b : BoundaryCondition) :
    Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*periodTwoCoefficient
      (fun x => (intervalExtension b (fun _ => ((0 : ℂ),1)) x).2) n) p ↔ p = ⊤ := by
  simp only [intervalExtension_coefficient_snd b _ continuous_const,
    intervalAmplitude_oneSided,memlp_overlap_zero_sobolev_one_iff]

/-- No original one-derivative pair has the Fourier coefficients of the reflected smooth input. -/
theorem intervalExtension_oneSided_no_oneDerivative_pair (b : BoundaryCondition) (hp : p ≠ ⊤) :
    ¬∃ a : WeightedCoeffPair (Weight.sobolev 1) p,
      ∀ n : ℤ, a.fst.val n = periodTwoCoefficient
          (fun x => (intervalExtension b (fun _ => ((0 : ℂ),1)) x).1) n ∧
        a.snd.val n = periodTwoCoefficient
          (fun x => (intervalExtension b (fun _ => ((0 : ℂ),1)) x).2) n := by
  rintro ⟨a,ha⟩
  apply hp
  apply (intervalExtension_oneSided_sobolev_one_iff b).mp
  have hm : Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*a.snd.val n) p := a.snd.property
  simpa only [← fun n => (ha n).2] using hm

/-- The original finite coefficient input for the physical constant (0,1). -/
def sourceReflectionConstantInput (p : ℝ≥0∞) [Fact (1 ≤ p)] : CoeffPair p :=
  (CoeffPair.toMax p).symm (finitePairCoeffs (0,Finsupp.single 0 1))

/-- Before reflection the original input belongs to every real Sobolev order. -/
theorem sourceReflectionConstantInput_has_all_orders (s : ℝ) :
    ∃ a : WeightedCoeffPair (Weight.sobolev s) p, ∀ n : ℤ,
      a.fst.val n = (sourceReflectionConstantInput p).fst n ∧
      a.snd.val n = (sourceReflectionConstantInput p).snd n := by
  refine ⟨(WeightedCoeffPair.toMax (Weight.sobolev s) p).symm
    (WeightedCoeff.ofFinsupp (Weight.sobolev s) p 0,
      WeightedCoeff.ofFinsupp (Weight.sobolev s) p (Finsupp.single 0 1)),?_⟩
  intro n
  exact ⟨rfl,rfl⟩

/-- The finite polynomial is literally the constant physical potential. -/
theorem sourceReflectionConstantInput_physical :
    BoundaryCondition.periodOnePair (0,Finsupp.single 0 1) =
      (fun _ : ℝ => ((0 : ℂ),1)) := by
  funext x
  simp [BoundaryCondition.periodOnePair,polynomial]

/-- The completed extension retains this exact physical kernel at every strict finite exponent. -/
theorem sourceReflectionConstantInput_amplitude (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (n : ℤ) :
    sourceIntervalAmplitudeCLM b hp1 hp (sourceReflectionConstantInput p) n = overlap 0 n := by
  rw [sourceReflectionConstantInput,sourceIntervalAmplitudeCLM_finite,
    sourceReflectionConstantInput_physical,intervalAmplitude_oneSided]

/-- The bounded order-zero map from Lemma 4.3 does not preserve one derivative. -/
theorem sourceIntervalExtension_oneSided_not_oneDerivative (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ¬Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*
      (sourceIntervalExtensionToBoundary b hp1 hp (sourceReflectionConstantInput p)).val.snd.val n) p := by
  simpa only [sourceIntervalExtensionToBoundary_snd,sourceReflectionConstantInput_amplitude] using
    not_memlp_overlap_zero_sobolev_one hp

/-- The actual smooth-test distribution of the completed extension has the same normalized coefficients. -/
theorem sourceReflectionConstantDistribution_coefficient (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (n : ℤ) :
    (SmoothPeriodicTest.Distribution.ofTempered
      (sourceIntervalExtensionDistributionCLM b hp1 hp (sourceReflectionConstantInput p)).2)
        (SmoothPeriodicTest.mode (L := (2 : ℝ)) (-n)) = overlap 0 n := by
  rw [SmoothPeriodicTest.Distribution.ofTempered_coefficient _
    (sourceIntervalExtensionDistribution_periodic b hp1 hp _).2,periodCoefficientTest_two]
  exact (congrArg Prod.snd (sourceIntervalExtensionDistribution_coefficients b hp1 hp
    (sourceReflectionConstantInput p) n)).trans (sourceReflectionConstantInput_amplitude b hp1 hp n)

/-- The regularity obstruction holds in the original smooth-test distribution space itself. -/
theorem sourceReflectionConstantDistribution_sobolev_one_iff (b : BoundaryCondition)
    (hp1 : 1 < p) (hp : p ≠ ⊤) (q : ℝ≥0∞) [Fact (1 ≤ q)] :
    SmoothPeriodicTest.Distribution.ofTempered
      (sourceIntervalExtensionDistributionCLM b hp1 hp (sourceReflectionConstantInput p)).2 ∈
        periodicFourierLebesgueSubmodule (L := (2 : ℝ)) (Weight.sobolev 1) q ↔ q = ⊤ := by
  change Memℓp (fun n => (Weight.sobolev 1 n : ℂ)*_) q ↔ q = ⊤
  simp only [sourceReflectionConstantDistribution_coefficient,memlp_overlap_zero_sobolev_one_iff]

end NLS.ZakharovShabat
