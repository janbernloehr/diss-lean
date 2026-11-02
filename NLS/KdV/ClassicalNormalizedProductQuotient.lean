import NLS.KdV.ClassicalCandidateEnergyProducts
import NLS.ComplexAnalysis.FilledSimpleQuotient

/-! # Entire quotient of the actual normalized numerator by its selected product

Every zero of the candidate omitted product is an actual simple Psi_n zero.
The quotient is therefore entire and nonzero at the selected zeros. Its
constancy and exact value are not assumed or asserted here.
-/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def classicalHillNormalizedProductQuotient (N : ℕ)
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) : ℂ → ℂ :=
  filledSimpleQuotient (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2))
    (classicalHillCandidateOmittedProduct N n t)

namespace ClassicalAllContourPeriodData
variable {N : ℕ} {V : Set (NLS.LinearVolterra.Curve ℂ)} {A : ℝ}
variable (D : ClassicalAllContourPeriodData N V A)
include D

theorem normalizedProductQuotient_entire
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (n : ℕ+)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hroots : ∀ k : ℕ+, k ≠ n →
      classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k t,t.2) = 0) :
    AnalyticOnNhd ℂ (classicalHillNormalizedProductQuotient N R n t) univ ∧
    ∀ lambda : ℂ, classicalHillNormalizedProductQuotient N R n t lambda*
      classicalHillCandidateOmittedProduct N n t lambda = classicalHillNormalizedNumerator N R n (lambda,t.2) := by
  have hB := D.candidate_omitted_product n t ht haux
  have hzero (lambda : ℂ) (hz : classicalHillCandidateOmittedProduct N n t lambda = 0) :
      classicalHillNormalizedNumerator N R n (lambda,t.2) = 0 := by
    obtain ⟨k,hkn,hk⟩ := (hB.2.2.1 lambda).mp hz
    rw [← hk]
    exact hroots k hkn
  constructor
  · intro lambda _
    exact analyticAt_filledSimpleQuotient
      (D.normalizedNumerator_entire R hRa n t.2 ht.2 lambda (mem_univ _))
      (hB.1 lambda (mem_univ _)) (fun hz => ⟨hzero lambda hz,hB.2.2.2 lambda hz⟩)
  · intro lambda
    exact filledSimpleQuotient_mul _ _ lambda (hzero lambda)

theorem normalizedProductQuotient_ne_zero_at_selected_root
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)) (n k : ℕ+) (hkn : k ≠ n)
    (t : NLS.Coeff 2 × NLS.LinearVolterra.Curve ℂ) (ht : t ∈ classicalHillCandidateDomain V)
    (haux : ∀ j ≤ (0 : ℤ), t.1 j = 0)
    (hPsi : deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,t.2))
      (classicalHillCandidateEnergy N k t) ≠ 0) :
    classicalHillNormalizedProductQuotient N R n t (classicalHillCandidateEnergy N k t) ≠ 0 := by
  have hB := D.candidate_omitted_product n t ht haux
  have hz := (hB.2.2.1 (classicalHillCandidateEnergy N k t)).mpr ⟨k,hkn,rfl⟩
  exact filledSimpleQuotient_ne_zero_of_simple_zeros _ _ _ hz hPsi (hB.2.2.2 _ hz)

/-- The entire quotient is exactly one on the whole free energy plane,
including the selected zeros where its definition uses derivatives. -/
theorem normalizedProductQuotient_free
    (R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hR0 : R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2)) (n : ℕ+) (lambda : ℂ) :
    classicalHillNormalizedProductQuotient N R n (0,0) lambda = 1 := by
  have ht : ((0 : NLS.Coeff 2),(0 : NLS.LinearVolterra.Curve ℂ)) ∈ classicalHillCandidateDomain V :=
    ⟨Metric.mem_ball_self (by positivity),D.zero_mem⟩
  have hB := D.candidate_omitted_product n (0,0) ht (fun _ _ => rfl)
  have he : (fun z : ℂ => classicalHillNormalizedNumerator N R n (z,0)) =
      classicalHillCandidateOmittedProduct N n (0,0) := by
    funext z
    rw [D.normalizedNumerator_free R hR0,
      D.candidate_omitted_product_zero_displacement n 0 D.zero_mem,D.numerator_free]
  change filledSimpleQuotient (fun z : ℂ => classicalHillNormalizedNumerator N R n (z,0))
    (classicalHillCandidateOmittedProduct N n (0,0)) lambda = 1
  rw [he]
  by_cases hz : classicalHillCandidateOmittedProduct N n (0,0) lambda = 0
  · simp only [filledSimpleQuotient,hz,ite_true,div_self (hB.2.2.2 lambda hz)]
  · simp only [filledSimpleQuotient,if_neg hz,div_self hz]

/-- The actual analytic zero branch supplies an entire product and quotient
on one source neighborhood, simultaneously for every retained root. -/
theorem exists_actual_normalized_product_quotient_family
    (R Q : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2))
    (hRa : AnalyticOnNhd ℂ R V) (hQa : AnalyticOnNhd ℂ Q V) (hQ : ∀ q ∈ V, ‖Q q‖ ≤ 2)
    (hQ0 : Q 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2))
    (hcompat : ∀ q ∈ V, ∀ m j : ℤ,
      NLS.Coeff.positiveIndexWeight m^2*(R q (lp.single 2 j 1)) m =
        NLS.Coeff.positiveIndexWeight j^2*(Q q (lp.single 2 j 1)) m) (n : ℕ+) :
    ∃ U : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
      U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
      (∀ k : ℕ+, AnalyticOnNhd ℂ (fun q => classicalHillCandidateEnergy N k (s q,q)) U) ∧
      (∀ k : ℕ+, classicalHillCandidateEnergy N k (s 0,0) = freeHillEnergy k) ∧
      ∀ q ∈ U, ‖s q‖ < Real.pi/16 ∧
        (∀ j : ℤ, j ≤ 0 ∨ j = (n : ℤ) → s q j = 0) ∧
        AnalyticOnNhd ℂ (classicalHillCandidateOmittedProduct N n (s q,q)) univ ∧
        TendstoLocallyUniformlyOn (fun M z => classicalHillCandidateOmittedPartialProduct N n (s q,q) z M)
          (classicalHillCandidateOmittedProduct N n (s q,q)) atTop univ ∧
        (∀ lambda : ℂ, classicalHillCandidateOmittedProduct N n (s q,q) lambda = 0 ↔
          ∃ k : ℕ+, k ≠ n ∧ classicalHillCandidateEnergy N k (s q,q) = lambda) ∧
        (∀ lambda : ℂ, classicalHillCandidateOmittedProduct N n (s q,q) lambda = 0 →
          deriv (classicalHillCandidateOmittedProduct N n (s q,q)) lambda ≠ 0) ∧
        AnalyticOnNhd ℂ (classicalHillNormalizedProductQuotient N R n (s q,q)) univ ∧
        (∀ lambda : ℂ, classicalHillNormalizedProductQuotient N R n (s q,q) lambda*
          classicalHillCandidateOmittedProduct N n (s q,q) lambda = classicalHillNormalizedNumerator N R n (lambda,q)) ∧
        ∀ k : ℕ+, k ≠ n →
          classicalHillNormalizedNumerator N R n (classicalHillCandidateEnergy N k (s q,q),q) = 0 ∧
          deriv (fun lambda => classicalHillNormalizedNumerator N R n (lambda,q))
            (classicalHillCandidateEnergy N k (s q,q)) ≠ 0 ∧
          classicalHillNormalizedProductQuotient N R n (s q,q) (classicalHillCandidateEnergy N k (s q,q)) ≠ 0 := by
  obtain ⟨U,s,hUV,hU,h0,hs0,hsa,henergy,hfree,hs⟩ :=
    D.exists_actual_simple_normalized_zero_family R Q hRa hQa hQ hQ0 hcompat n
  refine ⟨U,s,hUV,hU,h0,hs0,hsa,henergy,hfree,?_⟩
  intro q hq
  have ht : (s q,q) ∈ classicalHillCandidateDomain V :=
    ⟨by simpa only [Metric.mem_ball,dist_zero_right] using (hs q hq).1,hUV hq⟩
  have haux : ∀ j ≤ (0 : ℤ), s q j = 0 := fun j hj => (hs q hq).2.1 j (Or.inl hj)
  have hroots := (hs q hq).2.2.2
  have hB := D.candidate_omitted_product n (s q,q) ht haux
  have hquo := D.normalizedProductQuotient_entire R hRa n (s q,q) ht haux
    (fun k hkn => (hroots k hkn).1)
  refine ⟨(hs q hq).1,(hs q hq).2.1,hB.1,hB.2.1,hB.2.2.1,hB.2.2.2,hquo.1,hquo.2,?_⟩
  intro k hkn
  exact ⟨(hroots k hkn).1,(hroots k hkn).2,
    D.normalizedProductQuotient_ne_zero_at_selected_root R n k hkn (s q,q) ht haux (hroots k hkn).2⟩

end ClassicalAllContourPeriodData
/-- Actual normalized differentials admit the constructed omitted product
as an entire factor locally near zero. The entire quotient is retained;
its exact constancy and value remain a further proof obligation. -/
theorem exists_classicalHill_local_normalized_product_factorizations :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ R V ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ n k : ℕ+, ∀ q ∈ V,
          (2*(Real.pi : ℂ))⁻¹ * ∮ z in C((Real.pi : ℂ)*(k : ℕ),Real.pi/4),
            classicalHillNormalizedNumerator N R n (z^2,q)/classicalHillContinuedRoot (z^2,q)*(2*z) =
              if n = k then 1 else 0) ∧
        ∀ n : ℕ+, ∃ U : Set (NLS.LinearVolterra.Curve ℂ), ∃ s : NLS.LinearVolterra.Curve ℂ → NLS.Coeff 2,
          U ⊆ V ∧ IsOpen U ∧ 0 ∈ U ∧ s 0 = 0 ∧ AnalyticOnNhd ℂ s U ∧
          ∀ q ∈ U,
            AnalyticOnNhd ℂ (classicalHillCandidateOmittedProduct N n (s q,q)) univ ∧
            TendstoLocallyUniformlyOn (fun M z => classicalHillCandidateOmittedPartialProduct N n (s q,q) z M)
              (classicalHillCandidateOmittedProduct N n (s q,q)) atTop univ ∧
            (∀ lambda : ℂ, classicalHillCandidateOmittedProduct N n (s q,q) lambda = 0 ↔
              ∃ k : ℕ+, k ≠ n ∧ classicalHillCandidateEnergy N k (s q,q) = lambda) ∧
            (∀ lambda : ℂ, classicalHillCandidateOmittedProduct N n (s q,q) lambda = 0 →
              deriv (classicalHillCandidateOmittedProduct N n (s q,q)) lambda ≠ 0) ∧
            AnalyticOnNhd ℂ (classicalHillNormalizedProductQuotient N R n (s q,q)) univ ∧
            (∀ lambda : ℂ, classicalHillNormalizedProductQuotient N R n (s q,q) lambda*
              classicalHillCandidateOmittedProduct N n (s q,q) lambda = classicalHillNormalizedNumerator N R n (lambda,q)) ∧
            ∀ k : ℕ+, k ≠ n →
              classicalHillNormalizedProductQuotient N R n (s q,q) (classicalHillCandidateEnergy N k (s q,q)) ≠ 0 := by
  obtain ⟨N,V,T,R,S,Q,hN,hV,h0V,_,hRa,_,hQa,_,hR0,_,hQ0,hinv,hentry,hcompat,A,D⟩ :=
    exists_classicalHill_twoWeighted_period_inverse
  refine ⟨N,V,R,hN,hV,h0V,hRa,hR0,?_,?_⟩
  · intro n k q hq
    exact D.normalizedNumerator_period n k q hq T R (fun m j => (hentry q hq m j).1) (hinv q hq).1
  intro n
  obtain ⟨U,s,hUV,hU,h0,hs0,hsa,_,_,hs⟩ :=
    D.exists_actual_normalized_product_quotient_family R Q hRa hQa
      (fun q hq => (hinv q hq).2.2.2.2.2) hQ0 hcompat n
  refine ⟨U,s,hUV,hU,h0,hs0,hsa,?_⟩
  intro q hq
  obtain ⟨_,_,hBa,hconv,hzero,hsimple,hqa,hfactor,hroots⟩ := hs q hq
  exact ⟨hBa,hconv,hzero,hsimple,hqa,hfactor,fun k hkn => (hroots k hkn).2.2⟩

end NLS.KdV
