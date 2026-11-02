import NLS.Articles.KdVPseudomeasures.SpectralAnalytic
import NLS.KdV.PseudomeasureSpectrum

/-! # The source's original singular Schrodinger operator and full resolvent

These Appendix C dependencies use the original period-two H-minus-one base
space and entire original H1 domain, exactly as the source defines L(q).
The potential ranges over the full original complex endpoint Banach space,
including its real mean-zero physically period-one source subspace. Global
labels, asymptotic enumeration and algebraic-multiplicity comparison remain
separate proof obligations.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue

/-- An arbitrary original complex endpoint potential, as the identical H-minus-one distribution. -/
def sourceComplexHminusOne (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : FourierLebesgueSpace (2:ℝ) (-1) 2 :=
  endpointLowerInclusion (-r) (-1) (by norm_num) (admissible_hminusOne_threshold r hr) q

theorem sourceComplexHminusOne_val (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : (sourceComplexHminusOne r hr q).val = q.val :=
  endpointLowerInclusion_val (-r) (-1) (by norm_num) (admissible_hminusOne_threshold r hr) q

/-- The complex original-potential inclusion equals the already checked coefficient realization. -/
theorem sourceEndpointCoefficients_HminusOne_complex (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    NLS.KdV.endpointHillHminusOne SpectralWeight.one r hr.2 (sourceEndpointCoefficients r q) =
      sourceComplexHminusOne r hr q := by
  apply Subtype.ext
  rw [sourceEndpointCoefficients_HminusOne_val, sourceComplexHminusOne_val]

/-- On the actual real physical source, the complex inclusion is exactly the original potential inclusion. -/
theorem sourceComplexHminusOne_ofPotential (r : ℝ) (hr : AdmissiblePredualOrder r) (q : Potential r) :
    sourceComplexHminusOne r hr q.val = potentialHminusOne r hr q := rfl

/-- The spectrum of the source unbounded operator on original H-minus-one with original H1 domain. -/
def sourceHillSpectrum (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) : Set ℂ :=
  {z | ¬Function.Bijective (NLS.KdV.singularHillOperator (sourceComplexHminusOne r hr q) -
    z • NLS.KdV.singularHillDomainInclusion)}

/-- No spectral realization changes when passing to the exact source coefficients. -/
theorem sourceHillSpectrum_eq (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    sourceHillSpectrum r hr q = NLS.KdV.endpointHillSpectrum r hr.2 (sourceEndpointCoefficients r q) := by
  ext z
  change (¬Function.Bijective (NLS.KdV.singularHillOperator (sourceComplexHminusOne r hr q) -
    z • NLS.KdV.singularHillDomainInclusion)) ↔ _
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  rfl

/-- Every source spectral point is an actual full-domain physical eigenvalue, globally in lambda. -/
theorem sourceHillSpectrum_mem_iff (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (z : ℂ) :
    z ∈ sourceHillSpectrum r hr q ↔
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        NLS.KdV.singularHillOperator (sourceComplexHminusOne r hr q) f =
          z • NLS.KdV.singularHillDomainInclusion f := by
  rw [sourceHillSpectrum_eq, ← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact NLS.KdV.mem_endpointHillSpectrum_iff r hr.1 hr.2 (sourceEndpointCoefficients r q) z

/-- The original partial operator is closed on its unchanged physical H1 domain. -/
theorem source_singularHill_closed (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    (NLS.KdV.singularHillPartialOperator (sourceComplexHminusOne r hr q)).IsClosed := by
  rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
  exact NLS.KdV.isClosed_endpointHillPartialOperator r hr.1 hr.2 (sourceEndpointCoefficients r q)

/-- The original physical operator has a bounded inverse into H1 and a compact inverse on H-minus-one. -/
theorem source_singularHill_compact_resolvent (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) :
    ∃ a : ℂ, ∃ B : FourierLebesgueSpace (2:ℝ) (-1) 2 →L[ℂ] FourierLebesgueSpace (2:ℝ) 1 2,
      (∀ f : FourierLebesgueSpace (2:ℝ) 1 2,
        B (NLS.KdV.singularHillOperator (sourceComplexHminusOne r hr q) f -
          a • NLS.KdV.singularHillDomainInclusion f) = f) ∧
      (∀ g : FourierLebesgueSpace (2:ℝ) (-1) 2,
        NLS.KdV.singularHillOperator (sourceComplexHminusOne r hr q) (B g) -
          a • NLS.KdV.singularHillDomainInclusion (B g) = g) ∧
      IsCompactOperator (NLS.KdV.singularHillDomainInclusion.comp B) := by
  obtain ⟨a,ha⟩ := NLS.KdV.endpointHillResolventSet_nonempty r hr.1 hr.2 (sourceEndpointCoefficients r q)
  refine ⟨a, NLS.KdV.endpointHillResolventToH1 r hr.2 (sourceEndpointCoefficients r q) a, ?_, ?_, ?_⟩
  · intro f
    rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
    exact NLS.KdV.endpointHillResolventToH1_left r hr.2 (sourceEndpointCoefficients r q) a ha f
  · intro g
    rw [← sourceEndpointCoefficients_HminusOne_complex r hr q]
    exact NLS.KdV.endpointHillResolventToH1_right r hr.2 (sourceEndpointCoefficients r q) a ha g
  · exact NLS.KdV.isCompactOperator_endpointHillBaseResolvent r hr.2 (sourceEndpointCoefficients r q) a

/-- The source singular spectrum has only finitely many points in every bounded complex region. -/
theorem sourceHillSpectrum_finite_norm_le (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (R : ℝ) :
    Set.Finite {z : ℂ | z ∈ sourceHillSpectrum r hr q ∧ ‖z‖ ≤ R} := by
  rw [sourceHillSpectrum_eq]
  exact NLS.KdV.finite_endpointHillSpectrum_norm_le r hr.1 hr.2 (sourceEndpointCoefficients r q) R

/-- The actual determinant detects full physical pencil invertibility, uniformly on original complex norm balls. -/
theorem source_uniform_full_resolvent_criterion (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) ⊤, ‖q‖ ≤ R →
      ∀ n : ℕ, N ≤ n → ∀ z ∈ NLS.KdV.reducedHillStrip n,
        (z ∈ sourceHillSpectrum r hr q ↔ sourceEndpointDeterminant r hr n (q,z) = 0) := by
  obtain ⟨N,hN,hcut⟩ := NLS.KdV.exists_endpointHill_cutoff r hr.2 R
  refine ⟨N,hN,?_⟩
  intro q hq n hnN z hz
  have hs : NLS.KdV.endpointHillConstant r*(n:ℝ)^(r-1/2)*‖sourceEndpointCoefficients r q‖ ≤ 1/2 := by
    rw [norm_sourceEndpointCoefficients]
    exact (mul_le_mul_of_nonneg_left hq (mul_nonneg (NLS.KdV.endpointHillConstant_pos r hr.2).le
      (Real.rpow_nonneg (by positivity) _))).trans (hcut n hnN)
  rw [sourceHillSpectrum_eq]
  exact NLS.KdV.mem_endpointHillSpectrum_iff_determinant r hr.1 hr.2 n (hN.trans hnN) z hz
    (sourceEndpointCoefficients r q) hs

end NLS.Articles.KdVPseudomeasures
