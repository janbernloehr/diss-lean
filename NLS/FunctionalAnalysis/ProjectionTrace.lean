import NLS.FunctionalAnalysis.ProjectionTransport
import NLS.FunctionalAnalysis.FiniteSpectralTrace

/-!
# Analytic traces on varying projection ranges

An analytic finite-rank projection family need not have a fixed range. Local
projection transport conjugates a commuting operator to the reference range,
where boundedness of trace proves analyticity. The intrinsic trace is independent
of this local identification. This applies to the simple boundary spectral
restrictions in Lemma 4.5 as well as higher-dimensional clusters.
-/

noncomputable section
open scoped Topology
namespace NLS.ProjectionTrace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The intrinsic restriction, interpreted as an operator on the projection range. -/
def restriction (P A : E →L[ℂ] E) : P.range →L[ℂ] P.range :=
  ProjectionTransport.compressed P P A

/-- The restriction agrees with the original operator on its invariant range. -/
theorem restriction_apply (P A : E →L[ℂ] E) (hP : IsIdempotentElem P)
    (hA : Commute P A) (x : P.range) : (restriction P A x : E) = A x := by
  have ht := ProjectionTransport.transport_self P hP
  have hu : IsUnit (ProjectionTransport.transport P P) := by rw [ht]; exact isUnit_one
  simpa only [restriction, ht, one_apply_eq_self] using
    ProjectionTransport.transport_compressed_apply P P A hP hP hu hA x

/-- Trace on the actual varying range, independent of any reference projection. -/
def trace (P A : E →L[ℂ] E) : ℂ := LinearMap.trace ℂ P.range (restriction P A).toLinearMap

/-- Invertible projection transport conjugates the local compression to the intrinsic restriction. -/
theorem compressed_conjugate (P Q A : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hu : IsUnit (ProjectionTransport.transport P Q)) (hA : Commute Q A) :
    let e := ProjectionTransport.rangeEquivalence P Q hP hQ hu
    e.toLinearEquiv.conjAlgEquiv ℂ (ProjectionTransport.compressed P Q A).toLinearMap =
      (restriction Q A).toLinearMap := by
  intro e
  have hW (y : P.range) : (e y : E) = ProjectionTransport.transport P Q y :=
    ProjectionTransport.rangeEquivalence_apply P Q hP hQ hu y
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (e (ProjectionTransport.compressed P Q A (e.symm x)) : E) = _
  rw [hW, ProjectionTransport.transport_compressed_apply P Q A hP hQ hu hA,
    ← hW, e.apply_symm_apply]
  exact (restriction_apply Q A hQ hA x).symm

theorem trace_eq_compressed (P Q A : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hu : IsUnit (ProjectionTransport.transport P Q)) (hA : Commute Q A) :
    trace Q A = LinearMap.trace ℂ P.range (ProjectionTransport.compressed P Q A).toLinearMap := by
  unfold trace
  rw [← compressed_conjugate P Q A hP hQ hu hA, LinearMap.trace_map]

/-- On a one-dimensional invariant range, trace is the eigenvalue of any nonzero eigenvector. -/
theorem trace_eq_of_finrank_one (P A : E →L[ℂ] E) (hP : IsIdempotentElem P)
    (hA : Commute P A) [FiniteDimensional ℂ P.range] (hdim : Module.finrank ℂ P.range = 1)
    (z : ℂ) (x : P.range) (hx : x ≠ 0) (he : A x = z • (x : E)) : trace P A = z := by
  let T : Module.End ℂ P.range := (restriction P A).toLinearMap
  have heig : T.HasEigenvalue z := by
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := x)
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hx⟩
    apply Subtype.ext
    change (restriction P A x : E) = z • (x : E)
    rw [restriction_apply P A hP hA x, he]
  have hs : T.charpoly.Splits := IsAlgClosed.splits _
  have hcard : T.charpoly.roots.card = 1 := by
    rw [← hs.natDegree_eq_card_roots, T.charpoly_natDegree, hdim]
  obtain ⟨w, hw⟩ := Multiset.card_eq_one.mp hcard
  have hz : z ∈ T.charpoly.roots := by
    rw [Polynomial.mem_roots T.charpoly_monic.ne_zero, ← Module.End.hasEigenvalue_iff_isRoot_charpoly]
    exact heig
  have hzw : z = w := by simpa only [hw, Multiset.mem_singleton] using hz
  change LinearMap.trace ℂ P.range T = z
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits hs, hw]
  simpa using hzw.symm

variable [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Intrinsic trace is analytic for an analytic commuting finite-rank projection family. -/
theorem analyticAt_trace {P A : X → E →L[ℂ] E} {a : X}
    (hP : AnalyticAt ℂ P a) (hA : AnalyticAt ℂ A a)
    (hp : IsIdempotentElem (P a)) [FiniteDimensional ℂ (P a).range]
    (hnear : ∀ᶠ x in 𝓝 a, IsIdempotentElem (P x) ∧ Commute (P x) (A x)) :
    AnalyticAt ℂ (fun x => trace (P x) (A x)) a := by
  have hu : IsUnit (ProjectionTransport.transport (P a) (P a)) := by
    rw [ProjectionTransport.transport_self _ hp]
    exact isUnit_one
  have ht := FiniteSpectralTrace.analyticAt_trace
    (ProjectionTransport.analyticAt_compressed (P a) hP hA hu)
  apply ht.congr
  filter_upwards [hnear, ProjectionTransport.eventually_isUnit_transport hP hp] with x hx hux
  exact (trace_eq_compressed (P a) (P x) (A x) hp hx.1 hux hx.2).symm

end NLS.ProjectionTrace
