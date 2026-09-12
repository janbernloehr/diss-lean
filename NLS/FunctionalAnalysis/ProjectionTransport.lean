import NLS.FunctionalAnalysis.ProjectionRank
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Analytic transport between projection ranges

For projections `P` and `Q`, the map `QP + (1-Q)(1-P)` intertwines them and
is the identity when `Q=P`. Invertibility therefore persists near `P` and
both the transport and its inverse vary analytically. This supplies the local
identifications of spectral subspaces used in Lemma 3.7, printed page 27.
-/

noncomputable section
open scoped Topology

namespace NLS.ProjectionTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Transport between a reference projection and a varying projection. -/
def transport (P Q : E →L[ℂ] E) : E →L[ℂ] E := Q * P + (1 - Q) * (1 - P)

/-- Transport is the identity at the reference projection. -/
theorem transport_self (P : E →L[ℂ] E) (hP : IsIdempotentElem P) : transport P P = 1 := by
  change P * P + (1 - P) * (1 - P) = 1
  rw [hP, hP.one_sub]
  abel

theorem projection_mul_transport (P Q : E →L[ℂ] E) (hQ : IsIdempotentElem Q) :
    Q * transport P Q = Q * P := by
  have hz : Q * (1 - Q) = 0 := by rw [mul_sub, mul_one, hQ, sub_self]
  rw [transport, mul_add, ← mul_assoc, hQ, ← mul_assoc, hz, zero_mul, add_zero]

theorem transport_mul_projection (P Q : E →L[ℂ] E) (hP : IsIdempotentElem P) :
    transport P Q * P = Q * P := by
  have hz : (1 - P) * P = 0 := by rw [sub_mul, one_mul, hP, sub_self]
  rw [transport, add_mul, mul_assoc, hP, mul_assoc, hz, mul_zero, add_zero]

/-- The transport intertwines the two projections on the whole Banach space. -/
theorem projection_transport (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) :
    Q * transport P Q = transport P Q * P := by
  rw [projection_mul_transport P Q hQ, transport_mul_projection P Q hP]

/-- Invertible transport conjugates the reference projection to the new one. -/
theorem conjugate_projection (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hu : IsUnit (transport P Q)) :
    transport P Q * P * Ring.inverse (transport P Q) = Q := by
  rw [← projection_transport P Q hP hQ, mul_assoc,
    Ring.mul_inverse_cancel _ hu, mul_one]

/-- The inverse intertwines in the reverse direction. -/
theorem inverse_projection (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hu : IsUnit (transport P Q)) :
    P * Ring.inverse (transport P Q) = Ring.inverse (transport P Q) * Q := by
  calc
    _ = Ring.inverse (transport P Q) *
        (transport P Q * P * Ring.inverse (transport P Q)) := by
      rw [← mul_assoc, ← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
    _ = _ := by rw [conjugate_projection P Q hP hQ hu]

/-- An invertible transport as a continuous linear equivalence on the ambient space. -/
def equivalence (P Q : E →L[ℂ] E) (hu : IsUnit (transport P Q)) : E ≃L[ℂ] E :=
  ContinuousLinearEquiv.ofUnit hu.unit

@[simp] theorem equivalence_apply (P Q : E →L[ℂ] E) (hu : IsUnit (transport P Q)) (x : E) :
    equivalence P Q hu x = transport P Q x := by
  change hu.unit.val x = transport P Q x
  rw [hu.unit_spec]

@[simp] theorem equivalence_symm_apply (P Q : E →L[ℂ] E)
    (hu : IsUnit (transport P Q)) (x : E) :
    (equivalence P Q hu).symm x = Ring.inverse (transport P Q) x := by
  change (↑hu.unit⁻¹ : E →L[ℂ] E) x = Ring.inverse (transport P Q) x
  have hi : Ring.inverse (transport P Q) = (↑hu.unit⁻¹ : E →L[ℂ] E) := by
    simpa only [hu.unit_spec] using Ring.inverse_unit hu.unit
  exact congrArg (fun A : E →L[ℂ] E => A x) hi.symm

/-- The ambient equivalence maps the entire reference range onto the new range. -/
theorem map_range (P Q : E →L[ℂ] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hu : IsUnit (transport P Q)) :
    P.range.map (equivalence P Q hu).toLinearMap = Q.range := by
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv⟩, rfl⟩
    change P v = x at hv
    refine ⟨transport P Q v, ?_⟩
    change Q (transport P Q v) = equivalence P Q hu x
    rw [equivalence_apply, ← hv]
    exact congrArg (fun A : E →L[ℂ] E => A v) (projection_transport P Q hP hQ)
  · rintro ⟨v, hv⟩
    change Q v = y at hv
    refine ⟨(equivalence P Q hu).symm y, ?_, (equivalence P Q hu).apply_symm_apply y⟩
    refine ⟨Ring.inverse (transport P Q) v, ?_⟩
    change P (Ring.inverse (transport P Q) v) = (equivalence P Q hu).symm y
    rw [equivalence_symm_apply, ← hv]
    exact congrArg (fun A : E →L[ℂ] E => A v) (inverse_projection P Q hP hQ hu)

/-- Continuous linear identification of the two projection ranges. -/
def rangeEquivalence (P Q : E →L[ℂ] E) (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q)
    (hu : IsUnit (transport P Q)) : P.range ≃L[ℂ] Q.range :=
  (equivalence P Q hu).ofSubmodules P.range Q.range (map_range P Q hP hQ hu)

@[simp] theorem rangeEquivalence_apply (P Q : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hu : IsUnit (transport P Q))
    (x : P.range) : (rangeEquivalence P Q hP hQ hu x : E) = transport P Q x := by
  change equivalence P Q hu x = _
  exact equivalence_apply P Q hu x

/-- Compression onto a fixed range as a bounded linear operation on operators. -/
def compressionMap (P : E →L[ℂ] E) :
    (E →L[ℂ] E) →L[ℂ] (P.range →L[ℂ] P.range) :=
  ((ContinuousLinearMap.compL ℂ P.range E P.range).flip P.range.subtypeL).comp
    ((ContinuousLinearMap.compL ℂ E E P.range) P.rangeRestrict)

/-- An operator on the varying range, expressed on the fixed reference range.
This total definition has its similarity interpretation when transport is invertible. -/
def compressed (P Q A : E →L[ℂ] E) : P.range →L[ℂ] P.range :=
  compressionMap P (Ring.inverse (transport P Q) * A * transport P Q)

@[simp] theorem compressed_apply (P Q A : E →L[ℂ] E) (x : P.range) :
    (compressed P Q A x : E) = P (Ring.inverse (transport P Q) (A (transport P Q x))) := rfl

/-- For an operator commuting with the varying projection, compression is the
actual transported operator, with no loss from the final reference projection. -/
theorem transport_compressed_apply (P Q A : E →L[ℂ] E)
    (hP : IsIdempotentElem P) (hQ : IsIdempotentElem Q) (hu : IsUnit (transport P Q))
    (hA : Commute Q A) (x : P.range) :
    transport P Q (compressed P Q A x) = A (transport P Q x) := by
  have hPx : P x = x := by
    obtain ⟨v, hv⟩ := x.property
    change P v = (x : E) at hv
    have hh := congrArg (fun B : E →L[ℂ] E => B v) hP
    change P (P v) = P v at hh
    simpa only [hv] using hh
  have hQx : Q (transport P Q x) = transport P Q x := by
    have hh := congrArg (fun B : E →L[ℂ] E => B x) (projection_transport P Q hP hQ)
    change Q (transport P Q x) = transport P Q (P x) at hh
    simpa only [hPx] using hh
  have hy : Q (A (transport P Q x)) = A (transport P Q x) := by
    have hh := congrArg (fun B : E →L[ℂ] E => B (transport P Q x)) hA.eq
    change Q (A (transport P Q x)) = A (Q (transport P Q x)) at hh
    simpa only [hQx] using hh
  rw [compressed_apply]
  have hh := congrArg (fun B : E →L[ℂ] E => B (A (transport P Q x)))
    (inverse_projection P Q hP hQ hu)
  change P (Ring.inverse (transport P Q) (A (transport P Q x))) =
    Ring.inverse (transport P Q) (Q (A (transport P Q x))) at hh
  rw [hh, hy]
  exact congrArg (fun B : E →L[ℂ] E => B (A (transport P Q x)))
    (Ring.mul_inverse_cancel _ hu)

variable [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

omit [CompleteSpace E] in
/-- Transport depends analytically on any analytic family of bounded operators. -/
theorem analyticAt_transport (P : E →L[ℂ] E) {Q : X → E →L[ℂ] E} {a : X}
    (ha : AnalyticAt ℂ Q a) : AnalyticAt ℂ (fun x => transport P (Q x)) a :=
  (ha.mul analyticAt_const).add ((analyticAt_const.sub ha).mul analyticAt_const)

/-- Its inverse is analytic wherever the transport is invertible. -/
theorem analyticAt_inverse_transport (P : E →L[ℂ] E) {Q : X → E →L[ℂ] E} {a : X}
    (ha : AnalyticAt ℂ Q a) (hu : IsUnit (transport P (Q a))) :
    AnalyticAt ℂ (fun x => Ring.inverse (transport P (Q x))) a :=
  (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp
    (f := fun x : X => transport P (Q x)) (analyticAt_transport P ha)

/-- Every analytic projection family admits local invertible analytic transport. -/
theorem eventually_isUnit_transport {Q : X → E →L[ℂ] E} {a : X}
    (ha : AnalyticAt ℂ Q a) (hP : IsIdempotentElem (Q a)) :
    ∀ᶠ x in 𝓝 a, IsUnit (transport (Q a) (Q x)) := by
  have hunit : IsUnit (transport (Q a) (Q a)) := by rw [transport_self _ hP]; exact isUnit_one
  exact (analyticAt_transport (Q a) ha).continuousAt.preimage_mem_nhds
    (Units.isOpen.mem_nhds hunit)

/-- Analytic operator families become analytic endomorphisms of the fixed range. -/
theorem analyticAt_compressed (P : E →L[ℂ] E) {Q A : X → E →L[ℂ] E} {a : X}
    (hQ : AnalyticAt ℂ Q a) (hA : AnalyticAt ℂ A a) (hu : IsUnit (transport P (Q a))) :
    AnalyticAt ℂ (fun x => compressed P (Q x) (A x)) a := by
  have hB : AnalyticAt ℂ (fun x : X =>
      Ring.inverse (transport P (Q x)) * A x * transport P (Q x)) a :=
    ((analyticAt_inverse_transport P hQ hu).mul hA).mul (analyticAt_transport P hQ)
  have hC : AnalyticAt ℂ (fun B : E →L[ℂ] E => compressionMap P B)
      (Ring.inverse (transport P (Q a)) * A a * transport P (Q a)) :=
    ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := E →L[ℂ] E)
      (F := P.range →L[ℂ] P.range) (compressionMap P) _
  exact hC.comp (f := fun x : X =>
    Ring.inverse (transport P (Q x)) * A x * transport P (Q x)) hB

end NLS.ProjectionTransport
