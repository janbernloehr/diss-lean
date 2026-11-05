import NLS.MKdV.MiuraActionCotangentIndependence
import NLS.FunctionalAnalysis.FiniteCotangentProjection

/-! # Actual finite physical action projections on the original H1 space

At any real H1 source, retain an arbitrary finite collection of its open
physical actions together with the literal mean. Their analytic complex
extensions have a surjective actual Frechet derivative. A bounded linear
right inverse is constructed from this proved surjectivity.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

abbrev MiuraOpenActionIndex (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :=
  {n : ℕ // 1 ≤ n ∧ miuraMKdVAction a ha n ≠ 0}

def miuraFiniteActionCoordinates (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha))
    (b : ScalarDomain 2) : Option S → ℂ := fun i =>
  match i with
  | none => b.val 0
  | some n => miuraL2Action n.val.val (scalarInclusion b)

def miuraFiniteActionRows (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    Option S → ScalarDomain 2 →L[ℂ] ℂ := fun i =>
  match i with
  | none => WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0
  | some n => fderiv ℂ (fun b : ScalarDomain 2 => miuraL2Action n.val.val (scalarInclusion b)) a

theorem analyticAt_miuraFiniteActionCoordinates (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    AnalyticAt ℂ (miuraFiniteActionCoordinates a ha S) a := by
  apply AnalyticAt.pi
  intro i
  cases i with
  | none => exact (WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0).analyticAt a
  | some n =>
    have hmem := real_mem_miuraL2ActionDomain (scalarInclusion a)
      (by intro j; simpa only [scalarInclusion_apply] using ha j)
    exact ((analyticOnNhd_miuraL2Action n.val.val n.val.property.1) _ hmem).comp
      (scalarInclusion.analyticAt a)

theorem hasFDerivAt_miuraFiniteActionCoordinates (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    HasFDerivAt (miuraFiniteActionCoordinates a ha S)
      (ContinuousLinearMap.pi (miuraFiniteActionRows a ha S)) a := by
  apply hasFDerivAt_pi.mpr
  intro i
  cases i with
  | none => exact (WeightedCoeff.evalCLM (Weight.sobolev 1) 2 0).hasFDerivAt
  | some n =>
    have hmem := real_mem_miuraL2ActionDomain (scalarInclusion a)
      (by intro j; simpa only [scalarInclusion_apply] using ha j)
    have hd := (((analyticOnNhd_miuraL2Action n.val.val n.val.property.1) _ hmem).differentiableAt.hasFDerivAt.comp a
      scalarInclusion.hasFDerivAt)
    rw [← fderiv_miuraL2Action_H1 a ha n.val.val n.val.property.1] at hd
    exact hd

theorem surjective_miuraFiniteActionDerivative (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    Function.Surjective (fderiv ℂ (miuraFiniteActionCoordinates a ha S) a) := by
  classical
  rw [(hasFDerivAt_miuraFiniteActionCoordinates a ha S).fderiv]
  apply NLS.FunctionalAnalysis.surjective_pi_of_cotangent_independent
  intro c hz
  let d : MiuraOpenActionIndex a ha → ℂ := fun n =>
    if hn : n ∈ S then c (some ⟨n,hn⟩) else 0
  have hs : (∑ n ∈ S, d n • fderiv ℂ (fun b : ScalarDomain 2 => miuraL2Action n.val (scalarInclusion b)) a) =
      ∑ n : S, c (some n) • fderiv ℂ (fun b : ScalarDomain 2 => miuraL2Action n.val.val (scalarInclusion b)) a := by
    rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro n _
    simp only [d,dif_pos n.property]
  have hu := miuraH1ActionCotangent_coefficients_unique a ha S d (c none) (by
    rw [hs]
    simpa only [Fintype.sum_option,miuraFiniteActionRows] using hz)
  funext i
  cases i with
  | none => exact hu.1
  | some n =>
    have h := hu.2 n.val n.property
    simpa only [d,dif_pos n.property,Pi.zero_apply] using! h

theorem exists_miuraFiniteActionDerivative_rightInverse (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (S : Finset (MiuraOpenActionIndex a ha)) :
    ∃ R : (Option S → ℂ) →L[ℂ] ScalarDomain 2,
      (fderiv ℂ (miuraFiniteActionCoordinates a ha S) a).comp R =
        ContinuousLinearMap.id ℂ (Option S → ℂ) :=
  NLS.FunctionalAnalysis.exists_continuousLinear_rightInverse_of_surjective _
    (surjective_miuraFiniteActionDerivative a ha S)

end NLS.MKdV
