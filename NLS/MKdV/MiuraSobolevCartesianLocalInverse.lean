import NLS.MKdV.MiuraSobolevCartesianFreeEquivalence
import NLS.ComplexAnalysis.AnalyticNativeInverseNeighborhoods
import NLS.MKdV.MiuraActionFlowGroup

/-! # Full native analytic Cartesian inverse charts at zero on the Sobolev scale

The actual derivative is a bounded equivalence in each pair of native
Sobolev norms. The nonlinear analytic inverse theorem therefore applies
at every integer order, including the original physical H¹ scalar domain.
-/
noncomputable section
open Set Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraSobolevCartesianSequence_zero (s : ℕ) : miuraSobolevCartesianSequence s 0 = 0 := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by intro j; simp
  obtain ⟨U,_,h0U,_,hcoord⟩ := exists_local_miuraSobolevCartesianSequence_analytic s 0 hzero
  have he (n : ℤ) : ((miuraSobolevCartesianSequence s 0).1.val n,(miuraSobolevCartesianSequence s 0).2.val n) = 0 := by
    rw [hcoord 0 h0U n]
    simp only [map_zero,miuraL2CartesianCoefficient,miuraL2CartesianCoordinates_zero,ite_self]
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact congrArg Prod.fst (he n)
  · exact congrArg Prod.snd (he n)

theorem miuraSobolevPositiveCartesianMap_zero (s : ℕ) : miuraSobolevPositiveCartesianMap s 0 = 0 := by
  change (miuraSobolevPositiveProjection s (miuraSobolevCartesianSequence s 0),(0 : ScalarSobolev s).val 0) = 0
  rw [miuraSobolevCartesianSequence_zero,map_zero]
  rfl

/-- Genuine nonlinear inverse neighborhoods in native H^s and h^(s+1/2)
for every integer s>=0, with the literal mean retained. -/
theorem exists_miuraSobolevPositiveCartesian_localInverse_at_zero (s : ℕ) :
    ∃ U : Set (ScalarSobolev s), ∃ V : Set (MiuraPositiveSobolevTarget s),
      IsOpen U ∧ IsOpen V ∧ (0 : ScalarSobolev s) ∈ U ∧ (0 : MiuraPositiveSobolevTarget s) ∈ V ∧
      miuraSobolevPositiveCartesianMap s '' U = V ∧ BijOn (miuraSobolevPositiveCartesianMap s) U V ∧
      ∃ G : MiuraPositiveSobolevTarget s → ScalarSobolev s,
        AnalyticOnNhd ℂ (miuraSobolevPositiveCartesianMap s) U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraSobolevPositiveCartesianMap s a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraSobolevPositiveCartesianMap s (G z) = z) := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by intro j; simp
  exact exists_analytic_inverse_neighborhoods_of_fderiv_equiv
    (analyticAt_miuraSobolevPositiveCartesianMap s 0 hzero) (miuraSobolevCartesianFreeEquiv s)
    (miuraSobolevCartesianFreeJacobian_eq_equiv s) (miuraSobolevPositiveCartesianMap_zero s)

def miuraH1PositiveCartesianMap (a : ScalarDomain 2) : MiuraPositiveSobolevTarget 1 :=
  miuraSobolevPositiveCartesianMap 1 (miuraH1SobolevEquiv a)

def miuraH1CartesianFreeEquiv : ScalarDomain 2 ≃L[ℂ] MiuraPositiveSobolevTarget 1 :=
  miuraH1SobolevEquiv.toContinuousLinearEquiv.trans (miuraSobolevCartesianFreeEquiv 1)

theorem analyticAt_miuraH1PositiveCartesianMap (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) :
    AnalyticAt ℂ miuraH1PositiveCartesianMap a :=
  (analyticAt_miuraSobolevPositiveCartesianMap 1 (miuraH1SobolevEquiv a) (miuraH1SobolevReal a ha)).comp
    (miuraH1SobolevEquiv.toContinuousLinearEquiv.analyticAt a)

theorem fderiv_miuraH1PositiveCartesianMap_zero :
    fderiv ℂ miuraH1PositiveCartesianMap 0 = miuraH1CartesianFreeEquiv.toContinuousLinearMap := by
  have hz : ∀ j : ℤ, (0 : ScalarSobolev 1).val j = conj ((0 : ScalarSobolev 1).val (-j)) := by intro j; simp
  have hd := (analyticAt_miuraSobolevPositiveCartesianMap 1 0 hz).differentiableAt.hasFDerivAt
  change HasFDerivAt _ (miuraSobolevCartesianFreeJacobian 1) 0 at hd
  rw [miuraSobolevCartesianFreeJacobian_eq_equiv] at hd
  have he : HasFDerivAt (miuraSobolevPositiveCartesianMap 1) (miuraSobolevCartesianFreeEquiv 1).toContinuousLinearMap
      (miuraH1SobolevEquiv (0 : ScalarDomain 2)) := by simpa only [map_zero] using! hd
  have hc := he.comp (0 : ScalarDomain 2) miuraH1SobolevEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
  exact hc.fderiv

/-- The original complex H¹ domain itself has an inverse chart in its
full native order-three-halves Cartesian norm, including the signed mean. -/
theorem exists_miuraH1PositiveCartesian_localInverse_at_zero :
    ∃ U : Set (ScalarDomain 2), ∃ V : Set (MiuraPositiveSobolevTarget 1),
      IsOpen U ∧ IsOpen V ∧ (0 : ScalarDomain 2) ∈ U ∧ (0 : MiuraPositiveSobolevTarget 1) ∈ V ∧
      miuraH1PositiveCartesianMap '' U = V ∧ BijOn miuraH1PositiveCartesianMap U V ∧
      ∃ G : MiuraPositiveSobolevTarget 1 → ScalarDomain 2,
        AnalyticOnNhd ℂ miuraH1PositiveCartesianMap U ∧ AnalyticOnNhd ℂ G V ∧ G 0 = 0 ∧
        (∀ a ∈ U, G (miuraH1PositiveCartesianMap a) = a) ∧
        (∀ z ∈ V, G z ∈ U ∧ miuraH1PositiveCartesianMap (G z) = z) := by
  have hzero : ∀ j : ℤ, (0 : ScalarDomain 2).val j = conj ((0 : ScalarDomain 2).val (-j)) := by intro j; simp
  have hm : miuraH1PositiveCartesianMap 0 = 0 := by
    change miuraSobolevPositiveCartesianMap 1 (miuraH1SobolevEquiv 0) = 0
    rw [map_zero,miuraSobolevPositiveCartesianMap_zero]
  exact exists_analytic_inverse_neighborhoods_of_fderiv_equiv
    (analyticAt_miuraH1PositiveCartesianMap 0 hzero) miuraH1CartesianFreeEquiv fderiv_miuraH1PositiveCartesianMap_zero hm

end NLS.MKdV
