import NLS.KdV.HillIntegerSobolev
import NLS.KdV.HillHierarchyPhaseModel

/-! # Continuous physical lower Hamiltonians and the source trace coefficient on each sharp Sobolev domain. -/

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory NLS.Fourier NLS.ZakharovShabat Filter Topology
open scoped ContDiff
namespace NLS.KdV

def hillScalarSobolevLower (M j : ℕ) (hj : j ≤ M) : ScalarSobolev M →L[ℂ] ScalarSobolev j :=
  WeightedCoeff.sobolevInclusion (show (j : ℝ) ≤ M by exact_mod_cast hj)

@[simp] theorem hillScalarSobolevLower_apply (M j : ℕ) (hj : j ≤ M)
    (a : ScalarSobolev M) (k : ℤ) : (hillScalarSobolevLower M j hj a).val k = a.val k :=
  WeightedCoeff.sobolevInclusion_apply _ _ _

def hillSobolevHamiltonianAt (M j : ℕ) (hj : j ≤ M) (a : ScalarSobolev M) : ℂ :=
  if hz : j = 0 then (1/2 : ℂ)*sobolevOddKinetic 0
    (hillScalarSobolevLower M 0 (Nat.zero_le M) a, hillScalarSobolevLower M 0 (Nat.zero_le M) a)
  else hillSobolevHamiltonian j (by omega) (hillScalarSobolevLower M j hj a)

theorem continuous_hillSobolevHamiltonianAt (M j : ℕ) (hj : j ≤ M) :
    Continuous (hillSobolevHamiltonianAt M j hj) := by
  unfold hillSobolevHamiltonianAt
  by_cases hz : j = 0
  · have hk : Continuous (sobolevOddKinetic 0) :=
      continuous_iff_continuousAt.mpr (fun a => (analyticAt_sobolevOddKinetic 0 a).continuousAt)
    have hc := (hillScalarSobolevLower M 0 (Nat.zero_le M)).continuous
    simp only [dif_pos hz]
    exact continuous_const.mul (hk.comp (hc.prodMk hc))
  · simp only [dif_neg hz]
    exact (continuous_hillSobolevHamiltonian j (by omega)).comp (hillScalarSobolevLower M j hj).continuous

theorem hillSobolevHamiltonianAt_eq_classical (M j : ℕ) (hj : j ≤ M) (a : ScalarSobolev M)
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (ha : ∀ k, a.val k = periodOneCoefficient q k) :
    hillSobolevHamiltonianAt M j hj a = classicalKdVHierarchyHamiltonian q j := by
  by_cases hz : j = 0
  · subst j
    rw [hillSobolevHamiltonianAt, dif_pos rfl, classicalKdVHierarchyHamiltonian_zero q hq hp,
      classicalQuadraticInvariant]
    have hcoeff (k : ℤ) : (hillScalarSobolevLower M 0 (Nat.zero_le M) a).val k =
        periodOneCoefficient q k := by rw [hillScalarSobolevLower_apply, ha]
    have he := sobolevOddKinetic_eq_integral 0
      (hillScalarSobolevLower M 0 (Nat.zero_le M) a, hillScalarSobolevLower M 0 (Nat.zero_le M) a)
      q q hq hq hp hp hcoeff hcoeff
    simp only [iteratedDeriv_zero] at he
    rw [he]
    simp only [pow_two]
  · rw [hillSobolevHamiltonianAt, dif_neg hz]
    exact hillSobolevHamiltonian_eq_classical j (by omega) _ q hq hp
      (fun k => by rw [hillScalarSobolevLower_apply, ha])

def hillSobolevHamiltonianFamily (M : ℕ) (a : ScalarSobolev M) (j : ℕ) : ℂ :=
  if hj : j ≤ M then hillSobolevHamiltonianAt M j hj a else 0

theorem continuous_hillSobolevHamiltonianFamily (M j : ℕ) :
    Continuous (fun a => hillSobolevHamiltonianFamily M a j) := by
  by_cases hj : j ≤ M
  · simpa only [hillSobolevHamiltonianFamily, dif_pos hj] using continuous_hillSobolevHamiltonianAt M j hj
  · simp only [hillSobolevHamiltonianFamily, dif_neg hj]
    exact continuous_const

theorem hillHierarchyTraceCoefficient_congr_below (H G : ℕ → ℂ) (m : ℕ)
    (h : ∀ j, j ≤ m → H j = G j) : hillHierarchyTraceCoefficient H m = hillHierarchyTraceCoefficient G m := by
  unfold hillHierarchyTraceCoefficient
  rw [h m le_rfl]
  by_cases hm : 2 ≤ m
  · simp only [if_pos hm]
    congr 2
    apply Finset.sum_congr rfl
    intro ij hij
    have he := Finset.mem_antidiagonal.mp hij
    rw [h ij.1 (by omega), h ij.2 (by omega)]
  · simp only [if_neg hm]

theorem continuous_hillHierarchyTraceCoefficient {X : Type*} [TopologicalSpace X]
    (H : ℕ → X → ℂ) (hH : ∀ j, Continuous (H j)) (m : ℕ) :
    Continuous (fun a => hillHierarchyTraceCoefficient (fun j => H j a) m) := by
  unfold hillHierarchyTraceCoefficient
  by_cases hm : 2 ≤ m
  · simp only [if_pos hm]
    exact ((hH m).div_const _).sub (continuous_const.mul
      (continuous_finsetSum _ (fun ij _ => (hH ij.1).mul (hH ij.2))))
  · simp only [if_neg hm]
    exact ((hH m).div_const _).sub (continuous_const.mul continuous_const)

def hillSobolevTraceValue (M m : ℕ) (a : ScalarSobolev M) : ℂ :=
  hillHierarchyTraceCoefficient (hillSobolevHamiltonianFamily M a) m

theorem continuous_hillSobolevTraceValue (M m : ℕ) : Continuous (hillSobolevTraceValue M m) :=
  continuous_hillHierarchyTraceCoefficient (fun j a => hillSobolevHamiltonianFamily M a j)
    (continuous_hillSobolevHamiltonianFamily M) m

theorem hillSobolevTraceValue_eq_classical (M m : ℕ) (hm : m ≤ M) (a : ScalarSobolev M)
    (q : ℝ → ℂ) (hq : ContDiff ℝ ∞ q) (hp : Function.Periodic q 1)
    (ha : ∀ k, a.val k = periodOneCoefficient q k) :
    hillSobolevTraceValue M m a = hillClassicalHierarchyTraceValue q m := by
  apply hillHierarchyTraceCoefficient_congr_below
  intro j hj
  have hjM : j ≤ M := le_trans hj hm
  rw [hillSobolevHamiltonianFamily, dif_pos hjM]
  exact hillSobolevHamiltonianAt_eq_classical M j hjM a q hq hp ha

def hillNativeHierarchyTraceValue (m : ℕ)
    (p : WeightedCoeff (hillIntegerWeight m).doubleIndex.toWeight 2) : ℂ :=
  hillSobolevTraceValue m m (hillNativeIntegerToScalar m p)

theorem continuous_hillNativeHierarchyTraceValue (m : ℕ) : Continuous (hillNativeHierarchyTraceValue m) :=
  (continuous_hillSobolevTraceValue m m).comp (hillNativeIntegerToScalar m).continuous

end NLS.KdV
