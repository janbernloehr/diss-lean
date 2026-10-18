import NLS.ZakharovShabat.SourcePhysicalActions
import NLS.ZakharovShabat.SourceSection14ActionAngle
import NLS.ZakharovShabat.SourceHilbertActionTrace

/-! # The global physical Hilbert action-angle homeomorphism

The physical source and sequence target both use the sum of the component
energies. The global map and inverse are analytic in these norms. Literal
coordinates, choice independence, the convergent mass trace, exact norm
preservation, family independence, and exponent compatibility are retained.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Hilbert sequence pairs carry the sum of the two component energies. -/
abbrev PhysicalRealBirkhoffTarget := WithLp 2 (RealCoeff 2 × RealCoeff 2)

/-- Keep the raw Hilbert target coordinates while comparing to the product norm. -/
def physicalRealTargetEquiv : PhysicalRealBirkhoffTarget ≃L[ℝ] (RealCoeff 2 × RealCoeff 2) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)

/-- The physical real map with the exact source and target Hilbert norms. -/
def physicalRealActionAngleHomeomorph : physicalRealSubmodule ≃ₜ PhysicalRealBirkhoffTarget :=
  (realSourcePhysicalL2Equiv.toHomeomorph.symm.trans (D.realActionAngleHomeomorph le_rfl)).trans
    physicalRealTargetEquiv.symm.toHomeomorph

/-- The physical map retains exactly the original real action-angle coordinates. -/
@[simp] theorem physicalRealActionAngleHomeomorph_apply (u : physicalRealSubmodule) :
    (D.physicalRealActionAngleHomeomorph u).ofLp =
      D.realActionAngleMap (realSourcePhysicalL2Equiv.symm u) := rfl

/-- The inverse recovers the physical L2 class from the original inverse source. -/
@[simp] theorem physicalRealActionAngleHomeomorph_symm_apply (z : PhysicalRealBirkhoffTarget) :
    D.physicalRealActionAngleHomeomorph.symm z =
      realSourcePhysicalL2Equiv ((D.realActionAngleHomeomorph le_rfl).symm z.ofLp) := rfl

/-- Forward and inverse maps are analytic in the original physical Hilbert norms. -/
theorem physicalRealActionAngleHomeomorph_analytic :
    AnalyticOnNhd ℝ D.physicalRealActionAngleHomeomorph univ ∧
      AnalyticOnNhd ℝ D.physicalRealActionAngleHomeomorph.symm univ := by
  constructor
  · intro u _
    exact (physicalRealTargetEquiv.symm.analyticAt _).comp
      (((D.realActionAngleHomeomorph_analytic le_rfl).1 _ (mem_univ _)).comp
        (realSourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt u))
  · intro z _
    exact (realSourcePhysicalL2Equiv.toContinuousLinearEquiv.analyticAt _).comp
      (((D.realActionAngleHomeomorph_analytic le_rfl).2 _ (mem_univ _)).comp
        (physicalRealTargetEquiv.analyticAt z))

/-- The physical coordinates are literally the positive-root action-angle formulas. -/
theorem physicalRealActionAngleHomeomorph_formula (u : physicalRealSubmodule) (n : ℤ) :
    let φ := sourcePhysicalL2Equiv.symm u.val
    (D.physicalRealActionAngleHomeomorph u).fst n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
      Real.cos (sourceAngularOriginalTheta (by simp) (by norm_num) n s φ).re ∧
    (D.physicalRealActionAngleHomeomorph u).snd n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
      Real.sin (sourceAngularOriginalTheta (by simp) (by norm_num) n s φ).re := by
  constructor <;> rfl

/-- Every admissible eta choice gives the same physical coordinates; closed gaps need no choice condition. -/
theorem physicalRealActionAngleHomeomorph_formula_of_eta (u : physicalRealSubmodule) (n : ℤ) (v : ℂ)
    (hv : sourcePeriodicGapDisplacement (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u.val) n ≠ 0 →
      v ∈ sourceAngularOriginalEtaIntegralValues (by simp) (by norm_num) n s (sourcePhysicalL2Equiv.symm u.val)) :
    let φ := sourcePhysicalL2Equiv.symm u.val
    (D.physicalRealActionAngleHomeomorph u).fst n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
      Real.cos (v+sourceAngularBetaCorrection (by simp) (by norm_num) n s φ).re ∧
    (D.physicalRealActionAngleHomeomorph u).snd n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
      Real.sin (v+sourceAngularBetaCorrection (by simp) (by norm_num) n s φ).re := by
  change (D.realActionAngleMap _).1 n = _ ∧ (D.realActionAngleMap _).2 n = _
  rw [D.realActionAngleMap_eq]
  exact D.real_rectangular_formula_of_eta (realSourcePhysicalL2Equiv.symm u) n v hv

/-- The nonlinear physical map preserves the exact source and target norms. -/
theorem physicalRealActionAngleHomeomorph_norm (u : physicalRealSubmodule) :
    ‖D.physicalRealActionAngleHomeomorph u‖ = ‖u‖ := by
  have h := D.complex.hilbert_real_map_norm_sq (realSourcePhysicalL2Equiv.symm u)
  have he : ‖D.physicalRealActionAngleHomeomorph u‖^2 = ‖u‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    change ‖(D.realActionAngleMap _).1‖^2+‖(D.realActionAngleMap _).2‖^2 = _
    rw [D.realActionAngleMap_eq]
    exact h.trans (congrArg (fun r : ℝ => r^2) (realSourcePhysicalL2Equiv.symm.norm_map u))
  nlinarith [norm_nonneg (D.physicalRealActionAngleHomeomorph u),norm_nonneg u]

/-- The global physical inverse preserves the exact Hilbert norm. -/
theorem physicalRealActionAngleHomeomorph_symm_norm (z : PhysicalRealBirkhoffTarget) :
    ‖D.physicalRealActionAngleHomeomorph.symm z‖ = ‖z‖ := by
  have h := D.physicalRealActionAngleHomeomorph_norm (D.physicalRealActionAngleHomeomorph.symm z)
  rw [D.physicalRealActionAngleHomeomorph.apply_symm_apply] at h
  exact h.symm

include D in
/-- The physical action sum is half the squared original L2 pair norm. -/
theorem physical_sum_actions (u : physicalRealSubmodule) :
    (∑' n : ℤ, (physicalIndexedAction n u.val).re) = ‖u‖^2/2 := by
  have h := D.complex.hilbert_sum_actions_eq_half_norm_sq (realSourcePhysicalL2Equiv.symm u)
  have he : (∑' n : ℤ, (physicalIndexedAction n u.val).re) =
      ∑' n : ℤ, (sourceRealAction (by simp) (by norm_num)
        (realSourcePhysicalL2Equiv.symm u).val (realSourcePhysicalL2Equiv.symm u).property n).re := by
    apply tsum_congr
    intro n
    exact congrArg Complex.re (sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num)
      n (realSourcePhysicalL2Equiv.symm u).val (realSourcePhysicalL2Equiv.symm u).property)
  exact he.trans (h.trans (congrArg (fun r : ℝ => r^2/2) (realSourcePhysicalL2Equiv.symm.norm_map u)))

include D in
/-- The physical action series converges, with its actual mass as sum. -/
theorem physical_hasSum_actions (u : physicalRealSubmodule) :
    HasSum (fun n : ℤ => (physicalIndexedAction n u.val).re) (‖u‖^2/2) := by
  have hs := D.complex.summable_hilbert_realActions (realSourcePhysicalL2Equiv.symm u)
  have ht : Summable (fun n : ℤ => (physicalIndexedAction n u.val).re) := hs.congr (fun n => by
    exact (congrArg Complex.re (sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num)
      n (realSourcePhysicalL2Equiv.symm u).val (realSourcePhysicalL2Equiv.symm u).property)).symm)
  rw [← D.physical_sum_actions u]
  exact ht.hasSum

/-- Independent normalized families give the same physical map. -/
theorem physicalRealActionAngleHomeomorph_family
    {A B C : Set (CoeffPair 2)} {t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (E : SourceSection14OriginalData (by simp) (by norm_num) A B C t) :
    D.physicalRealActionAngleHomeomorph = E.physicalRealActionAngleHomeomorph := by
  ext u : 1
  apply WithLp.ofLp_injective
  change D.realActionAngleMap _ = E.realActionAngleMap _
  rw [D.realActionAngleMap_family E]

/-- Every larger finite exponent gives the same coordinates on original physical Hilbert data. -/
theorem physicalRealActionAngleHomeomorph_exponent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {hp : p ≠ ⊤} {hp1 : 1 < p} {A B C : Set (CoeffPair p)}
    {t : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (E : SourceSection14OriginalData hp hp1 A B C t) (h2p : 2 ≤ p) (u : physicalRealSubmodule) :
    ((RealCoeff.exponentInclusion h2p).prodMap (RealCoeff.exponentInclusion h2p))
      (D.physicalRealActionAngleHomeomorph u).ofLp =
      E.realActionAngleMap (realTypeSourceExponentInclusion h2p (realSourcePhysicalL2Equiv.symm u)) :=
  D.realActionAngleMap_exponent E h2p (realSourcePhysicalL2Equiv.symm u)

end SourceSection14OriginalData

end NLS.ZakharovShabat
