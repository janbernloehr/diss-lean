import NLS.ZakharovShabat.SourceStandardRootAnalytic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Basic inverse-root contour identities

The reciprocal standard root is analytic off the closed periodic gap.
Cauchy's theorem gives zero for circles whose filled discs avoid the
gap, including circles inside a different isolating disc. At a
collapsed gap the root is linear and the normalized diagonal contour
integral is minus one.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The standard root does not vanish off its closed gap segment. -/
theorem sourceStandardRoot_ne_zero_off_segment
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    sourceStandardRoot hp hp1 ψ n z ≠ 0 := by
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have ha : a ≠ z := by
    intro he
    apply hz
    rw [← he]
    exact left_mem_segment ℝ a b
  have hb : b ≠ z := by
    intro he
    apply hz
    rw [← he]
    exact right_mem_segment ℝ a b
  have hs := sourceStandardRoot_sq_of_not_mem_segment hp hp1 ψ n z hz
  change sourceStandardRoot hp hp1 ψ n z ^ 2 = (a-z)*(b-z) at hs
  intro he
  rw [he] at hs
  simp only [zero_pow (by norm_num : 2 ≠ 0)] at hs
  rcases mul_eq_zero.mp hs.symm with h | h
  · exact ha (sub_eq_zero.mp h)
  · exact hb (sub_eq_zero.mp h)

/-- The reciprocal standard root is analytic off its own gap segment. -/
theorem sourceStandardRoot_inv_analyticAt
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∉ sourcePeriodicSegment hp hp1 ψ n) :
    AnalyticAt ℂ (fun w => (sourceStandardRoot hp hp1 ψ n w)⁻¹) z := by
  exact (sourceStandardRoot_analyticAt hp hp1 ψ n z hz).inv
    (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ n z hz)

/-- The inverse standard root integrates to zero around a filled circle
that avoids the indexed gap segment. -/
theorem circleIntegral_sourceStandardRoot_inv_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (havoid : closedBall c r ⊆ (sourcePeriodicSegment hp hp1 ψ n)ᶜ) :
    (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) = 0 := by
  have hd : DifferentiableOn ℂ
      (fun z => (sourceStandardRoot hp hp1 ψ n z)⁻¹) (closedBall c r) := by
    intro z hz
    exact (sourceStandardRoot_inv_analyticAt hp hp1 ψ n z
      (havoid hz)).differentiableAt.differentiableWithinAt
  exact (DiffContOnCl.mk_ball (hd.mono ball_subset_closedBall)
    hd.continuousOn).circleIntegral_eq_zero hr


/-- The off-diagonal inverse-root contour integral vanishes for any
filled circle inside the other assigned isolating disc. -/
theorem circleIntegral_sourceStandardRoot_inv_off_index_eq_zero
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ ψ : CoeffPair p)
    (N : ℕ) (ε : ℝ) (m n : ℤ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hcluster : sourceSpectralCluster hp hp1 ψ n ⊆
      sourceIsolatingDisc hp hp1 φ N ε n)
    (hdisjoint : Disjoint (sourceIsolatingDisc hp hp1 φ N ε m)
      (sourceIsolatingDisc hp hp1 φ N ε n))
    (hfilled : closedBall c r ⊆ sourceIsolatingDisc hp hp1 φ N ε m) :
    (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) = 0 := by
  have hsegment := sourcePeriodicSegment_subset_isolatingDisc
    hp hp1 φ ψ N ε n hcluster
  apply circleIntegral_sourceStandardRoot_inv_eq_zero hp hp1 ψ n c r hr
  intro z hz hzin
  exact (Set.disjoint_left.mp hdisjoint (hfilled hz)) (hsegment hzin)


/-- At a collapsed periodic gap, the inverse standard root has the
expected residue of minus one. -/
theorem circleIntegral_sourceStandardRoot_inv_zeroGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (hmid : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ∈ ball c r) :
    (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) =
      -(2*Real.pi*Complex.I) := by
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
  have heq (z : ℂ) : (sourceStandardRoot hp hp1 ψ n z)⁻¹ =
      -((z-t)⁻¹) := by
    rw [sourceStandardRoot_of_zeroGap hp hp1 ψ n z hgap]
    change (t-z)⁻¹ = -((z-t)⁻¹)
    calc
      (t-z)⁻¹ = (-(z-t))⁻¹ := congrArg Inv.inv (by ring)
      _ = -((z-t)⁻¹) := inv_neg
  simp_rw [heq]
  have hintegral : (∮ z in C(c, r), -((z-t)⁻¹)) =
      -(∮ z in C(c, r), (z-t)⁻¹) := by
    simpa only [neg_one_mul] using
      (circleIntegral.integral_const_mul (-1) (fun z => (z-t)⁻¹) c r)
  rw [hintegral, circleIntegral.integral_sub_inv_of_mem_ball hmid]


/-- The normalized contour identity is minus one at a collapsed gap. -/
theorem normalized_circleIntegral_sourceStandardRoot_inv_zeroGap
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (c : ℂ) (r : ℝ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n = 0)
    (hmid : canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n ∈ ball c r) :
    (2*Real.pi*Complex.I)⁻¹ *
      (∮ z in C(c, r), (sourceStandardRoot hp hp1 ψ n z)⁻¹) = -1 := by
  rw [circleIntegral_sourceStandardRoot_inv_zeroGap hp hp1 ψ n c r hgap hmid]
  have hnonzero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  calc
    (2*Real.pi*Complex.I)⁻¹ * -(2*Real.pi*Complex.I) =
        -((2*Real.pi*Complex.I)⁻¹ * (2*Real.pi*Complex.I)) := by ring
    _ = -1 := by rw [inv_mul_cancel₀ hnonzero]

end NLS.ZakharovShabat
