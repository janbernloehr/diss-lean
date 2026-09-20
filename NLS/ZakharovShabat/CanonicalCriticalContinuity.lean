import NLS.ZakharovShabat.CanonicalCriticalRealBounds
import Mathlib.Order.Interval.Set.Infinite

/-!
# Continuity of canonical critical coordinates at real-type potentials

Choose real barriers arbitrarily close to the given coordinate while
avoiding the finite central root set. Rouché preserves the corresponding
prefix and suffix counts. Real-part ordering bounds the nearby coordinate
between these barriers, including when roots collide. Together with
imaginary-part continuity this proves the final assertion of Lemma 8.5.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every canonical real part is continuous at a real-type potential, including central collisions. -/
theorem continuousAt_canonicalCriticalPoints_re_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      (canonicalCriticalPoints hp hp1 ψ.val ψ.property n).re) φ := by
  obtain ⟨N,_,hN⟩ := exists_eventually_canonicalCriticalLabeling hp hp1 φ
  let K := max N n.natAbs + 1
  have hNK : N < K := by dsimp [K]; omega
  have hnK : n.natAbs ≤ K := by dsimp [K]; omega
  let ξ := canonicalCriticalPoints hp hp1 φ.val φ.property
  let R := centralCircleRadius K
  let s := Finset.Icc (-(K : ℤ)) K
  let F := s.image (fun j => (ξ j).re)
  let x := (ξ n).re
  have hφ := hN.self_of_nhds
  have hK : ∀ᶠ ψ : pairParitySubspace (p := p) 0 in 𝓝 φ,
      CriticalPointLabeling hp hp1 ψ.val ψ.property K (canonicalCriticalPoints hp hp1 ψ.val ψ.property) := by
    filter_upwards [hN] with ψ hψ
    exact hψ.enlarge K hNK.le
  have hstrict : ∀ j : ℤ, j.natAbs ≤ K → |(ξ j).re| < R := fun j hj =>
    (Complex.abs_re_le_norm _).trans_lt (hφ.norm_lt_larger_centralRadius K hNK j hj)
  have hx : -R < x ∧ x < R := abs_lt.mp (hstrict n hnK)
  have havoid (a : ℝ) (ha : a ∉ F) : ∀ j : ℤ, j.natAbs ≤ K → (ξ j).re ≠ a := by
    intro j hj he
    apply ha
    apply Finset.mem_image.mpr
    refine ⟨j,?_,he⟩
    dsimp [s]
    simp only [Finset.mem_Icc]
    omega
  change Tendsto _ (𝓝 φ) (𝓝 x)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨a,ha,haF⟩ := (Set.Ioo_infinite (show x < min R (x+ε) from
    lt_min hx.2 (by linarith))).exists_notMem_finset F
  obtain ⟨b,hb,hbF⟩ := (Set.Ioo_infinite (show max (-R) (x-ε) < x from
    max_lt hx.1 (by linarith))).exists_notMem_finset F
  have hax : x < a := ha.1
  have haR : a < R := ha.2.trans_le (min_le_left _ _)
  have haε : a < x+ε := ha.2.trans_le (min_le_right _ _)
  have hbx : b < x := hb.2
  have hbR : -R < b := (le_max_left _ _).trans_lt hb.1
  have hbε : x-ε < b := (le_max_right _ _).trans_lt hb.1
  have hleft : ∀ z ∈ sphere (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2),
      deriv (canonicalDiscriminant hp φ.val) z ≠ 0 := by
    simpa only [sub_neg_eq_add] using hφ.realDiameterSphere_nonzero_of_realType hreal K hNK.le
      (-R) a le_rfl haR.le (fun j hj => ne_of_gt (abs_lt.mp (hstrict j hj)).1) (havoid a haF)
  have hright := hφ.realDiameterSphere_nonzero_of_realType hreal K hNK.le b R hbR.le le_rfl
    (havoid b hbF) (fun j hj => ne_of_lt (abs_lt.mp (hstrict j hj)).2)
  have hupper := eventually_canonicalCriticalPoints_re_le_of_barrier hp hp1 φ hreal K hK n hnK a
    (hx.1.trans hax) haR.le hax.le hleft
  have hlower := eventually_le_canonicalCriticalPoints_re_of_barrier hp hp1 φ hreal K hK n hnK b
    hbR.le (hbx.trans hx.2) hbx.le hright
  filter_upwards [hupper,hlower] with ψ hψu hψl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Lemma 8.5: each canonical critical coordinate is continuous at every real-type potential. -/
theorem continuousAt_canonicalCriticalPoints_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalCriticalPoints hp hp1 ψ.val ψ.property n) φ := by
  have hr := continuousAt_canonicalCriticalPoints_re_of_realType hp hp1 φ hreal n
  have hi := continuousAt_canonicalCriticalPoints_im_of_realType hp hp1 φ hreal n
  have hrc := continuous_ofReal.continuousAt.comp hr
  have hic := continuous_ofReal.continuousAt.comp hi
  have hc : ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      ((canonicalCriticalPoints hp hp1 ψ.val ψ.property n).re : ℂ) +
        ((canonicalCriticalPoints hp hp1 ψ.val ψ.property n).im : ℂ)*I) φ :=
    hrc.add (hic.mul continuousAt_const)
  simpa only [Complex.re_add_im] using hc

/-- The displacement of each fixed coordinate is continuous at a real-type potential. -/
theorem continuousAt_canonicalCriticalDisplacement_apply_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalCriticalDisplacement hp hp1 ψ.val ψ.property n) φ := by
  simp only [canonicalCriticalDisplacement_apply]
  exact (continuousAt_canonicalCriticalPoints_of_realType hp hp1 φ hreal n).sub continuousAt_const

end NLS.ZakharovShabat
