import NLS.ZakharovShabat.CanonicalBoundaryRealBounds
import Mathlib.Order.Interval.Set.Infinite

/-!
# Continuity of canonical boundary coordinates at real-type potentials

Choose real barriers arbitrarily close to the given coordinate while
avoiding the finite central root set. Rouché preserves the corresponding
prefix and suffix counts. Real-part ordering bounds the nearby coordinate
between these barriers, including when roots collide. Together with
imaginary-part continuity this proves ordinary Lemma 9.1(ii) on reflected potentials.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every canonical real part is continuous at a real-type potential, including central collisions. -/
theorem continuousAt_canonicalBoundaryRoots_re_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : dirichletSubspace (p := p) =>
      (b.canonicalRoots hp hp1 ψ.val ψ.property n).re) φ := by
  obtain ⟨N,_,hN⟩ := exists_eventually_canonicalBoundaryLabeling hp hp1 φ
  let K := max N n.natAbs + 1
  have hnK : n.natAbs ≤ K := by dsimp [K]; omega
  let ξ := b.canonicalRoots hp hp1 φ.val φ.property
  let R := centralCircleRadius K
  let s := Finset.Icc (-(K : ℤ)) K
  let F := s.image (fun j => (ξ j).re)
  let x := (ξ n).re
  have hK : ∀ᶠ ψ : dirichletSubspace (p := p) in 𝓝 φ,
      BoundaryRootLabeling b hp ψ.val ψ.property K (b.canonicalRoots hp hp1 ψ.val ψ.property) := by
    filter_upwards [hN] with ψ hψ
    exact hψ b K (by dsimp [K]; omega)
  have hφ := hK.self_of_nhds
  have hstrict : ∀ j : ℤ, j.natAbs ≤ K → |(ξ j).re| < R := fun j hj =>
    hφ.abs_re_central_lt j hj
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
  obtain ⟨a₀,hb,hbF⟩ := (Set.Ioo_infinite (show max (-R) (x-ε) < x from
    max_lt hx.1 (by linarith))).exists_notMem_finset F
  have hax : x < a := ha.1
  have haR : a < R := ha.2.trans_le (min_le_left _ _)
  have haε : a < x+ε := ha.2.trans_le (min_le_right _ _)
  have hbx : a₀ < x := hb.2
  have hbR : -R < a₀ := (le_max_left _ _).trans_lt hb.1
  have hbε : x-ε < a₀ := (le_max_right _ _).trans_lt hb.1
  have hleft : ∀ z ∈ sphere (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2),
      b.characteristic hp φ.val φ.property z ≠ 0 := by
    simpa only [sub_neg_eq_add] using hφ.realDiameterSphere_nonzero_of_realType hp1 hreal
      (-R) a le_rfl haR.le (fun j hj => ne_of_gt (abs_lt.mp (hstrict j hj)).1) (havoid a haF)
  have hright := hφ.realDiameterSphere_nonzero_of_realType hp1 hreal a₀ R hbR.le le_rfl
    (havoid a₀ hbF) (fun j hj => ne_of_lt (abs_lt.mp (hstrict j hj)).2)
  have hupper := eventually_canonicalBoundaryRoots_re_le_of_barrier hp hp1 b φ hreal K hK n hnK a
    (hx.1.trans hax) haR.le hax.le hleft
  have hlower := eventually_le_canonicalBoundaryRoots_re_of_barrier hp hp1 b φ hreal K hK n hnK a₀
    hbR.le (hbx.trans hx.2) hbx.le hright
  filter_upwards [hupper,hlower] with ψ hψu hψl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Ordinary Lemma 9.1(ii): each canonical boundary coordinate is continuous at every real-type potential. -/
theorem continuousAt_canonicalBoundaryRoots_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : dirichletSubspace (p := p) =>
      b.canonicalRoots hp hp1 ψ.val ψ.property n) φ := by
  have hr := continuousAt_canonicalBoundaryRoots_re_of_realType hp hp1 b φ hreal n
  have hi := continuousAt_canonicalBoundaryRoots_im_of_realType hp hp1 b φ hreal n
  have hrc := continuous_ofReal.continuousAt.comp hr
  have hic := continuous_ofReal.continuousAt.comp hi
  have hc : ContinuousAt (fun ψ : dirichletSubspace (p := p) =>
      ((b.canonicalRoots hp hp1 ψ.val ψ.property n).re : ℂ) +
        ((b.canonicalRoots hp hp1 ψ.val ψ.property n).im : ℂ)*I) φ :=
    hrc.add (hic.mul continuousAt_const)
  simpa only [Complex.re_add_im] using hc

/-- The displacement of each fixed coordinate is continuous at a real-type potential. -/
theorem continuousAt_canonicalBoundaryDisplacement_apply_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (φ : dirichletSubspace (p := p)) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : dirichletSubspace (p := p) =>
      b.canonicalDisplacement hp hp1 ψ.val ψ.property n) φ := by
  simp only [BoundaryCondition.canonicalDisplacement_apply]
  exact (continuousAt_canonicalBoundaryRoots_of_realType hp hp1 b φ hreal n).sub continuousAt_const

end NLS.ZakharovShabat
