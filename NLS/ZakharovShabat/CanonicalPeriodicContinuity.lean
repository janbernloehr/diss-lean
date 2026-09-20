import NLS.ZakharovShabat.PeriodicEndpointRealBarriers
import Mathlib.Order.Interval.Set.Infinite

/-!
# Continuity of canonical periodic endpoints at real-type potentials

Choose nearby real barriers avoiding the finite central spectrum. Stable
prefix and suffix counts control every ordered slot's real part, including
at multiple eigenvalues. Imaginary-part stability then gives continuity
under arbitrary even complex perturbations of a real-type potential.
-/

noncomputable section
open Set Complex Filter Topology Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The real part of each canonical endpoint slot is continuous at real-type potentials. -/
theorem continuousAt_canonicalPeriodicSlot_re_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (k : ℤ ×ₗ Fin 2) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      (canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).re) φ := by
  obtain ⟨N,hkN,_,hN⟩ := exists_eventually_canonicalPeriodicEndpointLabeling_above hp hp1 φ (ofLex k).1.natAbs
  let ξ := canonicalPeriodicSlot hp hp1 φ.val φ.property
  let R := centralCircleRadius N
  let s := centralPeriodicSlots N
  let F := s.image (fun j => (ξ j).re)
  let x := (ξ k).re
  have hφ := hN.self_of_nhds
  have hk : k ∈ s := (mem_centralPeriodicSlots N k).mpr hkN
  have hstrict : ∀ j ∈ s, |(ξ j).re| < R := fun j hj =>
    hφ.abs_re_central_lt (ofLex j).1 ((mem_centralPeriodicSlots N j).mp hj) _ (periodicEndpointSlot_mem_pair _ _ j)
  have hx : -R < x ∧ x < R := abs_lt.mp (hstrict k hk)
  have havoid (a : ℝ) (ha : a ∉ F) : ∀ j ∈ s, (ξ j).re ≠ a := by
    intro j hj he
    exact ha (Finset.mem_image.mpr ⟨j,hj,he⟩)
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
  have hleft : ∀ z ∈ sphere (((-R+a)/2 : ℝ) : ℂ) ((a+R)/2), z ∉ periodicSpectrum hp φ.val := by
    simpa only [sub_neg_eq_add] using hφ.realDiameterSphere_avoids_spectrum hreal (-R) a le_rfl haR.le
      (fun j hj => ne_of_gt (abs_lt.mp (hstrict j hj)).1) (havoid a haF)
  have hright := hφ.realDiameterSphere_avoids_spectrum hreal b R hbR.le le_rfl
    (havoid b hbF) (fun j hj => ne_of_lt (abs_lt.mp (hstrict j hj)).2)
  have hupper := eventually_canonicalPeriodicSlot_re_le_of_barrier hp hp1 φ hreal N hN k hk a
    (hx.1.trans hax) haR.le hax.le hleft
  have hlower := eventually_le_canonicalPeriodicSlot_re_of_barrier hp hp1 φ hreal N hN k hk b
    hbR.le (hbx.trans hx.2) hbx.le hright
  filter_upwards [hupper,hlower] with ψ hψu hψl
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- Each canonical periodic endpoint slot is continuous at every real-type potential. -/
theorem continuousAt_canonicalPeriodicSlot_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (k : ℤ ×ₗ Fin 2) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalPeriodicSlot hp hp1 ψ.val ψ.property k) φ := by
  have hr := continuousAt_canonicalPeriodicSlot_re_of_realType hp hp1 φ hreal k
  have hi := continuousAt_canonicalPeriodicSlot_im_of_realType hp hp1 φ hreal k
  have hc : ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      ((canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).re : ℂ) +
        ((canonicalPeriodicSlot hp hp1 ψ.val ψ.property k).im : ℂ)*I) φ :=
    (continuous_ofReal.continuousAt.comp hr).add
      ((continuous_ofReal.continuousAt.comp hi).mul continuousAt_const)
  simpa only [Complex.re_add_im] using hc

/-- The left canonical periodic coordinate is continuous at every real-type potential. -/
theorem continuousAt_canonicalPeriodicLeft_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalPeriodicLeft hp hp1 ψ.val ψ.property n) φ := by
  simpa only [canonicalPeriodicSlot_left] using
    continuousAt_canonicalPeriodicSlot_of_realType hp hp1 φ hreal (toLex (n,0))

/-- The right canonical periodic coordinate is continuous at every real-type potential. -/
theorem continuousAt_canonicalPeriodicRight_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalPeriodicRight hp hp1 ψ.val ψ.property n) φ := by
  simpa only [canonicalPeriodicSlot_right] using
    continuousAt_canonicalPeriodicSlot_of_realType hp hp1 φ hreal (toLex (n,1))

/-- Each left displacement coordinate is continuous at real-type potentials. -/
theorem continuousAt_canonicalPeriodicLeftDisplacement_apply_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalPeriodicLeftDisplacement hp hp1 ψ.val ψ.property n) φ :=
  (continuousAt_canonicalPeriodicLeft_of_realType hp hp1 φ hreal n).sub continuousAt_const

/-- Each right displacement coordinate is continuous at real-type potentials. -/
theorem continuousAt_canonicalPeriodicRightDisplacement_apply_of_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : pairParitySubspace (p := p) 0) (hreal : IsRealType φ.val) (n : ℤ) :
    ContinuousAt (fun ψ : pairParitySubspace (p := p) 0 =>
      canonicalPeriodicRightDisplacement hp hp1 ψ.val ψ.property n) φ :=
  (continuousAt_canonicalPeriodicRight_of_realType hp hp1 φ hreal n).sub continuousAt_const

end NLS.ZakharovShabat
