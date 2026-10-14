import NLS.ZakharovShabat.SourceTheorem12_1

/-!
# The literal functions and roots in Theorem 12.1

The simultaneous root family produces entire functions with the exact
normalization of (2.20). The symmetric cutoffs include the exceptional
denominator π₀ = 1. The roots depend analytically on the complex source,
lie between the real periodic endpoints at real sources, and specialize
to the free lattice at zero potential.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Equation (2.20) as the limit of its literal symmetric finite products. -/
theorem tendsto_sourcePsiCandidate_literalProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (a : Coeff p) (z : ℂ) :
    Tendsto (fun N : ℕ => (-2 / singleSpectralDenominator n) *
      ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
        (displacedRoots a m-z) / singleSpectralDenominator m)
      atTop (𝓝 (sourcePsiCandidate n (z,a))) := by
  convert tendsto_sourcePsiCandidate_partialProduct hp hp1 n (z,a) using 1
  funext N
  simp only [jointDeletedSingleSpectralPartialProduct, singleSpectralFactor]
  ring

namespace SourceTheorem12_1Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual roots, including their free lattice centers, are complex analytic. -/
theorem root_analytic (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n m : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => displacedRoots (s n ψ : Coeff p) m) W := by
  intro ψ hψ
  let i : DeletedCoeff p n →L[ℂ] Coeff p := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have ha : AnalyticAt ℂ (fun χ => (s n χ : Coeff p)) ψ :=
    (i.analyticAt _).comp (H.analytic n ψ hψ)
  exact analyticAt_const.add ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).analyticAt _ |>.comp ha)

/-- In particular, the possibly complex roots have the asserted real analyticity. -/
theorem root_real_analytic (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n m : ℤ) :
    AnalyticOnNhd ℝ (fun ψ => displacedRoots (s n ψ : Coeff p) m) W :=
  (H.root_analytic n m).restrictScalars

/-- The entire functions vary jointly analytically with the complex source. -/
theorem numerator_joint (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourcePsiCandidate n (t.1,(s n t.2 : Coeff p)))
      (univ ×ˢ W) := by
  intro t ht
  let i : DeletedCoeff p n →L[ℂ] Coeff p := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL
  have hroot : AnalyticAt ℂ (fun u : ℂ × CoeffPair p => (s n u.2 : Coeff p)) t :=
    (i.analyticAt _).comp ((H.analytic n t.2 ht.2).comp analyticAt_snd)
  exact (analyticOnNhd_sourcePsiCandidate hp hp1 n (t.1,(s n t.2 : Coeff p)) (mem_univ _)).comp
    (f := fun u : ℂ × CoeffPair p => (u.1,(s n u.2 : Coeff p))) (analyticAt_fst.prod hroot)

/-- Every member of the simultaneous family is entire. -/
theorem entire (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    Differentiable ℂ (fun z => sourcePsiCandidate n (z,(s n ψ : Coeff p))) := by
  intro z
  exact ((H.numerator_joint n (z,ψ) ⟨mem_univ _,hψ⟩).comp
    (f := fun w : ℂ => (w,ψ)) (analyticAt_id.prod analyticAt_const)).differentiableAt

/-- At a real source, every retained root lies in its assigned closed gap. -/
theorem root_mem_gap (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (n m : ℤ) (hmn : m ≠ n) (φ : realTypeSourceLocus p) :
    displacedRoots (s n φ.val : Coeff p) m ∈ sourcePeriodicSegment hp hp1 φ.val m := by
  rw [H.real_agreement]
  exact sourcePsiGapRoot_mem_periodicSegment hp hp1 n m hmn φ

/-- The literal ordered real-endpoint assertion in Theorem 12.1. -/
theorem root_real_bounds (H : SourceTheorem12_1Data hp hp1 W₀ W s)
    (n m : ℤ) (hmn : m ≠ n) (φ : realTypeSourceLocus p) :
    (displacedRoots (s n φ.val : Coeff p) m).im = 0 ∧
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m).re ≤
        (displacedRoots (s n φ.val : Coeff p) m).re ∧
      (displacedRoots (s n φ.val : Coeff p) m).re ≤
        (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m).re := by
  have hgap := H.root_mem_gap n m hmn φ
  exact ⟨sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 φ.val φ.property m _ hgap,
    sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val m _ hgap⟩

/-- The entire root displacement vector is zero at the free source. -/
theorem displacement_zero (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n : ℤ) : s n 0 = 0 := by
  simpa only [sourcePsiGapRoot_zero] using
    H.real_agreement n (⟨0, by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus p)

/-- The free specialization of every root is exactly its signed lattice point. -/
theorem root_zero (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n m : ℤ) :
    displacedRoots (s n 0 : Coeff p) m = (Real.pi : ℂ)*m := by
  rw [H.displacement_zero]
  simp [displacedRoots]

/-- The normalization is retained at zero potential, including the omitted root. -/
theorem numerator_zero (H : SourceTheorem12_1Data hp hp1 W₀ W s) (n : ℤ) (z : ℂ) :
    sourcePsiCandidate n (z,(s n 0 : Coeff p)) = sourcePsiFree n z := by
  rw [H.displacement_zero]
  exact sourcePsiCandidate_zero hp hp1 n z

end SourceTheorem12_1Data
end NLS.ZakharovShabat
