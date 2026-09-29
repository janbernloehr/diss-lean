import NLS.ZakharovShabat.SourcePsiGlobalHeadDiscBound
import NLS.SequenceSpaces.DeletedCoordinateAtInfinity
import Mathlib.Analysis.Complex.Schwarz

/-!
# Uniform quotient variation in the root parameter

The locally bounded quotient majorants and the Schwarz lemma control
root-parameter variation on every selected disc with one constant.
A fixed majorant at the undeleted root sequence therefore controls all
nearby quotient errors, up to a scalar error tending to zero when the
deleted index escapes.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- With the source and spectral point fixed, the quotient is entire
in the root-displacement sequence. Its denominator is constant in
that parameter. -/
theorem differentiable_sourceSingleRootQuotient_rootParameter
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p) (z : ℂ) :
    Differentiable ℂ (fun a : Coeff p =>
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))) := by
  intro a
  have hinc : AnalyticAt ℂ (fun b : Coeff p => (z,b)) a :=
    analyticAt_const.prod analyticAt_id
  have hnum := ((analyticOnNhd_jointDeletedSingleSpectralProduct hp hp1 m)
    (z,a) (mem_univ _)).comp hinc
  exact (hnum.div_const
    (c := sourceStandardRootOmittedJointProduct hp hp1 m (z,ψ))).differentiableAt

/-- On one common family of isolating discs, a fixed `ℓᵖ` sequence
controls the quotient error at every nearby root parameter, with a
uniform linear variation term. -/
theorem exists_sourcePsiQuotient_uniformRootVariation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, K < m.natAbs →
        c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ B : Coeff p, ∃ L r : ℝ, 0 ≤ L ∧ 0 < r ∧
        ∀ b : Coeff p, b ∈ ball a r → ∀ m : ℤ,
          ∀ z ∈ closedBall (c m) (R m),
            ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(b,φ))-1‖ ≤
              ‖B m‖ + L*‖b-a‖ := by
  obtain ⟨U,hUopen,hbase,K,c,R,_,hchoice,hgeom,_,M,hM,hmajor⟩ :=
    exists_local_sourcePsiQuotient_uniformAllSelectedDiscMajorant
      hp hp1 φ hφ a
  let V : Set (Coeff p) := (fun b : Coeff p => (b,φ)) ⁻¹' U
  have hVopen : IsOpen V := hUopen.preimage (by fun_prop)
  have haV : a ∈ V := hbase
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hVopen a haV
  obtain ⟨B,hBnorm,hB⟩ := hmajor (a,φ) hbase
  let L : ℝ := 2*M/r
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨K,c,R,hchoice,(fun m => hgeom (a,φ) hbase m),B,L,r,hL,hr,?_⟩
  intro b hb m z hz
  let f : Coeff p → ℂ := fun v =>
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(v,φ))
  have hnorm (v : Coeff p) (hv : v ∈ ball a r) : ‖f v-1‖ ≤ M := by
    obtain ⟨Bv,hBvnorm,hBv⟩ := hmajor (v,φ) (hball hv)
    exact (hBv m z hz).trans
      ((lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' Bv m).trans hBvnorm)
  have hmaps : MapsTo f (ball a r) (closedBall (f a) (2*M)) := by
    intro v hv
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖f v-f a‖ = ‖(f v-1)-(f a-1)‖ := by congr 1; ring
      _ ≤ ‖f v-1‖+‖f a-1‖ := norm_sub_le _ _
      _ ≤ M+M := add_le_add (hnorm v hv) (hnorm a (mem_ball_self hr))
      _ = 2*M := by ring
  have hvar : ‖f b-f a‖ ≤ L*‖b-a‖ := by
    simpa only [dist_eq_norm] using
      Complex.dist_le_div_mul_dist_of_mapsTo_ball
        (differentiable_sourceSingleRootQuotient_rootParameter
          hp hp1 m φ z).differentiableOn hmaps hb
  calc
    ‖f b-1‖ = ‖(f b-f a)+(f a-1)‖ := by congr 1; ring
    _ ≤ ‖f b-f a‖+‖f a-1‖ := norm_add_le _ _
    _ ≤ L*‖b-a‖+‖B m‖ := add_le_add hvar (hB m z hz)
    _ = ‖B m‖+L*‖b-a‖ := by ring

end NLS.ZakharovShabat
