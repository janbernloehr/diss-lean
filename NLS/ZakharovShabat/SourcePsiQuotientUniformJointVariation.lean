import NLS.ZakharovShabat.SourcePsiQuotientUniformRootVariation
import NLS.SequenceSpaces.FiniteExponentTail

/-!
# Uniform quotient variation in both Banach parameters

Joint quotient analyticity and the locally bounded selected-disc
majorants give one Schwarz estimate for simultaneous variation of
the full root sequence and source. A fixed majorant at the reference
pair controls all nearby quotient errors, with a common linear
variation term on every selected disc.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A single Schwarz constant controls joint root/source variation
on every selected contour disc near an arbitrary real source. -/
theorem exists_sourcePsiQuotient_uniformJointVariation
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, K < m.natAbs →
        c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
      ∃ B : Coeff p, ∃ L r : ℝ, 0 ≤ L ∧ 0 < r ∧
        (∀ t ∈ ball (a,φ) r, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 t.2) ∧
        ∀ t ∈ ball (a,φ) r, ∀ m : ℤ,
          ∀ z ∈ closedBall (c m) (R m),
            ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)-1‖ ≤
              ‖B m‖ + L*‖t-(a,φ)‖ := by
  obtain ⟨U,hUopen,hbase,K,c,R,_,hchoice,hgeom,_,M,hM,hmajor⟩ :=
    exists_local_sourcePsiQuotient_uniformAllSelectedDiscMajorant hp hp1 φ hφ a
  obtain ⟨W,hWopen,_,hreal,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let V : Set (Coeff p × CoeffPair p) := U ∩ (univ ×ˢ W)
  have hVopen : IsOpen V := hUopen.inter (isOpen_univ.prod hWopen)
  have hbaseV : (a,φ) ∈ V := ⟨hbase,mem_univ _,hreal hφ⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hVopen (a,φ) hbaseV
  obtain ⟨B,_,hB⟩ := hmajor (a,φ) hbase
  let L : ℝ := 2*M/r
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨K,c,R,hchoice,B,L,r,hL,hr,
    (fun t ht m => hgeom t (hball ht).1 m),?_⟩
  intro t ht m z hz
  let f : Coeff p × CoeffPair p → ℂ := fun q =>
    sourceSingleRootQuotientJointProduct hp hp1 m (z,q)
  have hdiff : DifferentiableOn ℂ f (ball (a,φ) r) := by
    intro q hq
    have hdom : (z,q) ∈ sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨(hball hq).2.2,(hgeom q (hball hq).1 m).2.2.1 hz⟩
    have hinc : AnalyticAt ℂ (fun b : Coeff p × CoeffPair p => (z,b)) q :=
      analyticAt_const.prod analyticAt_id
    exact (((hQ m).2 (z,q) hdom).comp hinc).differentiableAt.differentiableWithinAt
  have hnorm (q : Coeff p × CoeffPair p) (hq : q ∈ ball (a,φ) r) :
      ‖f q-1‖ ≤ M := by
    obtain ⟨Bq,hBqnorm,hBq⟩ := hmajor q (hball hq).1
    exact (hBq m z hz).trans
      ((lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' Bq m).trans hBqnorm)
  have hmaps : MapsTo f (ball (a,φ) r) (closedBall (f (a,φ)) (2*M)) := by
    intro q hq
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖f q-f (a,φ)‖ = ‖(f q-1)-(f (a,φ)-1)‖ := by congr 1; ring
      _ ≤ ‖f q-1‖+‖f (a,φ)-1‖ := norm_sub_le _ _
      _ ≤ M+M := add_le_add (hnorm q hq) (hnorm (a,φ) (mem_ball_self hr))
      _ = 2*M := by ring
  have hvar : ‖f t-f (a,φ)‖ ≤ L*‖t-(a,φ)‖ := by
    simpa only [dist_eq_norm] using
      Complex.dist_le_div_mul_dist_of_mapsTo_ball hdiff hmaps ht
  calc
    ‖f t-1‖ = ‖(f t-f (a,φ))+(f (a,φ)-1)‖ := by congr 1; ring
    _ ≤ ‖f t-f (a,φ)‖+‖f (a,φ)-1‖ := norm_add_le _ _
    _ ≤ L*‖t-(a,φ)‖+‖B m‖ := add_le_add hvar (hB m z hz)
    _ = ‖B m‖+L*‖t-(a,φ)‖ := by ring

/-- The quotient tends uniformly to one on free-centered tail discs
throughout a joint neighborhood of any root vector and real source.
The same cutoff encloses all moving periodic tail segments. -/
theorem exists_local_sourcePsiQuotient_uniformSmallTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a,φ) ∈ U ∧
      ∃ K : ℕ, ∀ t ∈ U, ∀ m : ℤ, K ≤ m.natAbs →
        sourcePeriodicSegment hp hp1 t.2 m ⊆ ball ((Real.pi : ℂ)*m) (Real.pi/8) ∧
        ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
          ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)-1‖ < ε := by
  obtain ⟨K,c,R,hchoice,B,L,r,hL,hr,hgeom,hbound⟩ :=
    exists_sourcePsiQuotient_uniformJointVariation hp hp1 a φ hφ
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  obtain ⟨N,hN⟩ := NLS.Coeff.exists_natAbs_norm_lt hpr B (half_pos hε)
  let ρ := min r (ε/(2*(L+1)))
  have hρ : 0 < ρ := lt_min hr (by positivity)
  refine ⟨ball (a,φ) ρ,isOpen_ball,mem_ball_self hρ,max (K+1) N,?_⟩
  intro t ht m hm
  have ht' : t ∈ ball (a,φ) r := ball_subset_ball (min_le_left _ _) ht
  have hmK : K < m.natAbs := by omega
  have hmN : N ≤ m.natAbs := by omega
  obtain ⟨hc,hR⟩ := hchoice m hmK
  have hseg := (hgeom t ht' m).2.1
  rw [hc,hR] at hseg
  refine ⟨hseg,?_⟩
  intro z hz
  have hz' : z ∈ closedBall (c m) (R m) := by simpa only [hc,hR] using hz
  have hdist : ‖t-(a,φ)‖ < ε/(2*(L+1)) := by
    have htDist : ‖t-(a,φ)‖ < ρ := by simpa only [mem_ball,dist_eq_norm] using ht
    exact htDist.trans_le (min_le_right _ _)
  have hvar : L*‖t-(a,φ)‖ < ε/2 := by
    have hpos : 0 < 2*(L+1) := by positivity
    have hmul := (lt_div_iff₀ hpos).mp hdist
    have hnorm := norm_nonneg (t-(a,φ))
    nlinarith
  exact (hbound t ht' m z hz').trans_lt (by linarith [hN m hmN])

end NLS.ZakharovShabat
