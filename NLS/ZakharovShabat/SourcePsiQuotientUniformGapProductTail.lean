import NLS.ZakharovShabat.SourcePsiQuotientUniformJointVariation
import NLS.ZakharovShabat.SourcePsiGapProductCompact
import NLS.ZakharovShabat.SourcePsiMidpointQuotientFiniteHeadLowerBound
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform small quotient tails near the full real gap product

Joint Schwarz estimates give a neighborhood and tail cutoff at each
reference gap-root vector. Compactness selects finitely many such
neighborhoods. Their finite union contains one closed thickening of
the entire gap product and reference source, with one common cutoff.
This bound applies to every filled deleted-index branch at once.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On a fixed neighborhood of the entire real gap product, the
regular quotients are uniformly close to one on every sufficiently
distant free-centered tail disc. The moving tail gaps lie inside
those same discs. -/
theorem exists_sourcePsiQuotient_uniformSmallTail_near_gapProduct
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ,
      ∀ t ∈ cthickening δ (sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}),
        ∀ m : ℤ, K ≤ m.natAbs →
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball ((Real.pi : ℂ)*m) (Real.pi/8) ∧
          ∀ z ∈ closedBall ((Real.pi : ℂ)*m) (Real.pi/8),
            ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)-1‖ < ε := by
  classical
  have hlocal (a : sourcePeriodicGapRootSet hp hp1 φ.val) :=
    exists_local_sourcePsiQuotient_uniformSmallTail hp hp1 a.val φ.val φ.property ε hε
  choose U hUopen hbase K htail using hlocal
  let S := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  have hS : IsCompact S := (isCompact_sourcePeriodicGapRootSet hp hp1 φ.val).prod isCompact_singleton
  have hcover : S ⊆ ⋃ a : sourcePeriodicGapRootSet hp hp1 φ.val, U a := by
    rintro ⟨a,ψ⟩ ⟨ha,hψ⟩
    have heq : ψ = φ.val := mem_singleton_iff.mp hψ
    subst ψ
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,hbase ⟨a,ha⟩⟩
  obtain ⟨s,hs⟩ := hS.elim_finite_subcover U hUopen hcover
  let O := ⋃ a ∈ s, U a
  have hO : IsOpen O := isOpen_biUnion (fun a _ => hUopen a)
  obtain ⟨δ,hδ,hthick⟩ := hS.exists_cthickening_subset_open hO hs
  refine ⟨δ,hδ,s.sup K,?_⟩
  intro t ht m hm
  obtain ⟨a,ha⟩ := mem_iUnion.mp (hthick ht)
  obtain ⟨has,hta⟩ := mem_iUnion.mp ha
  exact htail a t hta m ((Finset.le_sup has).trans hm)

/-- All midpoint quotient values have one positive lower bound near
the compact full real gap product and reference source. Tail values
are within one half of one; the finite head uses compact nonvanishing.
Collapsed gaps are included in both bounds. -/
theorem exists_sourcePsi_midpointQuotient_uniform_lowerBound_near_gapProduct
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ t ∈ cthickening δ (sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}),
        ∀ m : ℤ, c ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (sourceStandardRootMidpoint hp hp1 t.2 m,t)‖ := by
  obtain ⟨δtail,hδtail,K,htail⟩ :=
    exists_sourcePsiQuotient_uniformSmallTail_near_gapProduct hp hp1 φ (1/2) (by norm_num)
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  obtain ⟨δhead,c,hδhead,hc,hhead⟩ :=
    exists_sourcePsi_midpointQuotient_finiteHead_lowerBound_near_gapProduct hp hp1 φ s
  let S := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  refine ⟨min δtail δhead,min (1/2) c,lt_min hδtail hδhead,lt_min (by norm_num) hc,?_⟩
  intro t ht m
  by_cases hm : K ≤ m.natAbs
  · obtain ⟨hseg,hbound⟩ := htail t (cthickening_mono (min_le_left _ _) S ht) m hm
    have hmid : sourceStandardRootMidpoint hp hp1 t.2 m ∈
        closedBall ((Real.pi : ℂ)*m) (Real.pi/8) :=
      ball_subset_closedBall (hseg (sourcePeriodicMidpoint_mem_segment hp hp1 t.2 m))
    have herr := hbound _ hmid
    have htri := norm_sub_norm_le (1 : ℂ)
      (sourceSingleRootQuotientJointProduct hp hp1 m
        (sourceStandardRootMidpoint hp hp1 t.2 m,t))
    rw [norm_one,norm_sub_rev] at htri
    exact (min_le_left (1/2) c).trans (by linarith)
  · have hms : m ∈ s := by simp only [s,Finset.mem_Icc]; omega
    exact (min_le_right (1/2) c).trans
      (hhead t (cthickening_mono (min_le_right _ _) S ht) m hms)

end NLS.ZakharovShabat
