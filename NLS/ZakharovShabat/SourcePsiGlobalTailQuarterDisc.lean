import NLS.ZakharovShabat.SourcePsiGlobalContourFamily
import NLS.ZakharovShabat.SourcePsiShiftedDiscLatticeBound
import NLS.ZakharovShabat.SourcePsiNearFreeGapGeometry
import NLS.ZakharovShabat.SourcePsiRealTailOpenGap

/-!
# Free quarter-disc omission on the global tail

Near an arbitrary real-type source, distant selected periodic gaps
have free-centered eighth-π contours. The free quarter-π discs at
still more distant indices also avoid the finitely many nonstandard
head gaps, providing a common omitted-root analytic domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At sufficiently distant selected indices, the closed free
quarter-π disc avoids every other moving periodic gap on one source
neighborhood. -/
theorem exists_local_sourcePsi_tailQuarterDisc_omittedDomain
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ m : ℤ, K ≤ m.natAbs →
        closedBall ((Real.pi : ℂ)*m) (Real.pi/4) ⊆
          sourceStandardRootOmittedDomain hp hp1 ψ m := by
  obtain ⟨K₀,V,hVopen,hφV,c,R,hchoice,hgeom⟩ :=
    exists_local_sourcePsi_allGap_contourFamily hp hp1 φ hφ
  let s : Finset ℤ := Finset.Icc (-(K₀ : ℤ)) (K₀ : ℤ)
  have hRhead (k : ℤ) (hk : k ∈ s) : 0 ≤ R k :=
    (hgeom φ hφV k).1.le
  obtain ⟨L,hL⟩ := exists_uniform_shifted_disc_lattice_cutoff
    s c R hRhead
  let K : ℕ := K₀+L+2
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ m hm z hz k hkm hzk
  by_cases hk : k ∈ s
  · have hkK : k.natAbs ≤ K₀ := by
      simp only [s,Finset.mem_Icc] at hk
      omega
    have htri : m.natAbs ≤ (m-k).natAbs + k.natAbs := by
      have h := Int.natAbs_add_le (m-k) k
      simpa only [sub_add_cancel] using h
    have hdist : L ≤ (m-k).natAbs := by
      dsimp [K] at hm
      omega
    have hsep := hL k hk m hdist
    have hzkDisc : z ∈ closedBall (c k) (R k) :=
      ball_subset_closedBall ((hgeom ψ hψ k).2.1 hzk)
    have hfar := shifted_disc_free_lattice_distance_lower
      m k (c k) (R k) hsep z hzkDisc
    have hmk : m ≠ k := Ne.symm hkm
    have habs : (1 : ℝ) ≤ |((m-k : ℤ) : ℝ)| := by
      exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hmk)
    have hnear : ‖((Real.pi : ℂ)*m)-z‖ ≤ Real.pi/4 := by
      simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hz
    nlinarith [Real.pi_pos]
  · have hkK : K₀ < k.natAbs := by
      simp only [s,Finset.mem_Icc] at hk
      omega
    obtain ⟨hc,hR⟩ := hchoice k hkK
    have hzkFree : z ∈ ball ((Real.pi : ℂ)*k) (Real.pi/8) := by
      simpa only [hc,hR] using (hgeom ψ hψ k).2.1 hzk
    exact (Set.disjoint_left.mp
      (free_quarter_closedBall_disjoint_other_eighth_ball
        m k (Ne.symm hkm))) hz hzkFree

/-- On one source neighborhood, every sufficiently distant open real
gap has a real psi equation coordinate on its free eighth-π circle,
uniformly over deleted indices and real root inputs. -/
theorem exists_local_sourcePsi_realTailOpenGap_coordinates
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
        ∀ n : ℤ, ∀ a : DeletedCoeff p n,
          (∀ k : ℤ, (displacedRoots (a : Coeff p) k).im = 0) →
            ∀ m : ℤ, K ≤ m.natAbs →
              (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
                (periodOnePotential_mem ψ) m).re <
                (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
                  (periodOnePotential_mem ψ) m).re →
                (sourcePsiEquationCoordinate hp hp1 n m
                  (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)).im = 0 := by
  obtain ⟨Kdom,Vdom,hVdomOpen,hφVdom,hdom⟩ :=
    exists_local_sourcePsi_tailQuarterDisc_omittedDomain hp hp1 φ hφ
  obtain ⟨Ksmall,Vsmall,hVsmallOpen,hφVsmall,hsmall⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨W,hWopen,_,hrealW,hQ⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let K : ℕ := max Kdom Ksmall
  let V : Set (CoeffPair p) := Vdom ∩ Vsmall ∩ W
  have hVopen : IsOpen V :=
    (hVdomOpen.inter hVsmallOpen).inter hWopen
  have hφV : φ ∈ V := ⟨⟨hφVdom,hφVsmall⟩,hrealW hφ⟩
  refine ⟨K,V,hVopen,hφV,?_⟩
  intro ψ hψ hreal n a hroots m hm hopen
  have hmDom : Kdom ≤ m.natAbs := by dsimp [K] at hm; omega
  have hmSmall : Ksmall ≤ m.natAbs := by dsimp [K] at hm; omega
  have hdomQuarter := hdom ψ hψ.1.1 m hmDom
  obtain ⟨hmid,hgap⟩ := hsmall ψ hψ.1.2 m hmSmall
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      ball ((Real.pi : ℂ)*m) (Real.pi/8) :=
    sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ m hmid hgap
  have hdomEighth : closedBall ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m :=
    (closedBall_subset_closedBall
      (by nlinarith [Real.pi_pos])).trans hdomQuarter
  have hcircle : sphere ((Real.pi : ℂ)*m) (Real.pi/8) ⊆
      sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_enclosingCircle hp hp1 ψ m
      ((Real.pi : ℂ)*m) (Real.pi/8) hseg hdomEighth
  by_cases hmn : m = n
  · subst m
    simp [sourcePsiEquationCoordinate]
  · exact sourcePsiEquationCoordinate_freeEighth_im_eq_zero_of_openRealGap
      hp hp1 ψ hreal n m (Ne.symm hmn) a hroots hopen
        W hψ.2 (hQ m).2 hdomQuarter hcircle hmid hgap

end NLS.ZakharovShabat
