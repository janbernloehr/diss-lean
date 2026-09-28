import NLS.ZakharovShabat.SourcePsiSelectedJacobianDiagonalCompact
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation
import NLS.ZakharovShabat.SourcePsiRegularFactorIsolatingDisc
import NLS.ZakharovShabat.SourcePsiFilledRegularFactor
import NLS.SequenceSpaces.CompactIdentityFredholm

/-!
# Diagonal isomorphism from isolated selected roots

The scalar all-gap nonvanishing argument and the compact operator
decomposition now use one selected contour family. Pairwise disjoint
isolating discs supply the two root-separation hypotheses in every
retained row. The contour construction places each selected closed
disc inside its assigned isolating disc, and analyticity of the regular
factor follows from the global analytic quotient domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- For a common locally selected contour family, root localization in
the assigned isolating discs makes the diagonal part of the bounded psi
Jacobian bijective, while its off-diagonal part is compact. -/
theorem exists_local_sourcePsi_selectedJacobian_isolatingDiagonal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        (∀ i j : ℤ, i ≠ j →
          Disjoint (sourceIsolatingDisc hp hp1 φ Niso εiso i)
            (sourceIsolatingDisc hp hp1 φ Niso εiso j)) ∧
        (∀ m : ℤ, closedBall (c m) (R m) ⊆
          sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m
              (t.1 : Coeff p) t.2 (c m) (R m)) ∧
        (∀ t ∈ U,
          IsRealType (CoeffPair.toMax p t.2) →
          (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
            ∀ m : ℤ,
              ((sourcePsiSelectedEquationSequence hp hp1 n c R
                t.1 t.2 : Coeff p) m).im = 0) ∧
        DifferentiableOn ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U ∧
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ k : ℤ, k ≠ n →
            displacedRoots (a : Coeff p) k ∈
              sourceIsolatingDisc hp hp1 φ Niso εiso k) →
            let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
            let d : Coeff ⊤ := Coeff.deletedJacobianDiagonalSymbol n Q
            let D : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              Coeff.deletedMultiplierCLM n d
            let C : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              Coeff.deletedJacobianOffDiagonal n Q
            IsCompactOperator C ∧ Function.Bijective D ∧ Q = D + C := by
  obtain ⟨Umain,hUmainOpen,hbaseMain,c,R,Niso,εiso,
      hcluster,hdisjoint,hfilled,hcReal,hgeom,hcoord,hrealSeq,hdiff,hmain⟩ :=
    exists_local_sourcePsi_selectedJacobian_diagonalPlusCompact
      hp hp1 φ hφ n a₀
  obtain ⟨W,hWopen,_,hrealW,hQdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let U : Set (DeletedCoeff p n × CoeffPair p) :=
    Umain ∩ {t | t.2 ∈ W}
  have hUopen : IsOpen U :=
    hUmainOpen.inter (hWopen.preimage continuous_snd)
  have hbase : (a₀,φ) ∈ U := ⟨hbaseMain,hrealW hφ⟩
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,
    hdisjoint,hfilled,hcReal,?_,?_,?_,?_,?_⟩
  · intro t ht m
    exact hgeom t ht.1 m
  · intro t ht m
    exact hcoord t ht.1 m
  · intro t ht hreal hroots m
    exact hrealSeq t ht.1 hreal hroots m
  · exact hdiff.mono (fun t ht => ht.1)
  intro a ψ hpair hreal hroots hrootloc
  have hlocTail : ∀ j : ℤ, Niso < j.natAbs →
      ‖(a : Coeff p) j‖ ≤ Real.pi/4 := by
    intro j hj
    by_cases hjn : j = n
    · subst j
      rw [show (a : Coeff p) n = 0 from a.property, norm_zero]
      positivity
    have hnot : ¬ j.natAbs ≤ Niso := not_le.mpr hj
    have hdist : dist (displacedRoots (a : Coeff p) j)
        ((Real.pi : ℂ)*j) < Real.pi/4 := by
      simpa only [sourceIsolatingDisc,if_neg hnot,refinedResonantDisk,
        mem_ball] using hrootloc j hjn
    have heq : dist (displacedRoots (a : Coeff p) j)
        ((Real.pi : ℂ)*j) = ‖(a : Coeff p) j‖ := by
      simp [dist_eq_norm,displacedRoots]
    rw [heq] at hdist
    exact hdist.le
  obtain ⟨hdom,L,htail,hcompact,hbij,hnonzero,hsplit⟩ :=
    hmain a ψ hpair.1 hreal hroots hlocTail
  refine ⟨hcompact,?_,hsplit⟩
  apply hbij
  intro m hmn _
  let ξ : ℂ := sourceStandardRootMidpoint hp hp1 ψ n
  have hξSeg : ξ ∈ sourcePeriodicSegment hp hp1 ψ n := by
    simpa only [ξ, sourceStandardRootMidpoint] using
      sourcePeriodicMidpoint_mem_segment hp hp1 ψ n
  have hξDisc : ξ ∈ sourceIsolatingDisc hp hp1 φ Niso εiso n :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ Niso εiso n
      (hcluster (a,ψ) hpair.1 n) hξSeg
  have hξReal : ξ.im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType
      hp hp1 ψ hreal n ξ hξSeg
  have hrootsFilled : ∀ k : ℤ,
      (displacedRoots (sourcePsiFillDeletedRoot n a ξ) k).im = 0 :=
    displacedRoots_sourcePsiFillDeletedRoot_im_eq_zero n a ξ
      (fun k _ => hroots k) hξReal
  have hrootlocFilled : ∀ k : ℤ,
      displacedRoots (sourcePsiFillDeletedRoot n a ξ) k ∈
        sourceIsolatingDisc hp hp1 φ Niso εiso k := by
    intro k
    by_cases hkn : k = n
    · subst k
      simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using hξDisc
    · rw [displacedRoots_sourcePsiFillDeletedRoot_other n k hkn]
      exact hrootloc k hkn
  apply hnonzero m hmn ξ hrootsFilled
  · have hcircle : ∀ j : ℤ,
        sphere (c j) (R j) ⊆
          sourceIsolatingDisc hp hp1 φ Niso εiso j := by
      intro j z hz
      exact hfilled j (sphere_subset_closedBall hz)
    exact sourcePsi_deletedRoot_avoids_otherCircle_of_isolatingDiscs
      hp hp1 φ Niso εiso (sourcePsiFillDeletedRoot n a ξ) c R
        hcircle hrootlocFilled hdisjoint m n hmn
  · exact analyticOnNhd_sourcePsiFillDeletedRoot_gapRegularFactor
      hp hp1 φ Niso εiso n m a ξ ψ W hpair.2 (hQdata m).2
        (c m) (R m) (hdom m) (hfilled m) hξDisc
        (hdisjoint m n hmn)
  · exact sourcePsi_otherRoots_avoid_standardGap_of_isolatingDiscs
      hp hp1 φ ψ Niso εiso (sourcePsiFillDeletedRoot n a ξ)
        (fun j => sourcePeriodicSegment_subset_isolatingDisc
          hp hp1 φ ψ Niso εiso j
            (hcluster (a,ψ) hpair.1 j))
        hrootlocFilled hdisjoint m

/-- The local selected Jacobian is an isomorphism as soon as its
injectivity is known. This is the Fredholm reduction in Corollary 12.8;
the injectivity assertion itself is Lemma 12.7. -/
theorem exists_local_sourcePsi_selectedJacobian_bijective_of_injective
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ k : ℤ, k ≠ n →
            displacedRoots (a : Coeff p) k ∈
              sourceIsolatingDisc hp hp1 φ Niso εiso k) →
            let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
            Function.Injective Q → Function.Bijective Q := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,_,_,_,_,_,_,_,hdecomp⟩ :=
    exists_local_sourcePsi_selectedJacobian_isolatingDiagonal
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,?_⟩
  intro a ψ hpair hreal hroots hrootloc Q hinj
  obtain ⟨hcompact,hbij,hsplit⟩ :=
    hdecomp a ψ hpair hreal hroots hrootloc
  dsimp only [Q] at hinj ⊢
  rw [hsplit]
  exact Coeff.bijective_add_compact_of_bijective_of_injective
    _ _ hbij hcompact (by simpa only [← hsplit] using hinj)

end NLS.ZakharovShabat
