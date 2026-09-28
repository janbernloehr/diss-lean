import NLS.ZakharovShabat.SourcePsiSelectedJacobianDiagonalCompact
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation
import NLS.ZakharovShabat.SourcePsiRegularFactorIsolatingDisc

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
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ k : ℤ,
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
      hcluster,hdisjoint,hfilled,hmain⟩ :=
    exists_local_sourcePsi_selectedJacobian_diagonalPlusCompact
      hp hp1 φ hφ n a₀
  obtain ⟨W,hWopen,_,hrealW,hQdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  let U : Set (DeletedCoeff p n × CoeffPair p) :=
    Umain ∩ {t | t.2 ∈ W}
  have hUopen : IsOpen U :=
    hUmainOpen.inter (hWopen.preimage continuous_snd)
  have hbase : (a₀,φ) ∈ U := ⟨hbaseMain,hrealW hφ⟩
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,?_⟩
  intro a ψ hpair hreal hroots hrootloc
  have hlocTail : ∀ j : ℤ, Niso < j.natAbs →
      ‖(a : Coeff p) j‖ ≤ Real.pi/4 := by
    intro j hj
    have hnot : ¬ j.natAbs ≤ Niso := not_le.mpr hj
    have hdist : dist (displacedRoots (a : Coeff p) j)
        ((Real.pi : ℂ)*j) < Real.pi/4 := by
      simpa only [sourceIsolatingDisc,if_neg hnot,refinedResonantDisk,
        mem_ball] using hrootloc j
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
  apply hnonzero m hmn
  · have hcircle : ∀ j : ℤ,
        sphere (c j) (R j) ⊆
          sourceIsolatingDisc hp hp1 φ Niso εiso j := by
      intro j z hz
      exact hfilled j (sphere_subset_closedBall hz)
    exact sourcePsi_deletedRoot_avoids_otherCircle_of_isolatingDiscs
      hp hp1 φ Niso εiso (a : Coeff p) c R hcircle hrootloc
        hdisjoint m n hmn
  · exact analyticOnNhd_deletedPsi_gapRegularFactor_of_isolatingDisc
      hp hp1 φ Niso εiso n m a ψ W hpair.2 (hQdata m).2
        (c m) (R m) (hdom m) (hfilled m) (hrootloc n)
        (hdisjoint m n hmn)
  · exact sourcePsi_otherRoots_avoid_standardGap_of_isolatingDiscs
      hp hp1 φ ψ Niso εiso (a : Coeff p)
        (fun j => sourcePeriodicSegment_subset_isolatingDisc
          hp hp1 φ ψ Niso εiso j
            (hcluster (a,ψ) hpair.1 j))
        hrootloc hdisjoint m

end NLS.ZakharovShabat
