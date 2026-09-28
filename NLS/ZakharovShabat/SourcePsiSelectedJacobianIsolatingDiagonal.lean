import NLS.ZakharovShabat.SourcePsiSelectedJacobianDiagonalCompact
import NLS.ZakharovShabat.SourcePsiIsolatingRootSeparation

/-!
# Diagonal isomorphism from isolated selected roots

The scalar all-gap nonvanishing argument and the compact operator
decomposition now use one selected contour family. Pairwise disjoint
isolating discs supply the two root-separation hypotheses in every
retained row. The remaining explicit conditions are that the selected
contours lie inside their assigned discs and that the gap regular
factor is analytic on the selected closed discs.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- For a common locally selected contour family, isolating discs and
regular-factor analyticity make the diagonal part of the bounded psi
Jacobian bijective, while its off-diagonal part is compact. -/
theorem exists_local_sourcePsi_selectedJacobian_isolatingDiagonal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          (∀ j : ℤ, ‖(a : Coeff p) j‖ ≤ Real.pi/4) →
          ∀ φiso : CoeffPair p, ∀ N : ℕ, ∀ ε : ℝ,
            (∀ m : ℤ,
              sourcePeriodicSegment hp hp1 ψ m ⊆
                sourceIsolatingDisc hp hp1 φiso N ε m) →
            (∀ k : ℤ,
              displacedRoots (a : Coeff p) k ∈
                sourceIsolatingDisc hp hp1 φiso N ε k) →
            (∀ m k : ℤ, m ≠ k →
              Disjoint (sourceIsolatingDisc hp hp1 φiso N ε m)
                (sourceIsolatingDisc hp hp1 φiso N ε k)) →
            (∀ m : ℤ,
              sphere (c m) (R m) ⊆
                sourceIsolatingDisc hp hp1 φiso N ε m) →
            (∀ m : ℤ, m ≠ n →
              AnalyticOnNhd ℂ
                (fun z => (((n-m : ℤ) : ℂ) *
                  sourcePsiGapRegularFactor hp hp1 n m (a : Coeff p) ψ z))
                (closedBall (c m) (R m))) →
            let Q : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
            let d : Coeff ⊤ := Coeff.deletedJacobianDiagonalSymbol n Q
            let D : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              Coeff.deletedMultiplierCLM n d
            let C : DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
              Coeff.deletedJacobianOffDiagonal n Q
            IsCompactOperator C ∧ Function.Bijective D ∧ Q = D + C := by
  obtain ⟨U,hUopen,hbase,c,R,hmain⟩ :=
    exists_local_sourcePsi_selectedJacobian_diagonalPlusCompact
      hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,?_⟩
  intro a ψ hpair hreal hroots hloc φiso N ε hseg hrootloc hdisjoint
    hcircle hreg
  obtain ⟨L,htail,hcompact,hbij,hnonzero,hsplit⟩ :=
    hmain a ψ hpair hreal hroots hloc
  refine ⟨hcompact,?_,hsplit⟩
  apply hbij
  intro m hmn _
  apply hnonzero m hmn
  · exact sourcePsi_deletedRoot_avoids_otherCircle_of_isolatingDiscs
      hp hp1 φiso N ε (a : Coeff p) c R hcircle hrootloc
        hdisjoint m n hmn
  · exact hreg m hmn
  · exact sourcePsi_otherRoots_avoid_standardGap_of_isolatingDiscs
      hp hp1 φiso ψ N ε (a : Coeff p) hseg hrootloc hdisjoint m

end NLS.ZakharovShabat
