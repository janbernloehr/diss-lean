import NLS.ZakharovShabat.SourcePsiIsolatingComplexNormalization
import NLS.ZakharovShabat.SourcePsiLemma12_10

/-!
# Lemma 12.11 on the common complex psi neighborhood

Construct the all-index root atlas inside both the actual spectral
isolation neighborhood and the domain of the jointly analytic quotient.
The local assigned circles have exact Kronecker periods throughout
their complex source balls. Their union is the same open simply
connected neighborhood for every deleted index, retaining all of
Lemma 12.10's root placement and real agreement. The literal omitted
raw integral is exactly 2 pi everywhere on this common domain.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The common analytic psi extension with its full contour
orthogonality, including the omitted index. At each complex source one
valid all-index circle family works simultaneously for all numerators. -/
structure SourcePsiNormalizedComplexExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop
    extends SourcePsiIsolatingComplexExtension hp hp1 W s where
  contour_orthogonality : ∀ ψ ∈ W, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
    sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ n m, sourcePsiContour hp hp1 n (s n ψ : Coeff p) ψ (c m) (R m) =
        if m = n then 1 else 0

/-- Source-space Lemma 12.11, preserving the common source domain,
analytic branches, and actual isolating root placement of Lemma 12.10. -/
theorem exists_sourcePsi_lemma12_11 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ U W : Set (CoeffPair p), SourceSpectralIsolationNeighborhood hp hp1 U ∧
      IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ U ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiNormalizedComplexExtension hp hp1 W s := by
  obtain ⟨U,hU,hUconn,hreal,hgeometry⟩ := exists_global_source_isolating_neighborhood hp hp1
  obtain ⟨V,hV,_,hVreal,hdata⟩ := exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  obtain ⟨A⟩ := nonempty_sourcePsiIsolatingComplexRootAtlas hp hp1 (U ∩ V)
    (hU.inter hV) (fun φ hφ => ⟨hreal hφ,hVreal hφ⟩)
  let B := A.toSourcePsiComplexRootAtlas
  refine ⟨U,B.domain,⟨hU,hUconn,hreal,hgeometry⟩,B.isOpen_domain,
    B.isSimplyConnected_domain,B.realType_subset_domain,
    A.domain_subset.trans inter_subset_left,B.branch,{
      toSourcePsiIsolatingComplexExtension := {
        analytic := B.analytic,
        real_agreement := B.eq_sourcePsiGapRoot_of_real,
        contour_zero := B.contour_zero,
        isolation := ?_
      },
      contour_orthogonality := fun ψ hψ => A.contour_orthogonality V inter_subset_right hdata ψ hψ
    }⟩
  intro φ
  exact ⟨(B.localBranch φ).sourceRadius,(B.localBranch φ).sourceRadius_pos,
    A.cutoff φ,A.enlargement φ,A.enlargement_pos φ,A.enlargement_le φ,
    subset_iUnion B.sourceBall φ,A.clusters φ,A.disjoint φ,A.global_placement φ,A.filled_placement φ⟩

namespace SourcePsiNormalizedComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Literal raw contour orthogonality on the common complex domain,
with the dissertation's normalization and orientation. -/
theorem raw_contour_orthogonality (hs : SourcePsiNormalizedComplexExtension hp hp1 W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ n m, (∮ z in C(c m,R m),
        sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ : Coeff p),ψ))) =
          (2*Real.pi : ℂ)*(if m = n then 1 else 0) := by
  obtain ⟨c,R,hfamily,hperiod⟩ := hs.contour_orthogonality ψ hψ
  refine ⟨c,R,hfamily,?_⟩
  intro n m
  have hπ : (2*Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hnorm := hperiod n m
  unfold sourcePsiContour at hnorm
  have h := congrArg (fun w : ℂ => (2*Real.pi : ℂ)*w) hnorm
  simpa only [← mul_assoc,mul_inv_cancel₀ hπ,one_mul] using h

/-- Every omitted raw period is exactly 2 pi at every source in W. -/
theorem raw_omitted_contour (hs : SourcePsiNormalizedComplexExtension hp hp1 W s)
    (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
      sphere c R ⊆ sourceCanonicalRootDomain hp hp1 ψ ∧
      (∮ z in C(c,R), sourcePsiContourIntegrandJoint hp hp1 n (z,((s n ψ : Coeff p),ψ))) =
        (2*Real.pi : ℂ) := by
  obtain ⟨c,R,hfamily,hraw⟩ := hs.raw_contour_orthogonality ψ hψ
  exact ⟨c n,R n,(hfamily.2 n).1,(hfamily.2 n).2.1,(hfamily.2 n).2.2.1,
    (hfamily.2 n).2.2.2,by simpa using hraw n n⟩

end SourcePsiNormalizedComplexExtension
end NLS.ZakharovShabat
