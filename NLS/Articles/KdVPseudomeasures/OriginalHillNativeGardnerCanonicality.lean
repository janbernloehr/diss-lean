import NLS.Articles.KdVPseudomeasures.OriginalHillNativeOpenGardner
import NLS.KdV.HillRealOpenGapDensity

/-! The ACTUAL signed-coordinate Gardner matrix at every physical real
mean-zero source, including all collapsed gaps. The joint open selected
gap locus is dense in the real Banach source; full native bracket
continuity extends the proved matrix without finite-gap density. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem continuous_hillRealNativeGardnerBracket (k l : ℤ) :
    Continuous (fun q : HillRealMeanZeroSource => hillHminusNativeGardnerBracket k l (hillRealMeanZeroInclusion q)) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hr : IsRealPeriodOneHminusOne (hillRealMeanZeroInclusion q) := q.property
  have ha : ContinuousAt (hillHminusNativeGardnerBracket k l) (hillRealMeanZeroInclusion q) :=
    (analyticOnNhd_hillHminusNativeGardnerBracket k l _
      (real_mem_hillHminusActionAngleNativeDomain _ hr)).continuousAt
  exact ha.comp hillRealMeanZeroInclusion.continuous.continuousAt

theorem hillRealNativeGardner_canonical_matrix (n m : ℕ+) (q : HillRealMeanZeroSource) :
    hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) (hillRealMeanZeroInclusion q)=0 ∧
    hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) (hillRealMeanZeroInclusion q)=0 ∧
    hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) (hillRealMeanZeroInclusion q)=if n=m then I else 0 := by
  classical
  let f : HillRealMeanZeroSource → ℂ × ℂ × ℂ := fun r =>
    (hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) (hillRealMeanZeroInclusion r),
     hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) (hillRealMeanZeroInclusion r),
     hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) (hillRealMeanZeroInclusion r))
  have hf : Continuous f := (continuous_hillRealNativeGardnerBracket (n:ℤ) (m:ℤ)).prodMk
    ((continuous_hillRealNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ))).prodMk
      (continuous_hillRealNativeGardnerBracket (n:ℤ) (-(m:ℤ))))
  let Z : Set HillRealMeanZeroSource := {r | f r=(0,0,if n=m then I else 0)}
  have hZ : IsClosed Z := isClosed_eq hf continuous_const
  have hd := dense_hillReal_finitely_many_open_gaps ({n,m} : Finset ℕ+)
  have hsub : {r : HillRealMeanZeroSource | ∀ j ∈ ({n,m} : Finset ℕ+),
      hillHminusCanonicalGapSquare j r.val.val ≠ 0} ⊆ Z := by
    intro r hr
    have hn : hillHminusCanonicalGapSquare n (originalPeriodOneCoefficients (originalHillPotentialOfRealSource r)) ≠ 0 := by
      rw [originalHillPotentialOfRealSource_coefficients]
      exact hr n (by simp)
    have hm : hillHminusCanonicalGapSquare m (originalPeriodOneCoefficients (originalHillPotentialOfRealSource r)) ≠ 0 := by
      rw [originalHillPotentialOfRealSource_coefficients]
      exact hr m (by simp)
    have he := original_Hill_native_Gardner_open_matrix n m (originalHillPotentialOfRealSource r) hn hm
    rw [originalHillPotentialOfRealSource_coefficients] at he
    exact Prod.ext he.1 (Prod.ext he.2.1 he.2.2)
  have he : q ∈ Z := closure_minimal hsub hZ (hd q)
  change f q=(0,0,if n=m then I else 0) at he
  exact ⟨congrArg (fun z : ℂ × ℂ × ℂ => z.1) he,
    congrArg (fun z : ℂ × ℂ × ℂ => z.2.1) he,congrArg (fun z : ℂ × ℂ × ℂ => z.2.2) he⟩

theorem original_Hill_native_Gardner_canonical_matrix (n m : ℕ+) (q : OriginalHminusOnePotential) :
    hillHminusNativeGardnerBracket (n:ℤ) (m:ℤ) (originalPeriodOneCoefficients q)=0 ∧
    hillHminusNativeGardnerBracket (-(n:ℤ)) (-(m:ℤ)) (originalPeriodOneCoefficients q)=0 ∧
    hillHminusNativeGardnerBracket (n:ℤ) (-(m:ℤ)) (originalPeriodOneCoefficients q)=if n=m then I else 0 :=
  hillRealNativeGardner_canonical_matrix n m (originalHillRealMeanZeroSource q)

end NLS.Articles.KdVPseudomeasures
