import NLS.ZakharovShabat.SourcePsiC1ImplicitStep
import NLS.ZakharovShabat.SourcePsiConjugateRootEquivariance
import NLS.ZakharovShabat.SourcePsiEquationAllGapZero

/-!
# Real local implicit branches at arbitrary real psi solutions

The selected contour family is real-centered. At a real-type source,
conjugation sends any nearby solution to another solution. The complex
implicit theorem makes the solution locally unique, so the branch
remains real on the real-type locus. The all-gap zero theorem then
places its retained roots in the source periodic gaps.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- Every real zero in the retained-root domain has a local `C¹`
branch whose nearby real-type values have real roots in their gaps. -/
theorem exists_local_sourcePsi_C1_real_branch
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
          (a,ψ) ∈ U ∩ sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n →
          IsRealType (CoeffPair.toMax p ψ) →
          (∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) →
          sourcePsiSelectedEquationSequence hp hp1 n c R a ψ = 0 →
          ∃ s : CoeffPair p → DeletedCoeff p n,
            ContDiffAt ℂ 1 s ψ ∧ s ψ = a ∧
            ∀ᶠ χ in 𝓝 ψ,
              (s χ,χ) ∈ U ∩
                sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n ∧
              sourcePsiSelectedEquationSequence hp hp1 n c R (s χ) χ = 0 ∧
              (IsRealType (CoeffPair.toMax p χ) →
                (∀ j : ℤ, (displacedRoots (s χ : Coeff p) j).im = 0) ∧
                ∀ m : ℤ, m ≠ n →
                  displacedRoots (s χ : Coeff p) m ∈
                    sourcePeriodicSegment hp hp1 χ m) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,hcenter,hgeom,hcoord,_,_,hbranch⟩ :=
    exists_local_sourcePsi_C1_branch_unique hp hp1 φ hφ n a₀
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,?_⟩
  intro a ψ hmem hψ hroots hzero
  obtain ⟨s,V,hVopen,hVbase,hs,hsx,hunique,hsolution⟩ :=
    hbranch a ψ hmem hψ hroots hzero
  have haconj : NLS.DeletedCoeff.conj a = a := by
    apply Subtype.ext
    ext j
    have hj : ((a : Coeff p) j).im = 0 := by
      simpa [displacedRoots,Complex.mul_im] using hroots j
    simpa [NLS.DeletedCoeff.conj_apply] using
      (Complex.conj_eq_iff_im.mpr hj)
  have hconjCont : ContinuousAt
      (fun χ : CoeffPair p => (NLS.DeletedCoeff.conj (s χ),χ)) ψ := by
    have hc : ContinuousAt
        (fun χ : CoeffPair p => NLS.DeletedCoeff.conj (s χ)) ψ :=
      (NLS.DeletedCoeff.continuous_conj.continuousAt).comp hs.continuousAt
    exact hc.prodMk continuousAt_id
  have hconjmem : ∀ᶠ χ in 𝓝 ψ,
      (NLS.DeletedCoeff.conj (s χ),χ) ∈ U ∩ V := by
    apply hconjCont.eventually
    apply (hUopen.inter hVopen).mem_nhds
    simpa only [hsx,haconj] using
      (show (a,ψ) ∈ U ∩ V from ⟨hmem.1,hVbase⟩)
  refine ⟨s,hs,hsx,?_⟩
  filter_upwards [hsolution,hconjmem] with χ hsol hconj
  refine ⟨hsol.1,hsol.2,?_⟩
  intro hreal
  have hFconj := sourcePsiSelectedEquationSequence_conj_roots
    hp hp1 χ hreal n c R hcenter
      (fun j => (hgeom (s χ,χ) hsol.1.1 j).1)
      (fun j => (hgeom (s χ,χ) hsol.1.1 j).2.2.2)
      (s χ)
      (hcoord (s χ,χ) hsol.1.1)
      (hcoord (NLS.DeletedCoeff.conj (s χ),χ) hconj.1)
  have hzeroConj : sourcePsiSelectedEquationSequence hp hp1 n c R
      (NLS.DeletedCoeff.conj (s χ)) χ = 0 := by
    rw [hFconj,hsol.2,NLS.DeletedCoeff.conj_zero]
  have hfix : NLS.DeletedCoeff.conj (s χ) = s χ :=
    hunique _ χ hconj.2 hzeroConj
  have hrootReal (j : ℤ) : (((s χ : DeletedCoeff p n) : Coeff p) j).im = 0 := by
    have hcoordFix := congrArg
      (fun b : DeletedCoeff p n => (b : Coeff p) j) hfix
    exact Complex.conj_eq_iff_im.mp (by simpa using hcoordFix)
  have hdisplacedReal (j : ℤ) :
      (displacedRoots (s χ : Coeff p) j).im = 0 := by
    simp [displacedRoots,Complex.mul_im,hrootReal]
  have hrootloc : ∀ k : ℤ, k ≠ n →
      displacedRoots (s χ : Coeff p) k ∈
        sourceIsolatingDisc hp hp1 φ Niso εiso k := hsol.1.2
  have hgapRoots := retainedRoots_mem_periodicSegments_of_selectedEquation_zero
    hp hp1 φ χ hreal Niso εiso n (s χ) hdisplacedReal
      hrootloc hdisjoint c R hcenter
      (hgeom (s χ,χ) hsol.1.1) hfilled
      (hcoord (s χ,χ) hsol.1.1) hsol.2
  exact ⟨hdisplacedReal,hgapRoots⟩

end NLS.ZakharovShabat
