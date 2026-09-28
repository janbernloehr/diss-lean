import NLS.ZakharovShabat.SourcePsiFreeInitialSolution
import NLS.ZakharovShabat.SourcePsiConjugateRootEquivariance
import NLS.ZakharovShabat.SourcePsiEquationAllGapZero

/-!
# Reality of the local psi branch at the free potential

Conjugating a solution at a real-type potential gives another solution
on the same real-centered contour family. Both solutions lie near the
free pair, so local uniqueness from the complex `C¹` implicit theorem
identifies them. Every retained root displacement is therefore real.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- The local branch seeded at the free potential has real retained
roots for every sufficiently nearby real-type potential. -/
theorem exists_local_sourcePsi_C1_real_branch_at_free_source
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      ((0 : DeletedCoeff p n),(0 : CoeffPair p)) ∈ U ∧
      ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        ∃ Niso : ℕ, ∃ εiso : ℝ,
        ∃ s : CoeffPair p → DeletedCoeff p n,
          ContDiffAt ℂ 1 s 0 ∧ s 0 = 0 ∧
          ∀ᶠ ψ in 𝓝 (0 : CoeffPair p),
            (s ψ,ψ) ∈ U ∩
              sourcePsiRootPlacementDomain hp hp1
                (0 : CoeffPair p) Niso εiso n ∧
            sourcePsiSelectedEquationSequence hp hp1 n c R (s ψ) ψ = 0 ∧
            (IsRealType (CoeffPair.toMax p ψ) →
              (∀ m : ℤ,
                (((s ψ : DeletedCoeff p n) : Coeff p) m).im = 0) ∧
              ∀ m : ℤ, m ≠ n →
                displacedRoots (s ψ : Coeff p) m ∈
                  sourcePeriodicSegment hp hp1 ψ m) := by
  obtain ⟨U,hUopen,hbase,c,R,Niso,εiso,
      hdisjoint,hfilled,hcenter,hgeom,hcoord,s,V,hVopen,hVbase,
      hs,hs0,hunique,hsolution⟩ :=
    exists_local_sourcePsi_C1_branch_at_free_source hp hp1 n
  have hconjCont : ContinuousAt
      (fun ψ : CoeffPair p => (NLS.DeletedCoeff.conj (s ψ),ψ)) 0 := by
    have hc : ContinuousAt
        (fun ψ : CoeffPair p => NLS.DeletedCoeff.conj (s ψ)) 0 :=
      (NLS.DeletedCoeff.continuous_conj.continuousAt).comp hs.continuousAt
    exact hc.prodMk continuousAt_id
  have hconjmem : ∀ᶠ ψ in 𝓝 (0 : CoeffPair p),
      (NLS.DeletedCoeff.conj (s ψ),ψ) ∈ U ∩ V := by
    apply hconjCont.eventually
    apply (hUopen.inter hVopen).mem_nhds
    simpa only [hs0,NLS.DeletedCoeff.conj_zero] using
      (show ((0 : DeletedCoeff p n),(0 : CoeffPair p)) ∈ U ∩ V from
        ⟨hbase,hVbase⟩)
  refine ⟨U,hUopen,hbase,c,R,Niso,εiso,s,hs,hs0,?_⟩
  filter_upwards [hsolution,hconjmem] with ψ hsol hconj
  refine ⟨hsol.1,hsol.2,?_⟩
  intro hreal
  have hFconj := sourcePsiSelectedEquationSequence_conj_roots
    hp hp1 ψ hreal n c R hcenter
      (fun j => (hgeom (s ψ,ψ) hsol.1.1 j).1)
      (fun j => (hgeom (s ψ,ψ) hsol.1.1 j).2.2.2)
      (s ψ)
      (hcoord (s ψ,ψ) hsol.1.1)
      (hcoord (NLS.DeletedCoeff.conj (s ψ),ψ) hconj.1)
  have hzeroConj : sourcePsiSelectedEquationSequence hp hp1 n c R
      (NLS.DeletedCoeff.conj (s ψ)) ψ = 0 := by
    rw [hFconj,hsol.2,NLS.DeletedCoeff.conj_zero]
  have hfix : NLS.DeletedCoeff.conj (s ψ) = s ψ :=
    hunique _ ψ hconj.2 hzeroConj
  have hrootReal (m : ℤ) : (((s ψ : DeletedCoeff p n) : Coeff p) m).im = 0 := by
    have hcoordFix := congrArg
      (fun b : DeletedCoeff p n => (b : Coeff p) m) hfix
    exact Complex.conj_eq_iff_im.mp (by simpa using hcoordFix)
  have hdisplacedReal (m : ℤ) :
      (displacedRoots (s ψ : Coeff p) m).im = 0 := by
    simp [displacedRoots,Complex.mul_im,hrootReal]
  have hrootloc : ∀ k : ℤ, k ≠ n →
      displacedRoots (s ψ : Coeff p) k ∈
        sourceIsolatingDisc hp hp1 0 Niso εiso k := hsol.1.2
  have hgapRoots := retainedRoots_mem_periodicSegments_of_selectedEquation_zero
    hp hp1 0 ψ hreal Niso εiso n (s ψ) hdisplacedReal
      hrootloc hdisjoint c R hcenter
      (hgeom (s ψ,ψ) hsol.1.1) hfilled
      (hcoord (s ψ,ψ) hsol.1.1) hsol.2
  exact ⟨hrootReal,hgapRoots⟩

end NLS.ZakharovShabat
