import NLS.ZakharovShabat.SourcePsiRealContourComparison
import NLS.ZakharovShabat.SourcePsiGapRootLimitPlacement
import NLS.ZakharovShabat.SourcePsiLocalJacobianBijectivity
import NLS.ZakharovShabat.SourcePsiC1ImplicitStep
import NLS.ZakharovShabat.SourcePsiConjugateRootEquivariance
import NLS.ZakharovShabat.SourcePsiEquationAllGapZero

/-!
# Limits of real gap-contained psi solutions

The compactness theorem extracts a strong limit of deleted roots when
the real-type source potentials converge. A local selected contour
chart centered at that limit is `C¹`. Real-centered contour invariance
transfers the zero equation from each original, potentially different,
valid contour family to this fixed chart. Continuity then proves that
the limiting deleted roots solve its equation. Root placement makes the
Jacobian invertible there, yielding a locally unique `C¹` branch.
For nearby real-type sources, conjugation and the gap-zero theorem keep
the branch real and gap-contained.
Contour invariance also makes the branch locally unique among zeros
written in any other valid real-centered contour family.
-/

noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat

/-- A converging sequence of real-type sources with gap-contained
deleted roots solving valid real-centered selected equations has a
strongly convergent subsequence whose gap-contained limit solves a
local selected equation in a `C¹` chart with bijective root Jacobian
and a locally unique implicit branch whose nearby real-type values
remain in the periodic gaps. Local uniqueness is independent of the
valid real-centered contour family used to express a nearby zero. -/
theorem exists_limit_sourcePsi_gap_solution
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (ψ : ℕ → CoeffPair p) (hψ : Tendsto ψ atTop (𝓝 φ))
    (hreal : ∀ k, IsRealType (CoeffPair.toMax p (ψ k)))
    (n : ℤ) (a : ℕ → DeletedCoeff p n)
    (hgap : ∀ k : ℕ, ∀ m : ℤ, m ≠ n →
      displacedRoots (a k : Coeff p) m ∈
        sourcePeriodicSegment hp hp1 (ψ k) m)
    (c : ℕ → ℤ → ℂ) (R : ℕ → ℤ → ℝ)
    (hcenter : ∀ k m, (c k m).im = 0)
    (hgeom : ∀ k m,
      0 < R k m ∧
      sourcePeriodicSegment hp hp1 (ψ k) m ⊆
        ball (c k m) (R k m) ∧
      closedBall (c k m) (R k m) ⊆
        sourceStandardRootOmittedDomain hp hp1 (ψ k) m)
    (hcoord : ∀ k m,
      (sourcePsiSelectedEquationSequence hp hp1 n (c k) (R k)
        (a k) (ψ k) : Coeff p) m =
          sourcePsiEquationCoordinate hp hp1 n m
            (a k : Coeff p) (ψ k) (c k m) (R k m))
    (hzero : ∀ k,
      sourcePsiSelectedEquationSequence hp hp1 n (c k) (R k)
        (a k) (ψ k) = 0) :
    ∃ b : DeletedCoeff p n, ∃ σ : ℕ → ℕ,
      ∃ U : Set (DeletedCoeff p n × CoeffPair p),
      ∃ c₀ : ℤ → ℂ, ∃ R₀ : ℤ → ℝ,
        StrictMono σ ∧ Tendsto (a ∘ σ) atTop (𝓝 b) ∧
        (∀ m : ℤ, m ≠ n →
          displacedRoots (b : Coeff p) m ∈
            sourcePeriodicSegment hp hp1 φ m) ∧
        IsOpen U ∧ (b,φ) ∈ U ∧
        ContDiffOn ℂ 1
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2) U ∧
        sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ b φ = 0 ∧
        Function.Bijective
          (sourcePsiSelectedRootJacobian hp hp1 n c₀ R₀ b φ) ∧
        ∃ s : CoeffPair p → DeletedCoeff p n,
          ∃ V : Set (DeletedCoeff p n × CoeffPair p),
            IsOpen V ∧ (b,φ) ∈ V ∧
            ContDiffAt ℂ 1 s φ ∧ s φ = b ∧
            (∀ b' : DeletedCoeff p n, ∀ χ : CoeffPair p,
              (b',χ) ∈ V →
              sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ b' χ = 0 →
              b' = s χ) ∧
            (∀ b' : DeletedCoeff p n, ∀ χ : CoeffPair p,
              ∀ c' : ℤ → ℂ, ∀ R' : ℤ → ℝ,
              (b',χ) ∈ U ∩ V →
              IsRealType (CoeffPair.toMax p χ) →
              (∀ m, (c' m).im = 0) →
              (∀ m, 0 < R' m ∧
                sourcePeriodicSegment hp hp1 χ m ⊆ ball (c' m) (R' m) ∧
                closedBall (c' m) (R' m) ⊆
                  sourceStandardRootOmittedDomain hp hp1 χ m) →
              (∀ m,
                (sourcePsiSelectedEquationSequence hp hp1 n c' R' b' χ : Coeff p) m =
                  sourcePsiEquationCoordinate hp hp1 n m
                    (b' : Coeff p) χ (c' m) (R' m)) →
              sourcePsiSelectedEquationSequence hp hp1 n c' R' b' χ = 0 →
              b' = s χ) ∧
            ∀ᶠ χ in 𝓝 φ,
              sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ (s χ) χ = 0 ∧
              (IsRealType (CoeffPair.toMax p χ) →
                (∀ j : ℤ, (displacedRoots (s χ : Coeff p) j).im = 0) ∧
                ∀ m : ℤ, m ≠ n →
                  displacedRoots (s χ : Coeff p) m ∈
                    sourcePeriodicSegment hp hp1 χ m) := by
  obtain ⟨b,σ,hσ,hb,hbgap⟩ :=
    exists_tendsto_subseq_deletedGapRoots_mem_limit_segments
      hp hp1 φ hφ ψ hψ n a hgap
  obtain ⟨U,hUopen,hbase,c₀,R₀,Niso,εiso,
      hdisjoint,hfilled,hcenter₀,hgeom₀,hcoord₀,hC1,hbij⟩ :=
    exists_local_sourcePsi_selectedJacobian_bijective hp hp1 φ hφ n b
  have hψσ : Tendsto (ψ ∘ σ) atTop (𝓝 φ) :=
    hψ.comp hσ.tendsto_atTop
  have hpair : Tendsto
      (fun k => (a (σ k),ψ (σ k))) atTop (𝓝 (b,φ)) :=
    hb.prodMk_nhds hψσ
  have hUevent : ∀ᶠ k : ℕ in atTop,
      (a (σ k),ψ (σ k)) ∈ U :=
    hpair.eventually (hUopen.mem_nhds hbase)
  have hzero₀ : ∀ᶠ k : ℕ in atTop,
      sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀
        (a (σ k)) (ψ (σ k)) = 0 := by
    filter_upwards [hUevent] with k hk
    have hEq :=
      sourcePsiSelectedEquationSequence_eq_of_realCentered_enclosingCircles
        hp hp1 n (a (σ k)) (ψ (σ k)) (hreal (σ k))
        c₀ (c (σ k)) R₀ (R (σ k))
        hcenter₀ (hcenter (σ k))
        (fun m => (hgeom₀ (a (σ k),ψ (σ k)) hk m).1)
        (fun m => (hgeom (σ k) m).1)
        (fun m => (hgeom₀ (a (σ k),ψ (σ k)) hk m).2.1)
        (fun m => (hgeom (σ k) m).2.1)
        (fun m => (hgeom₀ (a (σ k),ψ (σ k)) hk m).2.2.1)
        (fun m => (hgeom (σ k) m).2.2)
        (hcoord₀ (a (σ k),ψ (σ k)) hk)
        (hcoord (σ k))
    exact hEq.trans (hzero (σ k))
  have hlimitZero :
      sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ b φ = 0 :=
    sourcePsiSelectedEquationSequence_zero_of_tendsto
      hp hp1 n c₀ R₀ U hUopen hC1
      (a ∘ σ) (ψ ∘ σ) b φ hb hψσ hbase hzero₀
  have hroots : ∀ j : ℤ,
      (displacedRoots (b : Coeff p) j).im = 0 := by
    intro j
    by_cases hj : j = n
    · subst j
      have hz : (b : Coeff p) n = 0 := b.property
      simp [displacedRoots,hz]
    · exact sourcePeriodicSegment_im_eq_zero_of_realType
        hp hp1 φ hφ j _ (hbgap j hj)
  have hrootloc : ∀ j : ℤ, j ≠ n →
      displacedRoots (b : Coeff p) j ∈
        sourceIsolatingDisc hp hp1 φ Niso εiso j := by
    intro j hj
    have hball := (hgeom₀ (b,φ) hbase j).2.1 (hbgap j hj)
    exact hfilled j (ball_subset_closedBall hball)
  have hbijAt : Function.Bijective
      (sourcePsiSelectedRootJacobian hp hp1 n c₀ R₀ b φ) :=
    hbij b φ hbase hφ hroots hrootloc
  have hF : ContDiffAt ℂ 1
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ t.1 t.2)
      (b,φ) := hC1.contDiffAt (hUopen.mem_nhds hbase)
  obtain ⟨s,V,hVopen,hVbase,hs,hsb,hunique,hzeros⟩ :=
    exists_C1_sourcePsi_local_solution_unique
      hp hp1 n c₀ R₀ b φ hF hlimitZero hbijAt
  have hbasePlacement : (b,φ) ∈
      sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n := hrootloc
  have hplacement : ∀ᶠ χ in 𝓝 φ,
      (s χ,χ) ∈ U ∩
        sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n := by
    have hcontinuous : ContinuousAt
        (fun χ : CoeffPair p => (s χ,χ)) φ :=
      hs.continuousAt.prodMk continuousAt_id
    apply hcontinuous.eventually
    apply (hUopen.inter (isOpen_sourcePsiRootPlacementDomain
      hp hp1 φ Niso εiso n)).mem_nhds
    simpa only [hsb] using
      (show (b,φ) ∈ U ∩
        sourcePsiRootPlacementDomain hp hp1 φ Niso εiso n from
        ⟨hbase,hbasePlacement⟩)
  have hbconj : NLS.DeletedCoeff.conj b = b := by
    apply Subtype.ext
    ext j
    have hj : ((b : Coeff p) j).im = 0 := by
      simpa [displacedRoots,Complex.mul_im] using hroots j
    simpa [NLS.DeletedCoeff.conj_apply] using
      (Complex.conj_eq_iff_im.mpr hj)
  have hconjCont : ContinuousAt
      (fun χ : CoeffPair p => (NLS.DeletedCoeff.conj (s χ),χ)) φ := by
    have hc : ContinuousAt
        (fun χ : CoeffPair p => NLS.DeletedCoeff.conj (s χ)) φ :=
      (NLS.DeletedCoeff.continuous_conj.continuousAt).comp hs.continuousAt
    exact hc.prodMk continuousAt_id
  have hconjmem : ∀ᶠ χ in 𝓝 φ,
      (NLS.DeletedCoeff.conj (s χ),χ) ∈ U ∩ V := by
    apply hconjCont.eventually
    apply (hUopen.inter hVopen).mem_nhds
    simpa only [hsb,hbconj] using
      (show (b,φ) ∈ U ∩ V from ⟨hbase,hVbase⟩)
  have hrealGap : ∀ᶠ χ in 𝓝 φ,
      sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀ (s χ) χ = 0 ∧
      (IsRealType (CoeffPair.toMax p χ) →
        (∀ j : ℤ, (displacedRoots (s χ : Coeff p) j).im = 0) ∧
        ∀ m : ℤ, m ≠ n →
          displacedRoots (s χ : Coeff p) m ∈
            sourcePeriodicSegment hp hp1 χ m) := by
    filter_upwards [hzeros,hplacement,hconjmem] with χ hzeroχ hplace hconj
    refine ⟨hzeroχ,?_⟩
    intro hreal
    have hFconj := sourcePsiSelectedEquationSequence_conj_roots
      hp hp1 χ hreal n c₀ R₀ hcenter₀
        (fun j => (hgeom₀ (s χ,χ) hplace.1 j).1)
        (fun j => (hgeom₀ (s χ,χ) hplace.1 j).2.2.2)
        (s χ)
        (hcoord₀ (s χ,χ) hplace.1)
        (hcoord₀ (NLS.DeletedCoeff.conj (s χ),χ) hconj.1)
    have hzeroConj : sourcePsiSelectedEquationSequence hp hp1 n c₀ R₀
        (NLS.DeletedCoeff.conj (s χ)) χ = 0 := by
      rw [hFconj,hzeroχ,NLS.DeletedCoeff.conj_zero]
    have hfix : NLS.DeletedCoeff.conj (s χ) = s χ :=
      hunique _ χ hconj.2 hzeroConj
    have hrootReal (j : ℤ) : (((s χ : DeletedCoeff p n) : Coeff p) j).im = 0 := by
      have hcoordFix := congrArg
        (fun a : DeletedCoeff p n => (a : Coeff p) j) hfix
      exact Complex.conj_eq_iff_im.mp (by simpa using hcoordFix)
    have hdisplacedReal (j : ℤ) :
        (displacedRoots (s χ : Coeff p) j).im = 0 := by
      simp [displacedRoots,Complex.mul_im,hrootReal]
    have hrootlocχ : ∀ k : ℤ, k ≠ n →
        displacedRoots (s χ : Coeff p) k ∈
          sourceIsolatingDisc hp hp1 φ Niso εiso k := hplace.2
    have hgapRoots := retainedRoots_mem_periodicSegments_of_selectedEquation_zero
      hp hp1 φ χ hreal Niso εiso n (s χ) hdisplacedReal
        hrootlocχ hdisjoint c₀ R₀ hcenter₀
        (hgeom₀ (s χ,χ) hplace.1) hfilled
        (hcoord₀ (s χ,χ) hplace.1) hzeroχ
    exact ⟨hdisplacedReal,hgapRoots⟩
  have hchartUnique : ∀ b' : DeletedCoeff p n, ∀ χ : CoeffPair p,
      ∀ c' : ℤ → ℂ, ∀ R' : ℤ → ℝ,
      (b',χ) ∈ U ∩ V →
      IsRealType (CoeffPair.toMax p χ) →
      (∀ m, (c' m).im = 0) →
      (∀ m, 0 < R' m ∧
        sourcePeriodicSegment hp hp1 χ m ⊆ ball (c' m) (R' m) ∧
        closedBall (c' m) (R' m) ⊆
          sourceStandardRootOmittedDomain hp hp1 χ m) →
      (∀ m,
        (sourcePsiSelectedEquationSequence hp hp1 n c' R' b' χ : Coeff p) m =
          sourcePsiEquationCoordinate hp hp1 n m
            (b' : Coeff p) χ (c' m) (R' m)) →
      sourcePsiSelectedEquationSequence hp hp1 n c' R' b' χ = 0 →
      b' = s χ := by
    intro b' χ c' R' hmem hreal hcenter' hgeom' hcoord' hzero'
    have hEq :=
      sourcePsiSelectedEquationSequence_eq_of_realCentered_enclosingCircles
        hp hp1 n b' χ hreal c₀ c' R₀ R'
        hcenter₀ hcenter'
        (fun m => (hgeom₀ (b',χ) hmem.1 m).1)
        (fun m => (hgeom' m).1)
        (fun m => (hgeom₀ (b',χ) hmem.1 m).2.1)
        (fun m => (hgeom' m).2.1)
        (fun m => (hgeom₀ (b',χ) hmem.1 m).2.2.1)
        (fun m => (hgeom' m).2.2)
        (hcoord₀ (b',χ) hmem.1) hcoord'
    exact hunique b' χ hmem.2 (hEq.trans hzero')
  exact ⟨b,σ,U,c₀,R₀,hσ,hb,hbgap,hUopen,hbase,hC1,
    hlimitZero,hbijAt,s,V,hVopen,hVbase,hs,hsb,hunique,hchartUnique,hrealGap⟩

end NLS.ZakharovShabat
