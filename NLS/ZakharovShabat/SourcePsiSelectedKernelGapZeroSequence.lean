import NLS.ZakharovShabat.SourcePsiVariationGapZeroSequence
import NLS.ZakharovShabat.SourcePsiVariationOpenGapZero
import NLS.ZakharovShabat.SourcePsiVariationCollapsedGapZero
import NLS.ZakharovShabat.SourcePsiSelectedJacobianKernelRealImag
import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder
import NLS.ZakharovShabat.FiniteSourceRealization

/-!
# Gap-zero sequences from the selected psi-Jacobian kernel

At real source data, every periodic gap is either open or collapsed.
The two contour arguments give a zero of the numerator variation in
each retained gap. Applying them to the real and imaginary components
of a complex kernel direction produces two `ℓᵖ` spectral sequences,
ready for the interpolation argument.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourcePeriodicGap_eq_zero_or_open
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : IsRealType (CoeffPair.toMax p ψ))
    (m : ℤ) :
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m = 0 ∨
    (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) m).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) m).re := by
  let φ := periodOnePotential ψ
  let heven := periodOnePotential_mem ψ
  let l := canonicalPeriodicLeft hp hp1 φ heven m
  let r := canonicalPeriodicRight hp hp1 φ heven m
  have hle : l.re ≤ r.re :=
    re_le_of_complexLexLE ((canonicalPeriodicEndpoints_spec hp hp1 φ heven).2.1 m)
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  · left
    obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_im_eq_zero_of_realType
      hp hp1 φ heven (isRealType_periodOnePotential ψ hψ) m
    have he : l = r := Complex.ext heq (hl.trans hr.symm)
    change r - l = 0
    exact sub_eq_zero.mpr he.symm

/-- Rowwise open- and collapsed-gap contour results produce one
simultaneous `ℓᵖ` zero sequence for every real kernel direction. -/
theorem exists_sourcePsiSelectedJacobian_realKernel_gapZero_sequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (hcenter : ∀ m : ℤ, ∃ x : ℝ, c m = (x:ℂ))
    (hR : ∀ m : ℤ, 0 < R m)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m))
    (hdom : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (v : DeletedCoeff p n)
    (hvreal : ∀ j : ℤ, ((v : Coeff p) j).im = 0)
    (hvkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ v = 0) :
    ∃ ρ : ℤ → ℂ,
      Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ρ n = displacedRoots (a : Coeff p) n ∧
      ∀ m : ℤ, m ≠ n →
        ρ m ∈ sourcePeriodicSegment hp hp1 ψ m ∧
        sourcePsiCandidateVariation n (a : Coeff p)
          (v : Coeff p) (ρ m) = 0 := by
  apply exists_sourcePsiCandidateVariation_gapZero_sequence
    hp hp1 ψ n (a : Coeff p) (v : Coeff p)
  intro m hmn
  rcases sourcePeriodicGap_eq_zero_or_open hp hp1 ψ hψ m with hcollapsed | hopen
  · have hmidMem : sourceStandardRootMidpoint hp hp1 ψ m ∈
        sourcePeriodicSegment hp hp1 ψ m := by
      simpa only [sourceStandardRootMidpoint] using
        sourcePeriodicMidpoint_mem_segment hp hp1 ψ m
    have hmid : sourceStandardRootMidpoint hp hp1 ψ m ∈
        ball (c m) (R m) := hseg m hmidMem
    have hzero := sourcePsiSelectedJacobian_kernel_variation_zero_at_collapsedGap
      hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ
        m hmn hcollapsed (hR m) hmid (hdom m) (hcircle m)
        v hvkernel
    exact ⟨sourceStandardRootMidpoint hp hp1 ψ m,hmidMem,hzero⟩
  · obtain ⟨x,hx⟩ := hcenter m
    have hs : sourcePeriodicSegment hp hp1 ψ m ⊆ ball (x:ℂ) (R m) := by
      simpa only [hx] using hseg m
    have hd : closedBall (x:ℂ) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m := by
      simpa only [hx] using hdom m
    obtain ⟨μ,hμ,hzero⟩ :=
      exists_sourcePsiSelectedJacobian_kernel_variation_zero_on_openGap
        hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
          m hmn hopen x hx (hR m) hs hd (hcircle m)
          v hvreal hvkernel
    exact ⟨μ,sourceStandardRoot_gapSegment_subset_periodicSegment
      hp hp1 ψ m hμ,hzero⟩

/-- A complex selected-Jacobian kernel direction yields two `ℓᵖ`
interpolation sequences, one for each real component. -/
theorem exists_sourcePsiSelectedJacobian_complexKernel_gapZero_sequences
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (hrealSeq : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (hcenter : ∀ m : ℤ, ∃ x : ℝ, c m = (x:ℂ))
    (hR : ∀ m : ℤ, 0 < R m)
    (hseg : ∀ m : ℤ,
      sourcePeriodicSegment hp hp1 ψ m ⊆ ball (c m) (R m))
    (hdom : ∀ m : ℤ,
      closedBall (c m) (R m) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ m)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 ψ)
    (h : DeletedCoeff p n)
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    (∃ ρ : ℤ → ℂ,
      Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ρ n = displacedRoots (a : Coeff p) n ∧
      ∀ m : ℤ, m ≠ n →
        ρ m ∈ sourcePeriodicSegment hp hp1 ψ m ∧
        sourcePsiCandidateVariation n (a : Coeff p)
          (DeletedCoeff.realPart h : Coeff p) (ρ m) = 0) ∧
    (∃ ρ : ℤ → ℂ,
      Memℓp (fun m => ρ m-(Real.pi:ℂ)*m) p ∧
      ρ n = displacedRoots (a : Coeff p) n ∧
      ∀ m : ℤ, m ≠ n →
        ρ m ∈ sourcePeriodicSegment hp hp1 ψ m ∧
        sourcePsiCandidateVariation n (a : Coeff p)
          (DeletedCoeff.imagPart h : Coeff p) (ρ m) = 0) := by
  obtain ⟨hre,him⟩ := sourcePsiSelectedRootJacobian_kernel_realImag
    hp hp1 n c R U hUopen hdiff hrealSeq a ψ hpair hψ hroots
      h hkernel
  constructor
  · exact exists_sourcePsiSelectedJacobian_realKernel_gapZero_sequence
      hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
        hcenter hR hseg hdom hcircle
        (DeletedCoeff.realPart h) (DeletedCoeff.realPart_im_eq_zero h) hre
  · exact exists_sourcePsiSelectedJacobian_realKernel_gapZero_sequence
      hp hp1 n c R U hUopen hcoord hdiff a ψ hpair hψ hroots
        hcenter hR hseg hdom hcircle
        (DeletedCoeff.imagPart h) (DeletedCoeff.imagPart_im_eq_zero h) him

end NLS.ZakharovShabat
