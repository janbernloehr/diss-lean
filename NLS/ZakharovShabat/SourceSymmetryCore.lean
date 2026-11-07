import NLS.ZakharovShabat.SourceReciprocalScaling
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Maps.Proper.Basic

/-! # An invariant open source neighborhood inside any almost-real neighborhood

Compactness of the unit circle makes the phase core open. Intersecting its
four P/T translates gives one open neighborhood of the entire real locus,
invariant under P, pure T and every real phase, inside the supplied domain.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceCircleRotation (c : Circle) (φ : CoeffPair p) : CoeffPair p :=
  sourceReciprocalScaling (c:ℂ) φ

@[simp] theorem sourceCircleRotation_one (φ : CoeffPair p) : sourceCircleRotation 1 φ = φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp [sourceCircleRotation]

@[simp] theorem sourceCircleRotation_mul (c d : Circle) (φ : CoeffPair p) :
    sourceCircleRotation c (sourceCircleRotation d φ) = sourceCircleRotation (c*d) φ := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp [sourceCircleRotation,mul_smul,mul_inv_rev,mul_comm]

theorem sourceComponentSwap_circleRotation (c : Circle) (φ : CoeffPair p) :
    sourceComponentSwap (sourceCircleRotation c φ) = sourceCircleRotation c⁻¹ (sourceComponentSwap φ) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp [sourceCircleRotation]

theorem sourceMidpointReflection_circleRotation (c : Circle) (φ : CoeffPair p) :
    sourceMidpointReflection (sourceCircleRotation c φ) = sourceCircleRotation c (sourceMidpointReflection φ) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> simp [sourceCircleRotation]

theorem sourceComponentSwap_midpointReflection (φ : CoeffPair p) :
    sourceComponentSwap (sourceMidpointReflection φ) = sourceMidpointReflection (sourceComponentSwap φ) := by
  apply (CoeffPair.toMax p).injective
  apply Prod.ext <;> rfl

theorem continuous_sourceCircleRotation :
    Continuous (fun q : Circle × CoeffPair p => sourceCircleRotation q.1 q.2) := by
  change Continuous (fun q : Circle × CoeffPair p =>
    (CoeffPair.toMax p).symm (((q.1:ℂ) • q.2.fst),((q.1:ℂ)⁻¹ • q.2.snd)))
  apply (CoeffPair.toMax p).symm.continuous.comp
  have hc : Continuous (fun q : Circle × CoeffPair p => (q.1:ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hd : Continuous (fun q : Circle × CoeffPair p => (q.1:ℂ)⁻¹) := by
    have hi : Continuous (fun q : Circle × CoeffPair p => q.1⁻¹) := continuous_fst.inv
    have hh : Continuous (fun q : Circle × CoeffPair p => ((q.1⁻¹ : Circle):ℂ)) :=
      continuous_subtype_val.comp hi
    simpa only [Circle.coe_inv] using hh
  exact (hc.smul ((CoeffPair.toMax p).continuous.fst.comp continuous_snd)).prodMk
    (hd.smul ((CoeffPair.toMax p).continuous.snd.comp continuous_snd))

private theorem realType_componentSwap (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p) :
    sourceComponentSwap φ ∈ realTypeSourceLocus p := by
  exact sourceComponentSwap_realType φ hφ

private theorem realType_midpointReflection (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p) :
    sourceMidpointReflection φ ∈ realTypeSourceLocus p := by
  intro n
  simpa using hφ (-n)

private theorem realType_circleRotation (c : Circle) (φ : CoeffPair p) (hφ : φ ∈ realTypeSourceLocus p) :
    sourceCircleRotation c φ ∈ realTypeSourceLocus p := by
  intro n
  change (c:ℂ)⁻¹*φ.snd n = conj ((c:ℂ)*φ.fst (-n))
  have h : φ.snd n = conj (φ.fst (-n)) := hφ n
  rw [h,map_mul,← Circle.coe_inv_eq_conj,Circle.coe_inv]

def sourceCircleCore (U : Set (CoeffPair p)) : Set (CoeffPair p) :=
  {φ | ∀ c : Circle, sourceCircleRotation c φ ∈ U}

theorem isOpen_sourceCircleCore (U : Set (CoeffPair p)) (hU : IsOpen U) :
    IsOpen (sourceCircleCore U) := by
  have hclosed : IsClosed {q : Circle × CoeffPair p | sourceCircleRotation q.1 q.2 ∉ U} :=
    hU.isClosed_compl.preimage continuous_sourceCircleRotation
  have hproj := isClosedMap_snd_of_compactSpace _ hclosed
  convert hproj.isOpen_compl using 1
  ext φ
  simp [sourceCircleCore,Set.mem_image,Prod.exists]

def sourceSymmetryCore (U : Set (CoeffPair p)) : Set (CoeffPair p) :=
  {φ | ∀ c : Circle,
    sourceCircleRotation c φ ∈ U ∧ sourceCircleRotation c (sourceComponentSwap φ) ∈ U ∧
    sourceCircleRotation c (sourceMidpointReflection φ) ∈ U ∧
    sourceCircleRotation c (sourceComponentSwap (sourceMidpointReflection φ)) ∈ U}

theorem isOpen_sourceSymmetryCore (U : Set (CoeffPair p)) (hU : IsOpen U) :
    IsOpen (sourceSymmetryCore U) := by
  have hc := isOpen_sourceCircleCore U hU
  have he : sourceSymmetryCore U =
      ((sourceCircleCore U ∩ sourceComponentSwap ⁻¹' sourceCircleCore U) ∩
        sourceMidpointReflection ⁻¹' sourceCircleCore U) ∩
        (fun φ => sourceComponentSwap (sourceMidpointReflection φ)) ⁻¹' sourceCircleCore U := by
    ext φ
    constructor
    · intro h
      exact ⟨⟨⟨fun c => (h c).1,fun c => (h c).2.1⟩,fun c => (h c).2.2.1⟩,fun c => (h c).2.2.2⟩
    · rintro ⟨⟨⟨h₁,h₂⟩,h₃⟩,h₄⟩ c
      exact ⟨h₁ c,h₂ c,h₃ c,h₄ c⟩
  rw [he]
  exact ((hc.inter (hc.preimage sourceComponentSwap.continuous)).inter
    (hc.preimage sourceMidpointReflection.continuous)).inter
      (hc.preimage (sourceComponentSwap.continuous.comp sourceMidpointReflection.continuous))

theorem sourceSymmetryCore_subset (U : Set (CoeffPair p)) : sourceSymmetryCore U ⊆ U := by
  intro φ hφ
  simpa only [sourceCircleRotation_one] using (hφ 1).1

theorem realTypeSourceLocus_subset_sourceSymmetryCore (U : Set (CoeffPair p))
    (hreal : realTypeSourceLocus p ⊆ U) : realTypeSourceLocus p ⊆ sourceSymmetryCore U := by
  intro φ hφ c
  exact ⟨hreal (realType_circleRotation c φ hφ),
    hreal (realType_circleRotation c _ (realType_componentSwap φ hφ)),
    hreal (realType_circleRotation c _ (realType_midpointReflection φ hφ)),
    hreal (realType_circleRotation c _ (realType_componentSwap _ (realType_midpointReflection φ hφ)))⟩

theorem sourceSymmetryCore_componentSwap (U : Set (CoeffPair p)) (φ : CoeffPair p)
    (hφ : φ ∈ sourceSymmetryCore U) : sourceComponentSwap φ ∈ sourceSymmetryCore U := by
  intro c
  simpa only [sourceComponentSwap_involutive,← sourceComponentSwap_midpointReflection] using
    And.intro (hφ c).2.1 (And.intro (hφ c).1 (And.intro (hφ c).2.2.2 (hφ c).2.2.1))

theorem sourceSymmetryCore_midpointReflection (U : Set (CoeffPair p)) (φ : CoeffPair p)
    (hφ : φ ∈ sourceSymmetryCore U) : sourceMidpointReflection φ ∈ sourceSymmetryCore U := by
  intro c
  simpa only [sourceMidpointReflection_involutive] using
    And.intro (hφ c).2.2.1 (And.intro (hφ c).2.2.2 (And.intro (hφ c).1 (hφ c).2.1))

theorem sourceSymmetryCore_circleRotation (U : Set (CoeffPair p)) (φ : CoeffPair p)
    (hφ : φ ∈ sourceSymmetryCore U) (d : Circle) : sourceCircleRotation d φ ∈ sourceSymmetryCore U := by
  intro c
  simpa only [sourceComponentSwap_circleRotation,sourceMidpointReflection_circleRotation,sourceCircleRotation_mul] using
    And.intro (hφ (c*d)).1 (And.intro (hφ (c*d⁻¹)).2.1
      (And.intro (hφ (c*d)).2.2.1 (hφ (c*d⁻¹)).2.2.2))

end NLS.ZakharovShabat
