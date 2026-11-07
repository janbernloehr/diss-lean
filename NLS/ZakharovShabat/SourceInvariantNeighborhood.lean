import NLS.ZakharovShabat.SourceSymmetryCore
import NLS.ZakharovShabat.SourceFullAbelianDifferentialData
import NLS.ZakharovShabat.SourceRealTypeConvex

/-! # A common connected invariant almost-real source neighborhood

Taking the zero component of the compact phase core preserves the entire
connected real form. Its exact invariance supports the original root and
primitive interfaces on one common source neighborhood.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceConnectedSymmetryCore (U : Set (CoeffPair p)) : Set (CoeffPair p) :=
  connectedComponentIn (sourceSymmetryCore U) 0

theorem sourceConnectedSymmetryCore_subset (U : Set (CoeffPair p)) :
    sourceConnectedSymmetryCore U ⊆ U :=
  (connectedComponentIn_subset _ _).trans (sourceSymmetryCore_subset U)

theorem isOpen_sourceConnectedSymmetryCore (U : Set (CoeffPair p)) (hU : IsOpen U) :
    IsOpen (sourceConnectedSymmetryCore U) := (isOpen_sourceSymmetryCore U hU).connectedComponentIn

theorem realTypeSourceLocus_subset_sourceConnectedSymmetryCore (U : Set (CoeffPair p))
    (hreal : realTypeSourceLocus p ⊆ U) : realTypeSourceLocus p ⊆ sourceConnectedSymmetryCore U :=
  isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn
    (by simp [realTypeSourceLocus]) (realTypeSourceLocus_subset_sourceSymmetryCore U hreal)

theorem isConnected_sourceConnectedSymmetryCore (U : Set (CoeffPair p))
    (hreal : realTypeSourceLocus p ⊆ U) : IsConnected (sourceConnectedSymmetryCore U) :=
  isConnected_connectedComponentIn_iff.mpr
    (realTypeSourceLocus_subset_sourceSymmetryCore U hreal (by simp [realTypeSourceLocus]))

private theorem component_mapsTo {U : Set (CoeffPair p)} (A : CoeffPair p → CoeffPair p)
    (hA : Continuous A) (h0 : A 0 = 0) (hU : MapsTo A U U) (hz : (0 : CoeffPair p) ∈ U) :
    MapsTo A (connectedComponentIn U 0) (connectedComponentIn U 0) := by
  have hp : IsPreconnected (A '' connectedComponentIn U 0) :=
    isPreconnected_connectedComponentIn.image A hA.continuousOn
  have hm : A 0 ∈ A '' connectedComponentIn U 0 := mem_image_of_mem A (mem_connectedComponentIn hz)
  have hs : A '' connectedComponentIn U 0 ⊆ U := by
    rintro _ ⟨φ,hφ,rfl⟩
    exact hU ((connectedComponentIn_subset _ _) hφ)
  have hsub := hp.subset_connectedComponentIn hm hs
  rw [h0] at hsub
  intro φ hφ
  exact hsub (mem_image_of_mem A hφ)

theorem sourceConnectedSymmetryCore_componentSwap (U : Set (CoeffPair p))
    (hreal : realTypeSourceLocus p ⊆ U) :
    MapsTo sourceComponentSwap (sourceConnectedSymmetryCore U) (sourceConnectedSymmetryCore U) :=
  component_mapsTo sourceComponentSwap sourceComponentSwap.continuous (by simp)
    (fun φ hφ => sourceSymmetryCore_componentSwap U φ hφ)
    (realTypeSourceLocus_subset_sourceSymmetryCore U hreal (by simp [realTypeSourceLocus]))

theorem sourceConnectedSymmetryCore_midpointReflection (U : Set (CoeffPair p))
    (hreal : realTypeSourceLocus p ⊆ U) :
    MapsTo sourceMidpointReflection (sourceConnectedSymmetryCore U) (sourceConnectedSymmetryCore U) :=
  component_mapsTo sourceMidpointReflection sourceMidpointReflection.continuous (by simp)
    (fun φ hφ => sourceSymmetryCore_midpointReflection U φ hφ)
    (realTypeSourceLocus_subset_sourceSymmetryCore U hreal (by simp [realTypeSourceLocus]))

theorem sourceConnectedSymmetryCore_circleRotation (U : Set (CoeffPair p))
    (hreal : realTypeSourceLocus p ⊆ U) (c : Circle) :
    MapsTo (sourceCircleRotation c) (sourceConnectedSymmetryCore U) (sourceConnectedSymmetryCore U) :=
  component_mapsTo (sourceCircleRotation c) (sourceReciprocalScaling (c:ℂ)).continuous
    (by simp [sourceCircleRotation]) (fun φ hφ => sourceSymmetryCore_circleRotation U φ hφ c)
    (realTypeSourceLocus_subset_sourceSymmetryCore U hreal (by simp [realTypeSourceLocus]))

/-- Root and actual full-primitive data coexist on an invariant connected
open neighborhood of the entire original real source locus. -/
theorem exists_sourceInvariantPrimitiveNeighborhood (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ A V : Set (CoeffPair p),
      IsOpen V ∧ IsConnected V ∧ realTypeSourceLocus p ⊆ V ∧
      MapsTo sourceComponentSwap V V ∧ MapsTo sourceMidpointReflection V V ∧
      (∀ c : Circle, MapsTo (sourceCircleRotation c) V V) ∧
      IsOpen (sourceCanonicalRootJointDomain hp hp1 V) ∧
      AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1) (sourceCanonicalRootJointDomain hp hp1 V) ∧
      SourceFullAbelianDifferentialData hp hp1 A V := by
  obtain ⟨A,U,_,D⟩ := exists_sourceFullAbelianDifferentialData hp hp1
  obtain ⟨G,hG,_,hrealG,hDom,hroot⟩ := exists_global_source_analytic_canonicalRoot hp hp1
  let B := U ∩ G
  have hB : IsOpen B := D.source_open.inter hG
  have hreal : realTypeSourceLocus p ⊆ B := fun φ hφ => ⟨D.real_subset hφ,hrealG hφ⟩
  let V := sourceConnectedSymmetryCore B
  have hV : IsOpen V := isOpen_sourceConnectedSymmetryCore B hB
  have hsub : V ⊆ B := sourceConnectedSymmetryCore_subset B
  have he : sourceCanonicalRootJointDomain hp hp1 V =
      sourceCanonicalRootJointDomain hp hp1 G ∩ Prod.snd ⁻¹' V := by
    ext t
    exact ⟨fun ht => ⟨⟨(hsub ht.1).2,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
  have hopen : IsOpen (sourceCanonicalRootJointDomain hp hp1 V) := by
    rw [he]
    exact hDom.inter (hV.preimage continuous_snd)
  refine ⟨A,V,hV,isConnected_sourceConnectedSymmetryCore B hreal,
    realTypeSourceLocus_subset_sourceConnectedSymmetryCore B hreal,
    sourceConnectedSymmetryCore_componentSwap B hreal,
    sourceConnectedSymmetryCore_midpointReflection B hreal,
    sourceConnectedSymmetryCore_circleRotation B hreal,hopen,
    hroot.mono (fun t ht => ⟨(hsub ht.1).2,ht.2⟩),?_⟩
  exact {
    source_open := hV
    real_subset := realTypeSourceLocus_subset_sourceConnectedSymmetryCore B hreal
    source_subset := fun φ hφ => D.source_subset (hsub hφ).1
    root_domain_open := hopen
    charts := fun φ hφ => D.charts φ (hsub hφ).1
    analytic := fun j => (D.analytic j).mono (fun t ht => ⟨(hsub ht.1).1,ht.2⟩)
    differential := fun j t ht => D.differential j t ⟨(hsub ht.1).1,ht.2⟩
  }

end NLS.ZakharovShabat
