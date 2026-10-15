import NLS.ZakharovShabat.SourceAbelianAdmissibleIntegrals
import NLS.ZakharovShabat.SourceAbelianGapSupremum
import NLS.ZakharovShabat.SourceFullAbelianDifferentialData

/-!
# One common source neighborhood for Section 19

The same canonical primitive carries its exact joint differential, original
endpoint integrals, and locally uniform mixed supremum. Its neighborhood may
be chosen inside any given open neighborhood of the whole real-source locus.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Common original primitive data, with one local family for all gaps and exponents. -/
structure SourceSection19Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W U : Set (CoeffPair p)) : Prop
    extends SourceFullAbelianDifferentialData hp hp1 W U where
  ambient_open : IsOpen W
  connected : IsConnected U
  local_models : ∀ φ ∈ U, ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ U ∧
      V ⊆ ball C.discs.source.val C.discs.sourceRadius ∧ SourceAbelianMixedGapData C V

/-- A common domain retains the original source neighborhood as an ambient constraint. -/
theorem exists_sourceSection19Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (X : Set (CoeffPair p)) (hX : IsOpen X) (hrealX : realTypeSourceLocus p ⊆ X) :
    ∃ W U : Set (CoeffPair p), U ⊆ X ∧ SourceSection19Data hp hp1 W U := by
  obtain ⟨W,hW,_,hlocal⟩ := exists_sourceAbelian_mixedGapData hp hp1
  choose C V hV hφV hVC hmix using hlocal
  obtain ⟨Wd,Ud,_,A⟩ := exists_sourceFullAbelianDifferentialData hp hp1
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, V φ
  have hS : IsOpen S := isOpen_iUnion hV
  have hrealS : realTypeSourceLocus p ⊆ S :=
    fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφV ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn (S ∩ (Ud ∩ X)) (0 : CoeffPair p)
  have hU : IsOpen U := (hS.inter (A.source_open.inter hX)).connectedComponentIn
  have hsub : U ⊆ S ∩ (Ud ∩ X) := connectedComponentIn_subset _ _
  have hz : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hreal : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz
      (fun ψ hψ => ⟨hrealS hψ,A.real_subset hψ,hrealX hψ⟩)
  have hcharts (ψ : CoeffPair p) (hψ : ψ ∈ U) : Nonempty (SourceAbelianSpectralChart hp hp1 W ψ) := by
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hsub hψ).1
    exact (C φ).charts ψ (hVC φ hφ)
  have hroot : IsOpen (sourceCanonicalRootJointDomain hp hp1 U) := by
    have he : sourceCanonicalRootJointDomain hp hp1 U =
        sourceCanonicalRootJointDomain hp hp1 Ud ∩ Prod.snd ⁻¹' U := by
      ext t
      exact ⟨fun ht => ⟨⟨(hsub ht.1).2.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [he]
    exact A.root_domain_open.inter (hU.preimage continuous_snd)
  have heq (n : ℤ) (t : ℂ × CoeffPair p) (ht : t ∈ sourceCanonicalRootJointDomain hp hp1 U) :
      sourceFullAbelianPrimitive hp hp1 W n =ᶠ[𝓝 t] sourceFullAbelianPrimitive hp hp1 Wd n := by
    filter_upwards [hroot.mem_nhds ht] with u hu
    obtain ⟨E⟩ := hcharts u.2 hu.1
    obtain ⟨Ed⟩ := A.charts u.2 (hsub hu.1).2.1
    exact sourceFullAbelianPrimitive_independent_neighborhood E Ed n u.1
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 u.2 hu.2)
  refine ⟨W,U,fun ψ hψ => (hsub hψ).2.2,{
    source_open := hU
    real_subset := hreal
    source_subset := ?_
    root_domain_open := hroot
    charts := hcharts
    analytic := fun n t ht => (A.analytic n t ⟨(hsub ht.1).2.1,ht.2⟩).congr (heq n t ht).symm
    differential := fun n t ht => (A.differential n t ⟨(hsub ht.1).2.1,ht.2⟩).congr_of_eventuallyEq (heq n t ht)
    ambient_open := hW
    connected := isConnected_connectedComponentIn_iff.mpr ⟨hrealS hz,A.real_subset hz,hrealX hz⟩
    local_models := ?_
  }⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hsub hψ).1
    exact (C φ).discs.source_subset (hVC φ hφ)
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hsub hψ).1
    exact ⟨C φ,U ∩ V φ,hU.inter (hV φ),⟨hψ,hφ⟩,inter_subset_left,
      fun χ hχ => hVC φ hχ.2,(hmix φ).mono inter_subset_right⟩

namespace SourceSection19Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W U : Set (CoeffPair p)}

/-- Every complex source in the common neighborhood has an actual Cauchy family. -/
theorem cauchyFamily (D : SourceSection19Data hp hp1 W U) (ψ : CoeffPair p) (hψ : ψ ∈ U) :
    ∃ C : SourceFullAbelianUniformCauchyFamily hp hp1 W,
      ψ ∈ ball C.discs.source.val C.discs.sourceRadius := by
  obtain ⟨C,V,_,hψV,_,hVC,_⟩ := D.local_models ψ hψ
  exact ⟨C,hVC hψV⟩

end SourceSection19Data
end NLS.ZakharovShabat
