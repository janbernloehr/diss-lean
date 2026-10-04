import NLS.ZakharovShabat.SourceFullAbelianSquareGapMajorants
import NLS.ZakharovShabat.SourceSymmetricContour

/-! # Jointly analytic filled squares with complex-gap error estimates

The Cauchy formula uses the midpoint and squared gap, so joint analyticity
survives endpoint collision. One common source neighborhood supports this
regularity and the mixed sequence bounds needed in Lemma 20.3.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- Only symmetric endpoint coordinates enter the joint analytic square. -/
theorem square_joint_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (V : Set (CoeffPair p)) (hVC : V ⊆ ball C.discs.source.val C.discs.sourceRadius)
    (j : ℤ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ j) V)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2) V) :
    AnalyticOnNhd ℂ (C.square j) (ball (C.discs.center j) (C.discs.outer j) ×ˢ V) := by
  intro t ht
  have hmid := (hτ t.2 ht.2).comp (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
  have hgap := (hγ t.2 ht.2).comp (f := fun t : ℂ × CoeffPair p => t.2) analyticAt_snd
  exact (((analyticAt_fst.sub hmid).pow 2).sub (hgap.div_const)).mul
    ((C.quotient_analytic j t ⟨ht.1,hVC ht.2⟩).pow 2)

/-- The canonical filled square is jointly analytic through the selected
moving gap, even when the endpoints coincide. Only the other cuts are omitted. -/
theorem fullSquare_joint_analytic
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)
    (V : Set (CoeffPair p)) (hV : IsOpen V)
    (hVC : V ⊆ ball C.discs.source.val C.discs.sourceRadius)
    (hroot : IsOpen (sourceCanonicalRootJointDomain hp hp1 V))
    (j : ℤ)
    (hτ : AnalyticOnNhd ℂ (fun ψ => sourceStandardRootMidpoint hp hp1 ψ j) V)
    (hγ : AnalyticOnNhd ℂ (fun ψ =>
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2) V) :
    AnalyticOnNhd ℂ (sourceFullAbelianSquare hp hp1 W j)
      (sourceStandardRootOmittedJointDomain hp hp1 V j) := by
  intro t ht
  by_cases hz : t.1 ∈ sourcePeriodicSegment hp hp1 t.2 j
  · have htB : t ∈ ball (C.discs.center j) (C.discs.outer j) ×ˢ V :=
      ⟨C.segment_subset_outer j t.2 (hVC ht.1) hz,ht.1⟩
    apply (C.square_joint_analytic V hVC j hτ hγ t htB).congr
    filter_upwards [(isOpen_ball.prod hV).mem_nhds htB] with u hu
    exact (C.fullSquare_eq_square j u.2 (hVC hu.2) hu.1).symm
  · have htR : t ∈ sourceCanonicalRootJointDomain hp hp1 V := by
      refine ⟨ht.1,?_⟩
      intro k
      by_cases hk : k = j
      · simpa only [hk] using hz
      · exact ht.2 k hk
    apply ((C.full_analytic j t ⟨hVC ht.1,htR.2⟩).pow 2).congr
    filter_upwards [hroot.mem_nhds htR] with u hu
    obtain ⟨D⟩ := C.charts u.2 (hVC hu.1)
    exact (sourceFullAbelianSquare_eq_sq D j
      (sourceCanonicalRootDomain_subset_openGapComplement hp hp1 u.2 hu.2)).symm

end SourceFullAbelianUniformCauchyFamily

/-- Joint filled-square analyticity and the Lemma 20.3 square expansion
hold on the same connected source neighborhood. All indices and every
finite auxiliary exponent above one use one local source ball. -/
theorem exists_sourceFullAbelian_almostReal_jointSquare_gap_majorants
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ realTypeSourceLocus p ⊆ U ∧ U ⊆ W ∧
      (∀ j : ℤ, AnalyticOnNhd ℂ (sourceFullAbelianSquare hp hp1 W j)
        (sourceStandardRootOmittedJointDomain hp hp1 U j)) ∧
      ∀ φ ∈ U, ∃ r : ℝ, 0 < r ∧ ball φ r ⊆ U ∧
        ∀ q : ℝ≥0∞, q ≠ ⊤ → 1 < q → ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ ball φ r,
          ∃ Bq : Coeff q, ∃ Bg : Coeff (ENNReal.ofReal (p.toReal/2)),
            ‖Bq‖ ≤ M ∧ ‖Bg‖ ≤ M ∧ ∀ j : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
              ‖sourceFullAbelianSquare hp hp1 W j (z,ψ) + sourceAngularSelectedPolynomial hp hp1 ψ j z‖ ≤
                ‖sourcePeriodicGapDisplacement hp hp1 ψ j‖^2*(‖Bq j‖+‖Bg j‖) := by
  obtain ⟨W,_,_,hlocal⟩ := exists_sourceFullAbelian_local_square_gap_majorants hp hp1
  choose C V hV hφV hVC hmajor using hlocal
  obtain ⟨M,hM,_,hrealM,hcoord⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  obtain ⟨_,O,_,hO,_,hrealO,_,hrootO,_,_⟩ := exists_sourceFullAbelian_almostReal_jointAnalytic hp hp1
  let T (φ : realTypeSourceSubmodule p) := V φ ∩ (O ∩ M)
  have hT (φ : realTypeSourceSubmodule p) : IsOpen (T φ) := (hV φ).inter (hO.inter hM)
  have hφT (φ : realTypeSourceSubmodule p) : φ.val ∈ T φ :=
    ⟨hφV φ,hrealO φ.property,hrealM φ.property⟩
  have hrootT (φ : realTypeSourceSubmodule p) : IsOpen (sourceCanonicalRootJointDomain hp hp1 (T φ)) := by
    have heq : sourceCanonicalRootJointDomain hp hp1 (T φ) =
        sourceCanonicalRootJointDomain hp hp1 O ∩ (Prod.snd ⁻¹' T φ) := by
      ext t
      exact ⟨fun ht => ⟨⟨ht.1.2.1,ht.2⟩,ht.1⟩,fun ht => ⟨ht.2,ht.1.2⟩⟩
    rw [heq]
    exact hrootO.inter ((hT φ).preimage continuous_snd)
  let S : Set (CoeffPair p) := ⋃ φ : realTypeSourceSubmodule p, T φ
  have hS : IsOpen S := isOpen_iUnion hT
  have hrealS : realTypeSourceLocus p ⊆ S :=
    fun ψ hψ => mem_iUnion.mpr ⟨⟨ψ,hψ⟩,hφT ⟨ψ,hψ⟩⟩
  let U := connectedComponentIn S (0 : CoeffPair p)
  have hzero : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  have hrealU : realTypeSourceLocus p ⊆ U :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hzero hrealS
  have hUS : U ⊆ S := connectedComponentIn_subset S 0
  have hU : IsOpen U := hS.connectedComponentIn
  refine ⟨W,U,hU,isConnected_connectedComponentIn_iff.mpr (hrealS hzero),hrealU,?_,?_,?_⟩
  · intro ψ hψ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hψ)
    exact (C φ).discs.source_subset (hVC φ hφ.1)
  · intro j t ht
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS ht.1)
    exact (C φ).fullSquare_joint_analytic (T φ) (hT φ)
      (fun ψ hψ => hVC φ hψ.1) (hrootT φ) j
      (fun ψ hψ => (hcoord ψ hψ.2.2 j).1)
      (fun ψ hψ => (hcoord ψ hψ.2.2 j).2) t ⟨hφ,ht.2⟩
  · intro χ hχ
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hUS hχ)
    obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp ((hU.inter (hT φ)).mem_nhds ⟨hχ,hφ⟩)
    refine ⟨r,hr,fun ψ hψ => (hsub hψ).1,?_⟩
    intro q hq hq1
    obtain ⟨B,hB,hb⟩ := hmajor φ q hq hq1
    exact ⟨B,hB,fun ψ hψ => hb ψ (hsub hψ).2.1⟩

end NLS.ZakharovShabat
