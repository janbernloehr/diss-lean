import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-!
# Holomorphy of the complex near-free psi equation sequence

The locally uniform deleted `ℓᵖ` bound and holomorphy of every fixed
contour coordinate imply Fréchet holomorphy of the full sequence.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The psi equation sequence is selected whenever its fixed-circle
coordinates belong to the deleted `ℓᵖ` space. Outside that domain it
is set to zero. -/
def sourcePsiDeletedEquationSequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) : DeletedCoeff p n := by
  classical
  exact if h : ∃ F : DeletedCoeff p n,
      ∀ m : ℤ, (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8)
  then Classical.choose h else 0

/-- At every parameter where the fixed-circle coordinate sequence
exists, the selected sequence has precisely those coordinates. -/
theorem sourcePsiDeletedEquationSequence_apply_of_exists
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (h : ∃ F : DeletedCoeff p n,
      ∀ m : ℤ, (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8))
    (m : ℤ) :
    (sourcePsiDeletedEquationSequence hp hp1 n a ψ : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m
        (a : Coeff p) ψ ((Real.pi : ℂ)*m) (Real.pi/8) := by
  simpa only [sourcePsiDeletedEquationSequence,dif_pos h] using
    (Classical.choose_spec h m)

/-- Lemma 12.4 near the free source: the complete deleted psi equation
is a locally bounded Fréchet-holomorphic map of the deleted root input
and the complex source potential. -/
theorem exists_nearFree_complex_deletedPsi_equation_differentiableOn
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ t ∈ U,
          ‖sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2‖ ≤ C) ∧
        DifferentiableOn ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            (sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2 : Coeff p)) U := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,C,hC,heq⟩ :=
    exists_nearFree_complex_deletedPsi_equation_uniformNorm
      hp hp1 (a₀ : Coeff p)
  obtain ⟨Vcircle,hVcircleOpen,hzeroCircle,hcircle⟩ :=
    exists_nearFree_freeEighthCircle_subset_rootDomain hp hp1
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  have hzeroW : (0 : CoeffPair p) ∈ W :=
    hrealW (by simp [realTypeSourceLocus])
  let H : DeletedCoeff p n × CoeffPair p → Coeff p × CoeffPair p :=
    fun t => ((t.1 : Coeff p),t.2)
  have hHcont : Continuous H :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hHdiff : Differentiable ℂ H := by
    have hsub : Differentiable ℂ
        (fun t : DeletedCoeff p n × CoeffPair p => (t.1 : Coeff p)) :=
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL).differentiable.comp
        differentiable_fst
    exact hsub.prodMk differentiable_snd
  let Uamb : Set (Coeff p × CoeffPair p) :=
    Ueq ∩ {t | t.2 ∈ Vcircle ∩ W}
  have hUambOpen : IsOpen Uamb :=
    hUeqOpen.inter ((hVcircleOpen.inter hWopen).preimage continuous_snd)
  let U : Set (DeletedCoeff p n × CoeffPair p) := H ⁻¹' Uamb
  have hUopen : IsOpen U := hUambOpen.preimage hHcont
  have hbase : (a₀,(0 : CoeffPair p)) ∈ U :=
    ⟨hbaseEq,hzeroCircle,hzeroW⟩
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2
  have hraw (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U) :
      ∃ G : DeletedCoeff p n,
        (∀ m : ℤ, (G : Coeff p) m =
          sourcePsiEquationCoordinate hp hp1 n m
            (t.1 : Coeff p) t.2 ((Real.pi : ℂ)*m) (Real.pi/8)) ∧
        ‖G‖ ≤ C :=
    heq n t.1 t.2 ht.1
  have hcoord (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U)
      (m : ℤ) : (F t : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 ((Real.pi : ℂ)*m) (Real.pi/8) := by
    exact sourcePsiDeletedEquationSequence_apply_of_exists
      hp hp1 n t.1 t.2 ⟨(hraw t ht).choose,(hraw t ht).choose_spec.1⟩ m
  have hbound (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U) :
      ‖F t‖ ≤ C := by
    obtain ⟨G,hGcoord,hGnorm⟩ := hraw t ht
    have hFG : F t = G := by
      ext m
      exact (hcoord t ht m).trans (hGcoord m).symm
    simpa only [hFG] using hGnorm
  have hscalar (m : ℤ) : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 ((Real.pi : ℂ)*m) (Real.pi/8)) U := by
    intro t ht
    have hbaseDiff :=
      differentiableAt_sourcePsiEquationCoordinate_of_contour_domain
        hp hp1 n m (t.1 : Coeff p) t.2
        ((Real.pi : ℂ)*m) (Real.pi/8) (by positivity)
        W ht.2.2 (hdata n).1 (hdata n).2
        (hcircle t.2 ht.2.1 m)
    exact (hbaseDiff.comp t (hHdiff t)).differentiableWithinAt
  have hFcoord (m : ℤ) : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p) m) U :=
    (hscalar m).congr (fun t ht => hcoord t ht m)
  have hFdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p)) U :=
    NLS.Coeff.differentiableOn_of_bounded_coordinatewise
      (fun t => (F t : Coeff p)) hUopen hFcoord C hbound
  refine ⟨U,hUopen,hbase,C,hC,?_,?_⟩
  · exact hbound
  · exact hFdiff

/-- The complex near-free psi equation is holomorphic with values in
the actual deleted-coordinate Banach space. The coordinate-deletion
projection is the identity on its values. -/
theorem exists_nearFree_complex_deletedPsi_equation_differentiableOn_deleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ t ∈ U,
          ‖sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2‖ ≤ C) ∧
        DifferentiableOn ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2) U := by
  obtain ⟨U,hUopen,hbase,C,hC,hbound,hambient⟩ :=
    exists_nearFree_complex_deletedPsi_equation_differentiableOn
      hp hp1 n a₀
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2
  have hproject (t : DeletedCoeff p n × CoeffPair p) :
      Coeff.deleteCoordinateTo n (F t : Coeff p) = F t := by
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n (F t : Coeff p)).2
      (F t).property
  have hcomposed : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        Coeff.deleteCoordinateTo n (F t : Coeff p)) U :=
    (Coeff.deleteCoordinateTo (p := p) n).differentiable.comp_differentiableOn
      hambient
  have hdeleted : DifferentiableOn ℂ F U :=
    hcomposed.congr (fun t _ => (hproject t).symm)
  exact ⟨U,hUopen,hbase,C,hC,hbound,hdeleted⟩

/-- The near-free form of Lemma 12.4, with the original contour formula,
local boundedness, and holomorphy into the deleted Banach space all on
one parameter neighborhood. -/
theorem exists_nearFree_complex_deletedPsi_equation_formula_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,(0 : CoeffPair p)) ∈ U ∧
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ t ∈ U, ∀ m : ℤ,
          (sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2 : Coeff p) m =
            sourcePsiEquationCoordinate hp hp1 n m
              (t.1 : Coeff p) t.2
              ((Real.pi : ℂ)*m) (Real.pi/8)) ∧
        (∀ t ∈ U,
          ‖sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2‖ ≤ C) ∧
        DifferentiableOn ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiDeletedEquationSequence hp hp1 n t.1 t.2) U := by
  obtain ⟨Uan,hUanOpen,hbaseAn,C,hC,hbound,han⟩ :=
    exists_nearFree_complex_deletedPsi_equation_differentiableOn_deleted
      hp hp1 n a₀
  obtain ⟨Ueq,hUeqOpen,hbaseEq,Ceq,hCeq,heq⟩ :=
    exists_nearFree_complex_deletedPsi_equation_uniformNorm
      hp hp1 (a₀ : Coeff p)
  let H : DeletedCoeff p n × CoeffPair p → Coeff p × CoeffPair p :=
    fun t => ((t.1 : Coeff p),t.2)
  have hHcont : Continuous H :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  let U : Set (DeletedCoeff p n × CoeffPair p) :=
    Uan ∩ H ⁻¹' Ueq
  have hUopen : IsOpen U :=
    hUanOpen.inter (hUeqOpen.preimage hHcont)
  have hbase : (a₀,(0 : CoeffPair p)) ∈ U :=
    ⟨hbaseAn,hbaseEq⟩
  refine ⟨U,hUopen,hbase,C,hC,?_,?_,?_⟩
  · intro t ht m
    obtain ⟨G,hGcoord,_⟩ := heq n t.1 t.2 ht.2
    exact sourcePsiDeletedEquationSequence_apply_of_exists
      hp hp1 n t.1 t.2 ⟨G,hGcoord⟩ m
  · intro t ht
    exact hbound t ht.1
  · exact han.mono inter_subset_left

end NLS.ZakharovShabat
