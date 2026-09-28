import NLS.ZakharovShabat.SourcePsiGlobalEquationSequenceBound
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable

/-!
# Holomorphy of the global psi equation sequence

On a common selected contour family, local uniform `ℓᵖ` bounds and
scalar contour holomorphy imply Fréchet holomorphy of the full deleted
equation sequence near every real-type source.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The psi equation on a selected contour family, set to zero outside
the parameter set where its coordinates form a deleted `ℓᵖ` sequence. -/
def sourcePsiSelectedEquationSequence
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) : DeletedCoeff p n := by
  classical
  exact if h : ∃ F : DeletedCoeff p n,
      ∀ m : ℤ, (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c m) (R m)
  then Classical.choose h else 0

/-- When the selected equation coordinates form a deleted sequence,
the chosen sequence has exactly those coordinates. -/
theorem sourcePsiSelectedEquationSequence_apply_of_exists
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (h : ∃ F : DeletedCoeff p n,
      ∀ m : ℤ, (F : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (a : Coeff p) ψ (c m) (R m))
    (m : ℤ) :
    (sourcePsiSelectedEquationSequence hp hp1 n c R a ψ : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m
        (a : Coeff p) ψ (c m) (R m) := by
  simpa only [sourcePsiSelectedEquationSequence,dif_pos h] using
    (Classical.choose_spec h m)

/-- The global complex psi equation has a locally bounded,
Fréchet-holomorphic realization in the deleted `ℓᵖ` Banach space near
any real-type source and any deleted root input. -/
theorem exists_local_sourcePsi_globalEquation_formula_analytic
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ U : Set (DeletedCoeff p n × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ K : ℕ, ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ t ∈ U, ∀ m : ℤ,
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
              sourcePsiEquationCoordinate hp hp1 n m
                (t.1 : Coeff p) t.2 (c m) (R m)) ∧
          (∀ t ∈ U,
            ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ C) ∧
          DifferentiableOn ℂ
            (fun t : DeletedCoeff p n × CoeffPair p =>
              sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,K,c,R,hchoice,hgeom,C,hC,heq⟩ :=
    exists_local_sourcePsi_globalEquation_uniformNorm
      hp hp1 φ hφ (a₀ : Coeff p)
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  have hφW : φ ∈ W := hrealW hφ
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
    Ueq ∩ {t | t.2 ∈ W}
  have hUambOpen : IsOpen Uamb :=
    hUeqOpen.inter (hWopen.preimage continuous_snd)
  let U : Set (DeletedCoeff p n × CoeffPair p) := H ⁻¹' Uamb
  have hUopen : IsOpen U := hUambOpen.preimage hHcont
  have hbase : (a₀,φ) ∈ U := ⟨hbaseEq,hφW⟩
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hraw (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U) :
      ∃ G : DeletedCoeff p n,
        (∀ m : ℤ, (G : Coeff p) m =
          sourcePsiEquationCoordinate hp hp1 n m
            (t.1 : Coeff p) t.2 (c m) (R m)) ∧
        ‖G‖ ≤ C := heq n t.1 t.2 ht.1
  have hcoord (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U)
      (m : ℤ) : (F t : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m) := by
    obtain ⟨G,hGcoord,_⟩ := hraw t ht
    exact sourcePsiSelectedEquationSequence_apply_of_exists
      hp hp1 n c R t.1 t.2 ⟨G,hGcoord⟩ m
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
          (t.1 : Coeff p) t.2 (c m) (R m)) U := by
    intro t ht
    have hdataM := hgeom ((t.1 : Coeff p),t.2) ht.1 m
    have hbaseDiff :=
      differentiableAt_sourcePsiEquationCoordinate_of_contour_domain
        hp hp1 n m (t.1 : Coeff p) t.2
          (c m) (R m) hdataM.1.le W ht.2
          (hdata n).1 (hdata n).2 hdataM.2.2.2
    exact (hbaseDiff.comp t (hHdiff t)).differentiableWithinAt
  have hFcoord (m : ℤ) : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p) m) U :=
    (hscalar m).congr (fun t ht => hcoord t ht m)
  have hFdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p)) U :=
    NLS.Coeff.differentiableOn_of_bounded_coordinatewise
      (fun t => (F t : Coeff p)) hUopen hFcoord C hbound
  have hproject (t : DeletedCoeff p n × CoeffPair p) :
      Coeff.deleteCoordinateTo n (F t : Coeff p) = F t := by
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n (F t : Coeff p)).2
      (F t).property
  have hcomposed : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        Coeff.deleteCoordinateTo n (F t : Coeff p)) U :=
    (Coeff.deleteCoordinateTo (p := p) n).differentiable.comp_differentiableOn
      hFdiff
  have hdeleted : DifferentiableOn ℂ F U :=
    hcomposed.congr (fun t _ => (hproject t).symm)
  exact ⟨U,hUopen,hbase,K,c,R,hchoice,C,hC,
    (fun t ht m => hcoord t ht m),hbound,hdeleted⟩

end NLS.ZakharovShabat
