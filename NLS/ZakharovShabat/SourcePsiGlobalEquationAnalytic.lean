import NLS.ZakharovShabat.SourcePsiGlobalEquationSequenceBound
import NLS.SequenceSpaces.BoundedCoordinateDifferentiable
import NLS.ZakharovShabat.SourcePsiContourConjugation
import NLS.ComplexAnalysis.BanachHolomorphicLineBounds

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
        (∀ m : ℤ, (c m).im = 0) ∧
        (∀ m : ℤ, K < m.natAbs →
          c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
        (∀ t ∈ U, ∀ m : ℤ,
          0 < R m ∧
          sourcePeriodicSegment hp hp1 t.2 m ⊆ ball (c m) (R m) ∧
          closedBall (c m) (R m) ⊆
            sourceStandardRootOmittedDomain hp hp1 t.2 m ∧
          sphere (c m) (R m) ⊆
            sourceCanonicalRootDomain hp hp1 t.2) ∧
        (∃ Niso : ℕ, ∃ εiso : ℝ,
          (∀ t ∈ U, ∀ m : ℤ,
            sourceSpectralCluster hp hp1 t.2 m ⊆
              sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
          (∀ i j : ℤ, i ≠ j →
            Disjoint (sourceIsolatingDisc hp hp1 φ Niso εiso i)
              (sourceIsolatingDisc hp hp1 φ Niso εiso j)) ∧
          ∀ m : ℤ, closedBall (c m) (R m) ⊆
            sourceIsolatingDisc hp hp1 φ Niso εiso m) ∧
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ t ∈ U, ∀ m : ℤ,
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
              sourcePsiEquationCoordinate hp hp1 n m
                (t.1 : Coeff p) t.2 (c m) (R m)) ∧
          (∀ t ∈ U,
            ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ C) ∧
          (∀ t ∈ U,
            IsRealType (CoeffPair.toMax p t.2) →
              (∀ k : ℤ, (displacedRoots (t.1 : Coeff p) k).im = 0) →
                ∀ m : ℤ,
                  ((sourcePsiSelectedEquationSequence hp hp1 n c R
                    t.1 t.2 : Coeff p) m).im = 0) ∧
          DifferentiableOn ℂ
            (fun t : DeletedCoeff p n × CoeffPair p =>
              sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,K,c,R,hcReal,hchoice,hgeom,
      ⟨Niso,εiso,hcluster,hdisjoint,hfilled⟩,C,hC,heq⟩ :=
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
  have hrealCoord (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U)
      (hreal : IsRealType (CoeffPair.toMax p t.2))
      (hroots : ∀ k : ℤ, (displacedRoots (t.1 : Coeff p) k).im = 0)
      (m : ℤ) : ((F t : Coeff p) m).im = 0 := by
    rw [hcoord t ht m]
    let x : ℝ := (c m).re
    have hx : (x:ℂ) = c m := by
      apply Complex.ext
      · rfl
      · simpa [x] using (hcReal m).symm
    obtain ⟨hR,_,_,hcircle⟩ :=
      hgeom ((t.1 : Coeff p),t.2) ht.1 m
    have h := sourcePsiEquationCoordinate_im_eq_zero_of_realCenteredCircle
      hp hp1 t.2 hreal n m (t.1 : Coeff p) hroots x (R m) hR
        (by simpa only [hx] using hcircle)
    simpa only [hx] using h
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
  exact ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,
    (fun t ht m => hgeom ((t.1 : Coeff p),t.2) ht.1 m),
    ⟨Niso,εiso,
      (fun t ht m => hcluster ((t.1 : Coeff p),t.2) ht.1 m),
      hdisjoint,hfilled⟩,C,hC,
    (fun t ht m => hcoord t ht m),hbound,hrealCoord,hdeleted⟩

/-- The selected equation on an anchored contour chart has Cauchy
bounds for its Banach-valued Taylor coefficients along every complex
line through a real-type base point. The same radius and norm constant
work for all unit directions and all derivative orders. -/
theorem exists_local_sourcePsi_globalEquation_uniformLineTaylorBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ r C : ℝ,
      0 < r ∧ 0 ≤ C ∧
      ∀ v : DeletedCoeff p n × CoeffPair p, ‖v‖ ≤ 1 →
        ∀ k : ℕ,
          ‖iteratedDeriv k
            (fun z : ℂ =>
              sourcePsiSelectedEquationSequence hp hp1 n c R
                (((a₀,φ) + z • v).1) (((a₀,φ) + z • v).2)) 0‖ ≤
            k.factorial * C / r^k := by
  obtain ⟨U,hUopen,hbase,_,c,R,_,_,_,_,C,hC,_,hbound,_,hFdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic hp hp1 φ hφ n a₀
  let x : DeletedCoeff p n × CoeffPair p := (a₀,φ)
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hUopen x hbase
  let r : ℝ := δ/3
  have hr : 0 < r := by dsimp [r]; positivity
  have hball2 : ball x (2*r) ⊆ U :=
    (ball_subset_ball (by dsimp [r]; linarith)).trans hball
  have hdiff : DifferentiableOn ℂ F (ball x (2*r)) :=
    hFdiff.mono hball2
  have hnorm (t : DeletedCoeff p n × CoeffPair p)
      (ht : t ∈ ball x (2*r)) : ‖F t‖ ≤ C :=
    hbound t (hball2 ht)
  refine ⟨c,R,r,C,hr,hC,?_⟩
  intro v hv k
  exact NLS.ComplexAnalysis.norm_iteratedDeriv_affineLine_le_of_ball_bound
    F x r C hr hdiff hnorm v hv k

end NLS.ZakharovShabat
