import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.SequenceSpaces.DeletedCoordinateAtInfinity
import NLS.ZakharovShabat.SourcePsiLimitScalarJacobianEntry

/-!
# One contour family for escaping deleted-index Jacobians

The uniform global psi equation bound supplies a single contour family
for every deleted index. At all sufficiently distant indices the
deleted coefficient sequence lies in its ambient neighborhood. The
coordinatewise contour formula and local boundedness then give a
holomorphic selected chart on this same contour family.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Near fixed real-type source data, a single contour family works for
all sufficiently distant deleted indices, with analytic selected
equation charts containing the corresponding deleted sequences. -/
theorem exists_common_sourcePsi_selectedJacobianCharts_at_natAbs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∃ U : Set (DeletedCoeff p n × CoeffPair p),
          IsOpen U ∧ (Coeff.deleteCoordinateTo n a,φ) ∈ U ∧
          (∀ t ∈ U, ∀ m : ℤ,
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
              sourcePsiEquationCoordinate hp hp1 n m
                (t.1 : Coeff p) t.2 (c m) (R m)) ∧
          DifferentiableOn ℂ
            (fun t : DeletedCoeff p n × CoeffPair p =>
              sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U := by
  obtain ⟨Ueq,hUeqOpen,hbaseEq,K,c,R,hcReal,hchoice,hgeom,
      hiso,C,hC,heq⟩ :=
    exists_local_sourcePsi_globalEquation_uniformNorm hp hp1 φ hφ a
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let Uamb : Set (Coeff p × CoeffPair p) := Ueq ∩ {t | t.2 ∈ W}
  have hUambOpen : IsOpen Uamb :=
    hUeqOpen.inter (hWopen.preimage continuous_snd)
  have hbase : (a,φ) ∈ Uamb := ⟨hbaseEq,hrealW hφ⟩
  have hparam : Tendsto
      (fun n : ℤ => ((Coeff.deleteCoordinate n a : Coeff p),φ))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (a,φ)) := by
    simpa only [nhds_prod_eq] using
      (Coeff.tendsto_deleteCoordinate_at_natAbs hp a).prodMk
        (tendsto_const_nhds (x := φ))
  have hnear : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ((Coeff.deleteCoordinate n a : Coeff p),φ) ∈ Uamb :=
    hparam.eventually (hUambOpen.mem_nhds hbase)
  refine ⟨c,R,(fun m => hgeom (a,φ) hbaseEq m),?_⟩
  filter_upwards [hnear] with n hn
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
  let U : Set (DeletedCoeff p n × CoeffPair p) := H ⁻¹' Uamb
  have hUopen : IsOpen U := hUambOpen.preimage hHcont
  have hpair : (Coeff.deleteCoordinateTo n a,φ) ∈ U := by
    change (((Coeff.deleteCoordinateTo n a : DeletedCoeff p n) : Coeff p),φ) ∈ Uamb
    change ((Coeff.deleteCoordinate n a : Coeff p),φ) ∈ Uamb
    exact hn
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
  exact ⟨U,hUopen,hpair,(fun t ht m => hcoord t ht m),hdeleted⟩

/-- The same contour family gives entrywise convergence of the actual
bounded full-space selected Jacobians wherever the retained root stays
off the fixed contour. -/
theorem exists_common_sourcePsi_fullJacobian_entryLimit
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∀ m k : ℤ,
        (∀ z ∈ sphere (c m) (R m), displacedRoots a k - z ≠ 0) →
          Tendsto (fun n : ℤ =>
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m)
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m))) := by
  obtain ⟨c,R,hgeom,hcharts⟩ :=
    exists_common_sourcePsi_selectedJacobianCharts_at_natAbs hp hp1 a φ hφ
  refine ⟨c,R,hgeom,?_⟩
  intro m k hk
  obtain ⟨hR,_,hdisc,hcircle⟩ := hgeom m
  have hscalar := tendsto_sourcePsiDeletedScalarMatrixEntry_at_natAbs
    hp hp1 m k a φ hφ (c m) (R m) hR.le hdisc hcircle hk
  have hne : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      m ≠ n ∧ k ≠ n := by
    apply eventually_comap.mpr
    apply eventually_atTop.mpr
    refine ⟨max m.natAbs k.natAbs + 1,?_⟩
    intro j hj n hn
    constructor
    · intro hmn
      subst n
      omega
    · intro hkn
      subst n
      omega
  have heq : (fun n : ℤ =>
      (sourcePsiFullRootJacobian hp hp1 n c R
        (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m) =ᶠ[
        Filter.comap Int.natAbs Filter.atTop]
      (fun n => sourcePsiDeletedScalarMatrixEntry hp hp1 n m k a φ (c m) (R m)) := by
    filter_upwards [hcharts,hne] with n hchart hn
    obtain ⟨U,hUopen,hpair,hcoord,hdiff⟩ := hchart
    exact sourcePsiFullRootJacobian_retained_entry_eq_scalarMatrixEntry
      hp hp1 n m k a φ c R U hUopen hcoord hdiff hpair hn.1 hn.2
  exact hscalar.congr' heq.symm

end NLS.ZakharovShabat
