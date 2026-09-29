import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.SequenceSpaces.DeletedCoordinateAtInfinity
import NLS.ZakharovShabat.SourcePsiLimitScalarJacobianEntry
import NLS.ComplexAnalysis.BanachTaylorBounds

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
theorem exists_common_sourcePsi_selectedJacobianCharts_at_natAbs_realCentered
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, (c m).im = 0) ∧
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Ktail : ℕ,
      (∀ m : ℤ, Ktail < m.natAbs →
        c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∃ U : Set (DeletedCoeff p n × CoeffPair p),
          IsOpen U ∧ (Coeff.deleteCoordinateTo n a,φ) ∈ U ∧
          ball (Coeff.deleteCoordinateTo n a,φ) δ ⊆ U ∧
          (∀ t ∈ U,
            ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ C) ∧
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
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hUambOpen (a,φ) hbase
  have hhalf : 0 < r / 2 := by positivity
  have hparam : Tendsto
      (fun n : ℤ => ((Coeff.deleteCoordinate n a : Coeff p),φ))
      (Filter.comap Int.natAbs Filter.atTop) (𝓝 (a,φ)) := by
    simpa only [nhds_prod_eq] using
      (Coeff.tendsto_deleteCoordinate_at_natAbs hp a).prodMk
        (tendsto_const_nhds (x := φ))
  have hnear : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ((Coeff.deleteCoordinate n a : Coeff p),φ) ∈ ball (a,φ) (r/2) :=
    hparam.eventually (isOpen_ball.mem_nhds (mem_ball_self hhalf))
  refine ⟨c,R,hcReal,(fun m => hgeom (a,φ) hbaseEq m),K,hchoice,r/2,hhalf,C,hC,?_⟩
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
    exact hball (ball_subset_ball (by linarith) hn)
  have hlocal : ball (Coeff.deleteCoordinateTo n a,φ) (r/2) ⊆ U := by
    intro t ht
    have hdist : dist (H t) ((Coeff.deleteCoordinate n a : Coeff p),φ) =
        dist t (Coeff.deleteCoordinateTo n a,φ) := by
      simp [H, Prod.dist_eq, Subtype.dist_eq, Coeff.deleteCoordinateTo]
    have ht' : dist (H t) (a,φ) < r := by
      calc
        dist (H t) (a,φ) ≤
            dist (H t) ((Coeff.deleteCoordinate n a : Coeff p),φ) +
              dist ((Coeff.deleteCoordinate n a : Coeff p),φ) (a,φ) :=
          dist_triangle _ _ _
        _ < r := by rw [hdist]; have h1 := (mem_ball.mp ht); have h2 := (mem_ball.mp hn); linarith
    exact hball (mem_ball.mpr ht')
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
  exact ⟨U,hUopen,hpair,hlocal,hbound,
    (fun t ht m => hcoord t ht m),hdeleted⟩

/-- Compatibility form of the real-centered construction, retaining
the original statement. -/
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
      ∃ Ktail : ℕ,
      (∀ m : ℤ, Ktail < m.natAbs →
        c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∃ U : Set (DeletedCoeff p n × CoeffPair p),
          IsOpen U ∧ (Coeff.deleteCoordinateTo n a,φ) ∈ U ∧
          ball (Coeff.deleteCoordinateTo n a,φ) δ ⊆ U ∧
          (∀ t ∈ U,
            ‖sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2‖ ≤ C) ∧
          (∀ t ∈ U, ∀ m : ℤ,
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
              sourcePsiEquationCoordinate hp hp1 n m
                (t.1 : Coeff p) t.2 (c m) (R m)) ∧
          DifferentiableOn ℂ
            (fun t : DeletedCoeff p n × CoeffPair p =>
              sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U := by
  obtain ⟨c,R,_,hdata⟩ :=
    exists_common_sourcePsi_selectedJacobianCharts_at_natAbs_realCentered hp hp1 a φ hφ
  exact ⟨c,R,hdata⟩

/-- On one contour family, escaping full-space Jacobians have both a
uniform operator-norm bound and the candidate `Q*` matrix-entry limits. -/
theorem exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit_realCentered
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ, (c m).im = 0) ∧
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ M : ℝ, 0 ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ,
          (∀ z ∈ sphere (c m) (R m), displacedRoots a k - z ≠ 0) →
            Tendsto (fun n : ℤ =>
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m)
              (Filter.comap Int.natAbs Filter.atTop)
              (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)))) ∧
        ∃ Ktail : ℕ,
          (∀ m : ℤ, Ktail < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
                deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (Coeff.deleteCoordinateTo n a +
                      Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0 := by
  obtain ⟨c,R,hcReal,hgeom,Kfree,hfree,δ,hδ,C,hC,hcharts⟩ :=
    exists_common_sourcePsi_selectedJacobianCharts_at_natAbs_realCentered hp hp1 a φ hφ
  let M : ℝ := 2*C/(δ/2) + 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  refine ⟨c,R,hcReal,hgeom,M,hM,?_,?_,Kfree,hfree,?_⟩
  filter_upwards [hcharts] with n hchart
  obtain ⟨U,hUopen,hbase,hlocal,hbound,hcoord,hdiff⟩ := hchart
  let b₀ : DeletedCoeff p n := Coeff.deleteCoordinateTo n a
  let f : DeletedCoeff p n → DeletedCoeff p n :=
    fun b => sourcePsiSelectedEquationSequence hp hp1 n c R b φ
  have hballPair (b : DeletedCoeff p n)
      (hb : b ∈ ball b₀ δ) : (b,φ) ∈ U := by
    apply hlocal
    simpa only [dist_prod_same_right, mem_ball] using hb
  have hfdiff : DifferentiableOn ℂ f (ball b₀ δ) := by
    intro b hb
    have hbU := hballPair b hb
    have hdiffAt := (hdiff (b,φ) hbU).differentiableAt
      (hUopen.mem_nhds hbU)
    have hpairDiff : DifferentiableAt ℂ
        (fun b : DeletedCoeff p n => (b,φ)) b :=
      (differentiableAt_id : DifferentiableAt ℂ
        (fun b : DeletedCoeff p n => b) b).prodMk (differentiableAt_const φ)
    exact (hdiffAt.comp b hpairDiff)
      |>.differentiableWithinAt
  have hfbound (b : DeletedCoeff p n) (hb : b ∈ ball b₀ δ) :
      ‖f b‖ ≤ C := hbound (b,φ) (hballPair b hb)
  have hδhalf : 0 < δ/2 := by positivity
  have hballEq : ball b₀ (δ/2+δ/2) = ball b₀ δ := by
    congr 1
    ring
  have hQ : ‖sourcePsiSelectedRootJacobian hp hp1 n c R b₀ φ‖ ≤
      2*C/(δ/2) := by
    change ‖fderiv ℂ f b₀‖ ≤ _
    exact NLS.ComplexAnalysis.norm_fderiv_le_of_ball_bound f b₀ b₀
      (δ/2) (δ/2) C hδhalf
      (by rw [hballEq]; exact hfdiff)
      (by rw [hballEq]; exact hfbound)
      (mem_ball_self hδhalf)
  have hfull := Coeff.norm_deletedOperatorExtension_le n (2:ℂ)
    (sourcePsiSelectedRootJacobian hp hp1 n c R b₀ φ)
  change ‖sourcePsiFullRootJacobian hp hp1 n c R b₀ φ‖ ≤ M
  calc
    ‖sourcePsiFullRootJacobian hp hp1 n c R b₀ φ‖ ≤
        ‖sourcePsiSelectedRootJacobian hp hp1 n c R b₀ φ‖ + 2 := by
      simpa only [sourcePsiFullRootJacobian,Coeff.deletedJacobianExtension,
        norm_ofNat] using hfull
    _ ≤ M := by dsimp [M]; exact add_le_add hQ le_rfl
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
    obtain ⟨U,hUopen,hpair,hlocal,hbound,hcoord,hdiff⟩ := hchart
    exact sourcePsiFullRootJacobian_retained_entry_eq_scalarMatrixEntry
      hp hp1 n m k a φ c R U hUopen hcoord hdiff hpair hn.1 hn.2
  exact hscalar.congr' heq.symm
  filter_upwards [hcharts] with n hchart
  obtain ⟨U,hUopen,hpair,_,_,hcoord,hdiff⟩ := hchart
  intro m k hmn hkn
  exact sourcePsiFullRootJacobian_retained_entry_eq_deriv
    hp hp1 n c R U hUopen hcoord hdiff
      (Coeff.deleteCoordinateTo n a) φ hpair m k hmn hkn

/-- Compatibility form of the real-centered construction, retaining
the original statement. -/
theorem exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit
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
      ∃ M : ℝ, 0 ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ,
          (∀ z ∈ sphere (c m) (R m), displacedRoots a k - z ≠ 0) →
            Tendsto (fun n : ℤ =>
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m)
              (Filter.comap Int.natAbs Filter.atTop)
              (𝓝 (sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)))) ∧
        ∃ Ktail : ℕ,
          (∀ m : ℤ, Ktail < m.natAbs →
            c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8) ∧
          ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
              (sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
                deriv (fun t : ℂ =>
                  sourcePsiDeletedEquationCoordinate hp hp1 n m
                    (Coeff.deleteCoordinateTo n a +
                      Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0 := by
  obtain ⟨c,R,_,hdata⟩ :=
    exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit_realCentered hp hp1 a φ hφ
  exact ⟨c,R,hdata⟩

/-- At fixed source data, the escaping full-space selected Jacobians
have a common operator-norm bound. -/
theorem exists_common_sourcePsi_fullJacobian_uniformNorm_at_natAbs
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
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M := by
  obtain ⟨c,R,hgeom,M,hM,hbound,_,_,_,_⟩ :=
    exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit hp hp1 a φ hφ
  exact ⟨c,R,hgeom,M,hM,hbound⟩

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
  obtain ⟨c,R,hgeom,M,hM,hbound,hentry,_,_,_⟩ :=
    exists_common_sourcePsi_fullJacobian_uniformNorm_entryLimit hp hp1 a φ hφ
  exact ⟨c,R,hgeom,hentry⟩

end NLS.ZakharovShabat
