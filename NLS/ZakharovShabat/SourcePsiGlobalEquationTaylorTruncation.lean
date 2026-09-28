import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.SequenceSpaces.BoundedCoordinateAnalytic

/-!
# Uniform Taylor bounds for finite selected psi equations

Near any real-type source and deleted-root input, one selected
contour family yields an `ℓᵖ`-valued equation with analytic scalar
coordinates and a common norm bound. Consequently every finite
coordinate truncation has multilinear Taylor coefficients bounded
uniformly in the truncation.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A single selected contour chart around a real-type source has
analytic scalar equation coordinates and a common sequence-norm bound. -/
theorem exists_local_sourcePsi_globalEquation_coordinatewiseAnalyticBounded
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ U : Set (DeletedCoeff p n × CoeffPair p), ∃ C : ℝ,
        IsOpen U ∧ (a₀,φ) ∈ U ∧ 0 ≤ C ∧
        (∀ m : ℤ, AnalyticOnNhd ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m) U) ∧
        (∀ t ∈ U,
          ‖(sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p)‖ ≤ C) := by
  obtain ⟨U₀,hU₀open,hbase₀,_,c,R,_,_,hgeom,_,C,hC,hcoord,hbound,_,_⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic
      hp hp1 φ hφ n a₀
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let U : Set (DeletedCoeff p n × CoeffPair p) :=
    U₀ ∩ {t | t.2 ∈ W}
  have hUopen : IsOpen U :=
    hU₀open.inter (hWopen.preimage continuous_snd)
  have hbase : (a₀,φ) ∈ U := ⟨hbase₀,hrealW hφ⟩
  let F : DeletedCoeff p n × CoeffPair p → Coeff p :=
    fun t => (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p)
  have hnorm (t : DeletedCoeff p n × CoeffPair p) (ht : t ∈ U) :
      ‖F t‖ ≤ C := by
    simpa [F] using hbound t ht.1
  have hHanalytic (t : DeletedCoeff p n × CoeffPair p) :
      AnalyticAt ℂ
        (fun b : DeletedCoeff p n × CoeffPair p =>
          ((b.1 : Coeff p),b.2)) t :=
    ((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt t.1).comp
      analyticAt_fst).prod analyticAt_snd)
  have hscalar (m : ℤ) : AnalyticOnNhd ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => F t m) U := by
    have hraw : AnalyticOnNhd ℂ
        (fun t : DeletedCoeff p n × CoeffPair p =>
          sourcePsiEquationCoordinate hp hp1 n m
            (t.1 : Coeff p) t.2 (c m) (R m)) U := by
      intro t ht
      obtain ⟨hR,_,_,hcircle⟩ := hgeom t ht.1 m
      have hAt := analyticAt_sourcePsiEquationCoordinate_of_contour_domain
        hp hp1 n m (t.1 : Coeff p) t.2
          (c m) (R m) hR.le W ht.2
          (hdata n).1 (hdata n).2 hcircle
      exact hAt.comp
        (f := fun b : DeletedCoeff p n × CoeffPair p =>
          ((b.1 : Coeff p),b.2)) (hHanalytic t)
    apply hraw.congr hUopen
    intro t ht
    exact (hcoord t ht.1 m).symm
  exact ⟨c,R,U,C,hUopen,hbase,hC,hscalar,hnorm⟩

/-- All finite coordinate truncations of one selected psi equation
have a common geometric bound on every multilinear Taylor
coefficient at a real-type base point. -/
theorem exists_local_sourcePsi_globalEquation_uniformTruncateTaylor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ ρ M : ℝ,
      0 < ρ ∧ 0 ≤ M ∧
      ∀ s : Finset ℤ, ∀ k : ℕ,
        ‖NLS.ComplexAnalysis.complexTaylorSeries
          (fun t : DeletedCoeff p n × CoeffPair p =>
            NLS.Coeff.truncate s
              (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p))
          (a₀,φ) k‖ ≤ (4*Real.exp 1/ρ)^k*M := by
  obtain ⟨c,R,U,C,hUopen,hbase,hC,hscalar,hnorm⟩ :=
    exists_local_sourcePsi_globalEquation_coordinatewiseAnalyticBounded
      hp hp1 φ hφ n a₀
  let F : DeletedCoeff p n × CoeffPair p → Coeff p :=
    fun t => (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p)
  obtain ⟨ρ,hρ,_,hTaylor⟩ :=
    NLS.Coeff.exists_uniform_truncate_taylor_bound
      F hUopen hscalar C hnorm (a₀,φ) hbase
  exact ⟨c,R,ρ,C,hρ,hC,hTaylor⟩

/-- The selected psi equation is Banach-space analytic on one contour
chart around each real-type base point. Its analytic structure follows
from the uniformly bounded scalar contour coordinates. -/
theorem exists_local_sourcePsi_globalEquation_analyticOnNhd
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ U : Set (DeletedCoeff p n × CoeffPair p),
        IsOpen U ∧ (a₀,φ) ∈ U ∧
        AnalyticOnNhd ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p)) U := by
  obtain ⟨c,R,U,C,hUopen,hbase,_,hscalar,hnorm⟩ :=
    exists_local_sourcePsi_globalEquation_coordinatewiseAnalyticBounded
      hp hp1 φ hφ n a₀
  refine ⟨c,R,U,hUopen,hbase,?_⟩
  exact NLS.Coeff.analyticOnNhd_of_bounded_coordinatewise
    (fun t : DeletedCoeff p n × CoeffPair p =>
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p))
    hUopen hscalar C hnorm

/-- The selected equation is analytic with values in the actual
deleted-coordinate Banach space used by the implicit root theorem. -/
theorem exists_local_sourcePsi_deletedEquation_analyticOnNhd
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∃ U : Set (DeletedCoeff p n × CoeffPair p),
        IsOpen U ∧ (a₀,φ) ∈ U ∧
        AnalyticOnNhd ℂ
          (fun t : DeletedCoeff p n × CoeffPair p =>
            sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U := by
  obtain ⟨c,R,U,hUopen,hbase,hanalytic⟩ :=
    exists_local_sourcePsi_globalEquation_analyticOnNhd
      hp hp1 φ hφ n a₀
  refine ⟨c,R,U,hUopen,hbase,?_⟩
  have hproject : AnalyticOnNhd ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        Coeff.deleteCoordinateTo n
          (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p)) U :=
    (Coeff.deleteCoordinateTo (p := p) n).comp_analyticOnNhd hanalytic
  apply hproject.congr hUopen
  intro t _
  apply Subtype.ext
  exact (Coeff.deleteCoordinate_eq_self_iff n
    (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p)).2
    (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2).property

/-- Any selected contour chart whose equation is differentiable and
whose scalar coordinates use valid canonical-root circles is analytic
near a real-type base point, with values in the deleted Banach space.
The contour family may be chosen independently of the norm-bound
construction above. -/
theorem exists_analytic_sourcePsi_deletedEquation_on_contourChart
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    {U : Set (DeletedCoeff p n × CoeffPair p)}
    (hUopen : IsOpen U) (hbase : (a₀,φ) ∈ U)
    (hgeom : ∀ t ∈ U, ∀ m : ℤ,
      0 < R m ∧ sphere (c m) (R m) ⊆
        sourceCanonicalRootDomain hp hp1 t.2)
    (hcoord : ∀ t ∈ U, ∀ m : ℤ,
      (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p) m =
        sourcePsiEquationCoordinate hp hp1 n m
          (t.1 : Coeff p) t.2 (c m) (R m))
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U) :
    ∃ V : Set (DeletedCoeff p n × CoeffPair p),
      IsOpen V ∧ (a₀,φ) ∈ V ∧ V ⊆ U ∧
      AnalyticOnNhd ℂ
        (fun t : DeletedCoeff p n × CoeffPair p =>
          sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) V := by
  obtain ⟨W,hWopen,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  let V : Set (DeletedCoeff p n × CoeffPair p) := U ∩ {t | t.2 ∈ W}
  have hVopen : IsOpen V :=
    hUopen.inter (hWopen.preimage continuous_snd)
  have hbaseV : (a₀,φ) ∈ V := ⟨hbase,hrealW hφ⟩
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  have hHanalytic (t : DeletedCoeff p n × CoeffPair p) :
      AnalyticAt ℂ
        (fun b : DeletedCoeff p n × CoeffPair p =>
          ((b.1 : Coeff p),b.2)) t :=
    ((((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.analyticAt t.1).comp
      analyticAt_fst).prod analyticAt_snd)
  have hscalar (m : ℤ) : AnalyticOnNhd ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p) m) V := by
    have hraw : AnalyticOnNhd ℂ
        (fun t : DeletedCoeff p n × CoeffPair p =>
          sourcePsiEquationCoordinate hp hp1 n m
            (t.1 : Coeff p) t.2 (c m) (R m)) V := by
      intro t ht
      obtain ⟨hR,hcircle⟩ := hgeom t ht.1 m
      have hAt := analyticAt_sourcePsiEquationCoordinate_of_contour_domain
        hp hp1 n m (t.1 : Coeff p) t.2
          (c m) (R m) hR.le W ht.2
          (hdata n).1 (hdata n).2 hcircle
      exact hAt.comp
        (f := fun b : DeletedCoeff p n × CoeffPair p =>
          ((b.1 : Coeff p),b.2)) (hHanalytic t)
    apply hraw.congr hVopen
    intro t ht
    exact (hcoord t ht.1 m).symm
  have hcont : ContinuousOn
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p)) V :=
    continuous_subtype_val.comp_continuousOn
      (hdiff.mono (fun _ ht => ht.1)).continuousOn
  have hanalyticCoe : AnalyticOnNhd ℂ
      (fun t : DeletedCoeff p n × CoeffPair p => (F t : Coeff p)) V :=
    NLS.Coeff.analyticOnNhd_of_coordinatewise_of_continuousOn
      (fun t => (F t : Coeff p)) hVopen hscalar hcont
  have hproject : AnalyticOnNhd ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        Coeff.deleteCoordinateTo n (F t : Coeff p)) V :=
    (Coeff.deleteCoordinateTo (p := p) n).comp_analyticOnNhd hanalyticCoe
  have hdeleted : AnalyticOnNhd ℂ F V := by
    apply hproject.congr hVopen
    intro t _
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n (F t : Coeff p)).2 (F t).property
  exact ⟨V,hVopen,hbaseV,fun _ ht => ht.1,hdeleted⟩

/-- The full selected psi equation, beyond its finite truncations,
has one geometric norm bound for every Fréchet Taylor coefficient at
a real-type base point. -/
theorem exists_local_sourcePsi_globalEquation_uniformTaylor
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ ρ M : ℝ,
      0 < ρ ∧ 0 ≤ M ∧
      ∀ k : ℕ,
        ‖NLS.ComplexAnalysis.complexTaylorSeries
          (fun t : DeletedCoeff p n × CoeffPair p =>
            (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p))
          (a₀,φ) k‖ ≤ (4*Real.exp 1/ρ)^k*M := by
  obtain ⟨c,R,U,C,hUopen,hbase,hC,hscalar,hnorm⟩ :=
    exists_local_sourcePsi_globalEquation_coordinatewiseAnalyticBounded
      hp hp1 φ hφ n a₀
  obtain ⟨ρ,hρ,_,hTaylor⟩ :=
    NLS.Coeff.exists_uniform_taylor_bound_of_bounded_coordinatewise
      (fun t : DeletedCoeff p n × CoeffPair p =>
        (sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 : Coeff p))
      hUopen hscalar C hnorm (a₀,φ) hbase
  exact ⟨c,R,ρ,C,hρ,hC,hTaylor⟩

end NLS.ZakharovShabat
