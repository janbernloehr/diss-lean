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

end NLS.ZakharovShabat
