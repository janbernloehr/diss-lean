import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.ComplexAnalysis.LocalRealAxisDerivative

/-!
# Real Jacobian entries of the global psi equation

The selected psi equation is holomorphic near every real-type source
and real on the real displaced-root locus. Restriction to a real
retained-root line therefore has a real complex derivative. This
argument covers every matrix entry without a separate contour
avoidance hypothesis.
-/

noncomputable section
open Set Metric Complex Filter
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Changing one deleted root by a real amount preserves the real
displaced-root locus. -/
theorem displacedRoots_add_deletedSingle_real
    (n k : ℤ) (hkn : k ≠ n) (a : DeletedCoeff p n)
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (y : ℝ) (j : ℤ) :
    (displacedRoots ((a+Coeff.deletedSingleCLM n k hkn (y:ℂ) :
      DeletedCoeff p n) : Coeff p) j).im = 0 := by
  have ha := hroots j
  simp only [displacedRoots, Submodule.coe_add, Coeff.deletedSingleCLM_coe,
    lp.coeFn_add, Pi.add_apply, Complex.add_im] at ha ⊢
  by_cases hj : j = k
  · subst j
    have hπ : ((Real.pi : ℂ) * (k:ℂ)).im = 0 := by simp
    have ha' : ((a : Coeff p) k).im = 0 := by simpa only [hπ, zero_add] using ha
    simp [ha']
  · rw [lp.single_apply_ne _ _ _ hj]
    simpa using ha

/-- Every retained-root directional derivative of the selected
holomorphic equation has a real coordinate at real data. -/
theorem deriv_sourcePsiSelectedEquationSequence_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a₀ : DeletedCoeff p n) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (hroots : ∀ j : ℤ, (displacedRoots (a₀ : Coeff p) j).im = 0)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U) (hbase : (a₀,φ) ∈ U)
    (hreal : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (m k : ℤ) (hkn : k ≠ n) :
    (deriv (fun z : ℂ =>
      (sourcePsiSelectedEquationSequence hp hp1 n c R
        (a₀+Coeff.deletedSingleCLM n k hkn z) φ : Coeff p) m) 0).im = 0 := by
  let line : ℂ → DeletedCoeff p n × CoeffPair p :=
    fun z => (a₀+Coeff.deletedSingleCLM n k hkn z,φ)
  have hline0 : line 0 = (a₀,φ) := by simp [line]
  have hlineDiff : DifferentiableAt ℂ line 0 := by
    dsimp [line]
    fun_prop
  have hF : DifferentiableAt ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2)
      (a₀,φ) :=
    (hdiff (a₀,φ) hbase).differentiableAt (hUopen.mem_nhds hbase)
  have heval : Differentiable ℂ
      (fun b : DeletedCoeff p n => (b : Coeff p) m) := by
    let L : DeletedCoeff p n →L[ℂ] ℂ :=
      (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
    change Differentiable ℂ L
    exact L.differentiable
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => sourcePsiSelectedEquationSequence hp hp1 n c R
        (line z).1 (line z).2) 0 := by
    rw [← hline0] at hF
    exact hF.comp 0 hlineDiff
  have hf : DifferentiableAt ℂ
      (fun z : ℂ =>
        (sourcePsiSelectedEquationSequence hp hp1 n c R
          (a₀+Coeff.deletedSingleCLM n k hkn z) φ : Coeff p) m) 0 := by
    change DifferentiableAt ℂ
      ((fun b : DeletedCoeff p n => (b : Coeff p) m) ∘
        (fun z : ℂ => sourcePsiSelectedEquationSequence hp hp1 n c R
          (line z).1 (line z).2)) 0
    exact (heval _).comp 0 hcomp
  have hlineContR : ContinuousAt (fun y : ℝ => line (y:ℂ)) 0 := by
    fun_prop
  have hUevent : ∀ᶠ y : ℝ in 𝓝 0, line (y:ℂ) ∈ U := by
    apply hlineContR.eventually
    change U ∈ 𝓝 (line (0:ℂ))
    rw [hline0]
    exact hUopen.mem_nhds hbase
  have hr : ∀ᶠ y : ℝ in 𝓝 0,
      ((sourcePsiSelectedEquationSequence hp hp1 n c R
        (a₀+Coeff.deletedSingleCLM n k hkn (y:ℂ)) φ : Coeff p) m).im = 0 := by
    filter_upwards [hUevent] with y hy
    have hlineRoots : ∀ j : ℤ,
        (displacedRoots ((line (y:ℂ)).1 : Coeff p) j).im = 0 := by
      intro j
      exact displacedRoots_add_deletedSingle_real n k hkn a₀ hroots y j
    simpa only [line] using hreal (line (y:ℂ)) hy hφ hlineRoots m
  exact NLS.ComplexAnalysis.HasDerivAt.im_eq_zero_of_eventually_real
    _ _ 0 hf.hasDerivAt hr

/-- Lemma 12.5's reality assertion for all entries of the locally
selected global psi Jacobian. -/
theorem exists_local_sourcePsi_realJacobian_entries
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n)
    (hroots : ∀ j : ℤ, (displacedRoots (a₀ : Coeff p) j).im = 0) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∀ m k : ℤ, ∀ hkn : k ≠ n,
        (deriv (fun z : ℂ =>
          (sourcePsiSelectedEquationSequence hp hp1 n c R
            (a₀+Coeff.deletedSingleCLM n k hkn z) φ : Coeff p) m) 0).im = 0 := by
  obtain ⟨U,hUopen,hbase,K,c,R,hcReal,hchoice,C,hC,hcoord,hbound,
    hreal,hdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic
      hp hp1 φ hφ n a₀
  exact ⟨c,R,fun m k hkn =>
    deriv_sourcePsiSelectedEquationSequence_im_eq_zero
      hp hp1 n a₀ φ hφ hroots c R U hUopen hbase hreal hdiff m k hkn⟩

end NLS.ZakharovShabat
