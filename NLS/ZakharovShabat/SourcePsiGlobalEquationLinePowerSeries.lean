import NLS.ZakharovShabat.SourcePsiGlobalEquationAnalytic
import NLS.ComplexAnalysis.BanachHolomorphicLineJets

/-!
# Power series of the selected psi equation on complex lines

On a selected contour chart near any real-type source, the full
deleted-sequence equation has a Banach-valued power series along
every complex line through the chosen root/source input. One disc
radius and one Cauchy coefficient bound work for all unit directions.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal NNReal
namespace NLS.ZakharovShabat

/-- The full selected psi equation has a power series on each unit
complex line through a real-type base point, with one common disc
radius and a uniform bound on every line Taylor derivative. -/
theorem exists_local_sourcePsi_globalEquation_linePowerSeries
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ r : ℝ≥0, ∃ C : ℝ,
      0 < r ∧ 0 ≤ C ∧
      ∀ v : DeletedCoeff p n × CoeffPair p, ‖v‖ ≤ 1 →
        ∃ P : FormalMultilinearSeries ℂ ℂ (DeletedCoeff p n),
          HasFPowerSeriesOnBall
            (fun z : ℂ =>
              sourcePsiSelectedEquationSequence hp hp1 n c R
                (((a₀,φ) + z • v).1) (((a₀,φ) + z • v).2)) P 0 r ∧
          ∀ k : ℕ,
            ‖iteratedDeriv k
              (fun z : ℂ =>
                sourcePsiSelectedEquationSequence hp hp1 n c R
                  (((a₀,φ) + z • v).1) (((a₀,φ) + z • v).2)) 0‖ ≤
              k.factorial * C / (r : ℝ)^k := by
  obtain ⟨U,hUopen,hbase,_,c,R,_,_,_,_,C,hC,_,hbound,_,hFdiff⟩ :=
    exists_local_sourcePsi_globalEquation_formula_analytic hp hp1 φ hφ n a₀
  let x : DeletedCoeff p n × CoeffPair p := (a₀,φ)
  let F : DeletedCoeff p n × CoeffPair p → DeletedCoeff p n :=
    fun t => sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hUopen x hbase
  let r : ℝ≥0 := ⟨δ/3,by positivity⟩
  have hr : 0 < r := by change 0 < δ/3; positivity
  have hr2 : 2*(r : ℝ) ≤ δ := by change 2*(δ/3) ≤ δ; linarith
  have hball2 : ball x (2*(r : ℝ)) ⊆ U :=
    (ball_subset_ball hr2).trans hball
  have hdiff : DifferentiableOn ℂ F (ball x (2*(r : ℝ))) :=
    hFdiff.mono hball2
  have hnorm (t : DeletedCoeff p n × CoeffPair p)
      (ht : t ∈ ball x (2*(r : ℝ))) : ‖F t‖ ≤ C :=
    hbound t (hball2 ht)
  refine ⟨c,R,r,C,hr,hC,?_⟩
  intro v hv
  obtain ⟨P,hP⟩ :=
    NLS.ComplexAnalysis.exists_linePowerSeriesOnBall_of_ball_differentiable
      F x r hr hdiff v hv
  refine ⟨P,hP,?_⟩
  intro k
  exact NLS.ComplexAnalysis.norm_iteratedDeriv_affineLine_le_of_ball_bound
    F x (r : ℝ) C (by exact_mod_cast hr) hdiff hnorm v hv k

/-- On one selected contour chart, every line Taylor jet of the
Banach-valued equation is homogeneous under contractions of its
root/source direction. The contour family and disc radius are fixed
independently of the direction and derivative order. -/
theorem exists_local_sourcePsi_globalEquation_lineJet_smul
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (a₀ : DeletedCoeff p n) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ r : ℝ≥0,
      0 < r ∧
      ∀ v : DeletedCoeff p n × CoeffPair p, ‖v‖ ≤ 1 →
        ∀ b : ℂ, ‖b‖ ≤ 1 →
          ∀ k : ℕ,
            iteratedDeriv k
              (fun z : ℂ =>
                sourcePsiSelectedEquationSequence hp hp1 n c R
                  (((a₀,φ) + z • (b • v)).1)
                  (((a₀,φ) + z • (b • v)).2)) 0 =
              b^k • iteratedDeriv k
                (fun z : ℂ =>
                  sourcePsiSelectedEquationSequence hp hp1 n c R
                    (((a₀,φ) + z • v).1)
                    (((a₀,φ) + z • v).2)) 0 := by
  obtain ⟨c,R,r,_,hr,_,hline⟩ :=
    exists_local_sourcePsi_globalEquation_linePowerSeries
      hp hp1 φ hφ n a₀
  refine ⟨c,R,r,hr,?_⟩
  intro v hv b hb k
  obtain ⟨P,hP,_⟩ := hline v hv
  let g : ℂ → DeletedCoeff p n := fun z =>
    sourcePsiSelectedEquationSequence hp hp1 n c R
      (((a₀,φ) + z • v).1) (((a₀,φ) + z • v).2)
  have hgAnalytic : AnalyticOnNhd ℂ g (ball 0 (r : ℝ)) := by
    simpa only [Metric.eball_coe] using hP.analyticOnNhd
  have hgSmooth : ContDiffOn ℂ k g (ball 0 (r : ℝ)) :=
    hgAnalytic.contDiffOn_of_completeSpace
  have hfun :
      (fun z : ℂ =>
        sourcePsiSelectedEquationSequence hp hp1 n c R
          (((a₀,φ) + z • (b • v)).1)
          (((a₀,φ) + z • (b • v)).2)) =
      (fun z : ℂ => g (b*z)) := by
    funext z
    simp only [g,smul_smul]
    rw [mul_comm z b]
  rw [hfun]
  exact NLS.ComplexAnalysis.iteratedDeriv_comp_const_mul_of_contDiffOn_ball
    g (r : ℝ) (by exact_mod_cast hr) k hgSmooth b hb

end NLS.ZakharovShabat
