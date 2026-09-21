import NLS.ZakharovShabat.BoundaryCharacteristicUniform
import NLS.ZakharovShabat.CentralBoundaryPolynomialAnalytic
import NLS.ZakharovShabat.PeriodOneBoundaryCharacteristic
import NLS.ComplexAnalysis.LocalAnalyticApproximation
import NLS.ComplexAnalysis.BanachSmoothAnalytic

/-!
# Joint analyticity of the ordinary boundary characteristic functions
Uniform approximation on actual Banach neighborhoods by jointly analytic
intrinsic polynomials proves joint analyticity of the infinite products.
The source interval extension gives Lemma 9.1(i) for both ordinary boundary
conditions, including at colliding eigenvalues and characteristic zeros.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Intrinsic boundary characteristics have uniform analytic approximation on joint open balls. -/
theorem localUniformAnalyticApproximation_boundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) :
    NLS.ComplexAnalysis.HasLocalUniformAnalyticApproximation
      (fun M (t : ℂ × dirichletSubspace (p := p)) => b.normalizedCentralPolynomial hp t.2.val t.2.property M t.1)
      (fun t => b.characteristic hp t.2.val t.2.property t.1) := by
  intro t
  obtain ⟨U,ho,_,ht,_,hU⟩ := exists_uniform_boundaryCharacteristic hp hp1 t.2
  obtain ⟨N,V,_,hV,_,htV,_,hA⟩ := exists_uniform_analytic_normalizedCentralBoundaryPolynomials hp t.2
  have hn : ball t.1 1 ×ˢ (U ∩ V) ∈ 𝓝 t :=
    prod_mem_nhds (ball_mem_nhds t.1 (by norm_num)) ((ho.inter hV).mem_nhds ⟨ht,htV⟩)
  obtain ⟨r,hr,hs⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r/2,half_pos hr,?_,?_⟩
  · rw [show 2*(r/2) = r by ring]
    apply (hU b _ (isCompact_closedBall t.1 1)).mono
    exact fun x hx => ⟨ball_subset_closedBall (hs hx).1,(hs hx).2.1⟩
  · filter_upwards [eventually_ge_atTop N] with M hM
    apply (hA b M hM).mono
    rw [show 2*(r/2) = r by ring]
    exact fun x hx => ⟨mem_univ _,(hs hx).2.2⟩

/-- All joint complex Fréchet derivatives exist and are continuous. -/
theorem contDiff_boundaryCharacteristic_joint (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) :
    ContDiff ℂ ∞ (fun t : ℂ × dirichletSubspace (p := p) => b.characteristic hp t.2.val t.2.property t.1) :=
  (localUniformAnalyticApproximation_boundaryCharacteristic hp hp1 b).contDiff

/-- Joint polynomial derivatives converge uniformly in operator norm on a neighborhood of every point. -/
theorem exists_uniform_fderiv_boundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (t : ℂ × dirichletSubspace (p := p)) :
    ∃ r : ℝ, 0 < r ∧ TendstoUniformlyOn
      (fun M => fderiv ℂ (fun t : ℂ × dirichletSubspace (p := p) =>
        b.normalizedCentralPolynomial hp t.2.val t.2.property M t.1))
      (fderiv ℂ (fun t : ℂ × dirichletSubspace (p := p) => b.characteristic hp t.2.val t.2.property t.1))
      atTop (ball t r) :=
  (localUniformAnalyticApproximation_boundaryCharacteristic hp hp1 b).uniform_fderiv t

/-- Both intrinsic boundary products are jointly Banach-space analytic, including all spectral zeros. -/
theorem analyticOnNhd_boundaryCharacteristic_joint (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun t : ℂ × dirichletSubspace (p := p) => b.characteristic hp t.2.val t.2.property t.1) univ :=
  NLS.ComplexAnalysis.analyticOnNhd_of_complexSmooth _ (contDiff_boundaryCharacteristic_joint hp hp1 b)

/-- Every mixed iterated Fréchet derivative is itself jointly analytic. -/
theorem analyticOnNhd_iteratedFDeriv_boundaryCharacteristic (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedFDeriv ℂ n
      (fun t : ℂ × dirichletSubspace (p := p) => b.characteristic hp t.2.val t.2.property t.1)) univ :=
  (analyticOnNhd_boundaryCharacteristic_joint hp hp1 b).iteratedFDeriv n

/-- The ordinary source period-one boundary characteristic is jointly analytic in potential and spectral parameter. -/
theorem analyticOnNhd_periodOneBoundaryCharacteristic_joint (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b t.2 t.1) univ := by
  let F := periodOneBoundaryPotential hp hp1
  intro t _
  exact AnalyticAt.comp
    (g := fun a : ℂ × dirichletSubspace (p := p) => b.characteristic hp a.2.val a.2.property a.1)
    (f := fun a : ℂ × CoeffPair p => (a.1,F a.2)) (x := t)
    (analyticOnNhd_boundaryCharacteristic_joint hp hp1 b (t.1,F t.2) (mem_univ _))
    (analyticAt_fst.prod (AnalyticAt.comp (g := F) (f := fun a : ℂ × CoeffPair p => a.2)
      (x := t) (F.analyticAt t.2) analyticAt_snd))

/-- Lemma 9.1(i) for either ordinary source boundary condition: joint analyticity and exact actual zeros. -/
theorem periodOneBoundaryCharacteristic_joint_spec (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b t.2 t.1) univ ∧
      ∀ (φ : CoeffPair p) (z : ℂ), periodOneBoundaryCharacteristic hp hp1 b φ z = 0 ↔
        z ∈ b.spectrum hp (periodOneBoundaryPotential hp hp1 φ).val (periodOneBoundaryPotential hp hp1 φ).property :=
  ⟨analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b,
    periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b⟩

end NLS.ZakharovShabat
