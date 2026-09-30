import NLS.ComplexAnalysis.ParametricCosineTerminal
import NLS.ZakharovShabat.SourceAngularCanonicalCosineSheetMatching
import NLS.ZakharovShabat.SourceAngularCanonicalCosineCommonDomain

/-!
# Source analyticity of beta at regular real Dirichlet terminals

Real interlacing supplies a regular base cosine angle. The analytic
implicit function theorem constructs its moving source-dependent angle.
The prescribed-sheet matching identifies the actual beta value with the
joint cosine primitive times an analytic coefficient using the actual
Dirichlet anti-discriminant. Thus beta itself is analytic near every real
source with a regular terminal, for every off-diagonal pair.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The ordinary real-source interlacing statement places the complex
boundary coordinate in the literal original periodic gap segment. -/
theorem canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (m : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 b φ m ∈ sourcePeriodicSegment hp hp1 φ m := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ m
  have hμ := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hreal m
  have hlim : l.im = 0 := sourceSpectralCluster_im_eq_zero hp hp1 φ hreal m (Or.inl rfl)
  have hrim : r.im = 0 := sourceSpectralCluster_im_eq_zero hp hp1 φ hreal m (Or.inr (Or.inl rfl))
  have hμim : μ.im = 0 := canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hreal m
  have hl : (l.re:ℂ) = l := by apply Complex.ext <;> simp [hlim]
  have hr : (r.re:ℂ) = r := by apply Complex.ext <;> simp [hrim]
  have hm : (μ.re:ℂ) = μ := by apply Complex.ext <;> simp [hμim]
  have hseg : μ.re ∈ segment ℝ l.re r.re := by
    rw [segment_eq_Icc (hμ.1.trans hμ.2)]
    exact hμ
  have himage : (μ.re:ℂ) ∈ segment ℝ (l.re:ℂ) (r.re:ℂ) := by
    have hmem := mem_image_of_mem Complex.ofRealAm.toLinearMap.toAffineMap hseg
    rw [image_segment] at hmem
    exact hmem
  change μ ∈ segment ℝ l r
  simpa only [hl,hr,hm] using himage

/-- The actual Dirichlet sheet's differential coefficient in canonical
cosine coordinates. Its denominator is the actual anti-discriminant at
the moving Dirichlet root. -/
def sourceAngularDirichletCosineCoefficient (hp : p ≠ ⊤) (hp1 : 1 < p) (m : ℤ) :
    ℂ × CoeffPair p → ℂ := fun x =>
  (-(canonicalPeriodicGap hp hp1 (periodOnePotential x.2) (periodOnePotential_mem x.2) m/2)*
      Complex.sin x.1) *
    (2*I*sourceStandardRootOmittedProduct hp hp1 m x.2
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet x.2 m)) /
    sourceAntiDiscriminantCandidate hp hp1 x.2
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet x.2 m)

namespace SourceAngularCanonicalCosineChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k} {W V : Set (CoeffPair p)}
  {Ω : Set ℂ} {c : ℤ → ℂ} {R : ℤ → ℝ}

/-- Evaluating the constructed cosine family at any regular Dirichlet
angle gives the actual beta value, including angles on the real axis. -/
theorem beta_eq_cosine_primitive
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (hmn : m ≠ n)
    (θ : ℂ) (hθ : θ ∈ Ω)
    (hpoint : sourceCanonicalCosinePoint hp hp1 m (θ,ψ) =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m)
    (hw : sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) ≠ 0) :
    sourceAngularBeta hp hp1 n m s ψ = sourceAngularDirichletCosineCoefficient hp hp1 m (θ,ψ)*
      sourceAngularCanonicalCosinePrimitive hp hp1 n m s (θ,ψ) := by
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 ψ m hw
  have hne := sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 ψ m _ _ hw hbase.1
  have hgap : canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m ≠
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro heq
    apply D.gap_ne_zero ψ hψ
    simp only [canonicalPeriodicGap,heq,sub_self]
  obtain ⟨F,A,E,hE⟩ := (D.disc_family ψ hψ).exists_dirichlet_primitive_data n m hmn hgap
    (D.endpoint_data ψ hψ) hne.1 hne.2
  have hmatch := D.sheet_matching ψ hψ n _ hw F E A hE.primitive θ hθ
    (by rw [hpoint]; exact hbase.1)
  rw [hpoint,hbase.2] at hmatch
  exact hE.beta_eq_terminal.trans (by simpa only [sourceAngularDirichletCosineCoefficient,neg_div] using hmatch)

/-- The literal Dirichlet cosine coefficient is jointly analytic near
every regular source terminal with an analytic moving boundary root. -/
theorem analyticAt_dirichletCosineCoefficient
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (θ : ℂ)
    (hμ : AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m) φ)
    (hw : sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) ≠ 0) :
    AnalyticAt ℂ (sourceAngularDirichletCosineCoefficient hp hp1 m) (θ,φ) := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hμ' : AnalyticAt ℂ μ φ := hμ
  have hμsnd : AnalyticAt ℂ (fun x : ℂ × CoeffPair p => μ x.2) (θ,φ) :=
    hμ'.comp (g := μ) (x := (θ,φ)) (f := fun x : ℂ × CoeffPair p => x.2) analyticAt_snd
  have hgraph : AnalyticAt ℂ (fun x : ℂ × CoeffPair p => (μ x.2,x.2)) (θ,φ) :=
    hμsnd.prod analyticAt_snd
  have hPbase : AnalyticAt ℂ (sourceStandardRootOmittedJointProduct hp hp1 m) (μ φ,φ) :=
    D.omitted_analytic (μ φ,φ) ⟨(D.disc_family φ hφ).dirichlet_mem_ball m,hφ⟩
  have hP : AnalyticAt ℂ (fun x : ℂ × CoeffPair p =>
      sourceStandardRootOmittedProduct hp hp1 m x.2 (μ x.2)) (θ,φ) :=
    hPbase.comp (g := sourceStandardRootOmittedJointProduct hp hp1 m) (x := (θ,φ))
      (f := fun x : ℂ × CoeffPair p => (μ x.2,x.2)) hgraph
  have hanti : AnalyticAt ℂ (fun x : ℂ × CoeffPair p =>
      sourceAntiDiscriminantCandidate hp hp1 x.2 (μ x.2)) (θ,φ) :=
    (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1
      (μ φ,φ) (mem_univ _)).comp (x := (θ,φ))
        (f := fun x : ℂ × CoeffPair p => (μ x.2,x.2)) hgraph
  have hγ : AnalyticAt ℂ (fun x : ℂ × CoeffPair p => canonicalPeriodicGap hp hp1
      (periodOnePotential x.2) (periodOnePotential_mem x.2) m) (θ,φ) :=
    (D.gap_analytic φ hφ).comp (x := (θ,φ)) (f := fun x : ℂ × CoeffPair p => x.2) analyticAt_snd
  exact (((hγ.div_const (c := (2:ℂ))).neg.mul
    (Complex.analyticAt_sin.comp (f := fun x : ℂ × CoeffPair p => x.1) analyticAt_fst)).mul
      (analyticAt_const.mul hP)).div hanti hw

/-- Actual off-diagonal beta is complex source analytic at a real source
whose Dirichlet terminal anti-discriminant is nonzero. -/
theorem analyticAt_beta_of_real_regular
    (D : SourceAngularCanonicalCosineChartData hp hp1 m s W V Ω c R)
    (φ : CoeffPair p) (hφ : φ ∈ V) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) (hmn : m ≠ n)
    (hw : sourceAntiDiscriminantCandidate hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) ≠ 0) :
    AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ := by
  let τ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  let δ : CoeffPair p → ℂ := fun ψ => canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m/2
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 φ m hw
  have hne := sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 φ m _ _ hw hbase.1
  have hl : τ φ-δ φ = canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hr : τ φ+δ φ = canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) m := by
    dsimp [τ,δ,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  obtain ⟨e,he,hsin,hpoint⟩ := exists_cosineGapPoint_regular_angle (τ φ) (δ φ) (μ φ)
    (by rw [hl,hr]; exact canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet φ hreal m)
    (by rw [hl]; exact hne.1) (by rw [hr]; exact hne.2)
  have hμ : AnalyticAt ℂ μ φ := analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
    hp hp1 .dirichlet φ hreal m
  obtain ⟨ε,hε,hεφ,hzeros⟩ := exists_analytic_parametricCosine_terminal τ δ μ φ e
    (D.midpoint_analytic φ hφ) ((D.gap_analytic φ hφ).div_const)
    hμ (div_ne_zero (D.gap_ne_zero φ hφ) (by norm_num)) hsin hpoint
  have hεΩ : ε φ ∈ Ω := by rw [hεφ]; exact D.angle_segment he
  have hgraph : AnalyticAt ℂ (fun ψ => (ε ψ,ψ)) φ := hε.prod analyticAt_id
  have hcandidate : AnalyticAt ℂ (fun ψ : CoeffPair p =>
      sourceAngularDirichletCosineCoefficient hp hp1 m (ε ψ,ψ)*
        sourceAngularCanonicalCosinePrimitive hp hp1 n m s (ε ψ,ψ)) φ :=
    ((D.analyticAt_dirichletCosineCoefficient φ hφ (ε φ) hμ hw).comp
      (f := fun ψ : CoeffPair p => (ε ψ,ψ)) hgraph).mul
      ((D.primitive_analytic n (ε φ,φ) ⟨hεΩ,hφ⟩).comp
        (f := fun ψ : CoeffPair p => (ε ψ,ψ)) hgraph)
  have hanti : ContinuousAt (fun ψ => sourceAntiDiscriminantCandidate hp hp1 ψ (μ ψ)) φ :=
    ((analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 (μ φ,φ) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (μ ψ,ψ)) (hμ.prod analyticAt_id)).continuousAt
  have hVevent : ∀ᶠ ψ in 𝓝 φ, ψ ∈ V := D.source_open.mem_nhds hφ
  have hangle : ∀ᶠ ψ in 𝓝 φ, ε ψ ∈ Ω := hε.continuousAt.eventually (D.angle_open.mem_nhds hεΩ)
  have heq : (fun ψ : CoeffPair p => sourceAngularDirichletCosineCoefficient hp hp1 m (ε ψ,ψ)*
      sourceAngularCanonicalCosinePrimitive hp hp1 n m s (ε ψ,ψ)) =ᶠ[𝓝 φ]
      sourceAngularBeta hp hp1 n m s := by
    filter_upwards [hzeros,hVevent,hangle,hanti.eventually_ne hw] with ψ hzero hψ hangle hne
    exact (D.beta_eq_cosine_primitive ψ hψ n hmn (ε ψ) hangle hzero hne).symm
  exact hcandidate.congr heq

end SourceAngularCanonicalCosineChartData

/-- One actual common beta domain supports source analyticity at every
real regular Dirichlet terminal and every off-diagonal numerator index.
All beta values and analytic boundary sequences, and the full original
simply connected psi extension, are retained. -/
theorem exists_sourceAngularBeta_common_domain_with_regularAnalyticity
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ W : Set (CoeffPair p), IsOpen W₀ ∧ IsSimplyConnected W₀ ∧
      realTypeSourceLocus p ⊆ W₀ ∧ IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
        SourcePsiSquaredGapComplexExtension hp hp1 W₀ s ∧
          (∀ b : BoundaryCondition, ∀ m : ℤ,
            AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
              canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) W) ∧
          (∀ ψ ∈ W, ∀ n m : ℤ, m ≠ n →
            sourceAngularBeta hp hp1 n m s ψ ∈ sourceAngularBetaValues hp hp1 n m s ψ ∧
              ∀ b ∈ sourceAngularBetaValues hp hp1 n m s ψ,
                b = sourceAngularBeta hp hp1 n m s ψ) ∧
          ∀ φ : realTypeSourceLocus p, ∀ n m : ℤ, m ≠ n →
            sourceAntiDiscriminantCandidate hp hp1 φ.val
              (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ.val m) ≠ 0 →
            AnalyticAt ℂ (sourceAngularBeta hp hp1 n m s) φ.val := by
  obtain ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hbeta,hcharts⟩ :=
    exists_sourceAngularBeta_common_domain_with_canonicalCosinePrimitives hp hp1
  refine ⟨W₀,W,hW₀,hW₀conn,hW₀real,hW,hWreal,hWW₀,s,hs,hroots,hbeta,?_⟩
  intro φ n m hmn hw
  have hbase := sourceAngularRootSheet_dirichlet_base hp hp1 φ.val m hw
  have hne := sourceAngularRootSheet_point_ne_periodic_endpoints hp hp1 φ.val m _ _ hw hbase.1
  have hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0 := by
    intro hzero
    have heq : canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m =
        canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m :=
      (sub_eq_zero.mp hzero).symm
    exact hne.1 (canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 .dirichlet
      φ.val φ.property m heq)
  obtain ⟨V,Ω,c,R,hφV,D⟩ := hcharts φ m hgap
  exact D.analyticAt_beta_of_real_regular φ.val hφV φ.property n hmn hw

end NLS.ZakharovShabat
