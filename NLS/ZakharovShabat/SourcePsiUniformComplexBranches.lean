import NLS.ZakharovShabat.SourcePsiUniformEquationEstimates
import NLS.ComplexAnalysis.QuantitativeTriangularDerivative
import NLS.ComplexAnalysis.QuantitativeAnalyticInverse

/-!
# Complex psi zero branches on an index-independent source ball

The quantitative inverse theorem applies to the equation-and-source
map. The tube bounds give one inverse norm bound and one derivative
Lipschitz constant, hence one source ball for all deleted indices.
The branches are analytic, solve the actual glued equations, retain
their canonical real base values, and are unique in a common root ball.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourcePsiUniformComplexBranchFamily
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    (D : SourcePsiUniformEquationTube hp hp1 φ) where
  sourceRadius : ℝ
  rootRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  rootRadius_pos : 0 < rootRadius
  sourceRadius_le_rootRadius : sourceRadius ≤ rootRadius
  rootRadius_lt : rootRadius < D.radius
  branch : (n : ℤ) → CoeffPair p → DeletedCoeff p n
  analytic : ∀ n, AnalyticOnNhd ℂ (branch n) (ball φ.val sourceRadius)
  at_base : ∀ n, branch n φ.val = sourcePsiGapRoot hp hp1 n φ
  graph : ∀ n, ∀ ψ ∈ ball φ.val sourceRadius,
    (branch n ψ,ψ) ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) rootRadius
  equation_zero : ∀ n, ∀ ψ ∈ ball φ.val sourceRadius, D.equation n (branch n ψ,ψ) = 0
  unique : ∀ n, ∀ ψ ∈ ball φ.val sourceRadius,
    ∀ b ∈ ball (sourcePsiGapRoot hp hp1 n φ) rootRadius,
      D.equation n (b,ψ) = 0 → b = branch n ψ

theorem nonempty_sourcePsiUniformComplexBranchFamily
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    (D : SourcePsiUniformEquationTube hp hp1 φ) :
    Nonempty (SourcePsiUniformComplexBranchFamily D) := by
  classical
  let J := 2*D.normBound/D.radius
  let L := 4*D.normBound/D.radius^2
  let B := D.inverseBound*(1+J)+1
  let ρ := NLS.ComplexAnalysis.quantitativeInverseJointRadius D.radius B L
  let δ := NLS.ComplexAnalysis.quantitativeInverseImageRadius D.radius B L
  have hR := D.radius_pos
  have hC := D.normBound_nonneg
  have hM := D.inverseBound_nonneg
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hB : 1 ≤ B := le_add_of_nonneg_left (by positivity)
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hρ : 0 < ρ := NLS.ComplexAnalysis.quantitativeInverseJointRadius_pos hR hBpos hL
  have hδ : 0 < δ := NLS.ComplexAnalysis.quantitativeInverseImageRadius_pos hR hBpos hL
  have hρR : ρ < D.radius := (min_le_left _ _).trans_lt (by linarith)
  have hδρ : δ ≤ ρ := by
    change ρ/(8*B) ≤ ρ
    apply (div_le_iff₀ (by positivity : 0 < 8*B)).mpr
    nlinarith [mul_nonneg hρ.le (by linarith : 0 ≤ 8*B-1)]
  let H : (n : ℤ) → DeletedCoeff p n × CoeffPair p → DeletedCoeff p n × CoeffPair p :=
    fun n q => (D.equation n q,q.2)
  have houter (n : ℤ) : ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius ⊆
      ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius) := ball_subset_ball (by linarith)
  have hHd (n : ℤ) (q : DeletedCoeff p n × CoeffPair p)
      (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :
      fderiv ℂ (H n) q = (fderiv ℂ (D.equation n) q).prod
        (ContinuousLinearMap.snd ℂ (DeletedCoeff p n) (CoeffPair p)) := by
    simpa only [H,fderiv_snd] using
      (D.differentiableAt n q (houter n hq)).fderiv_prodMk differentiableAt_snd
  have hHana (n : ℤ) : AnalyticOnNhd ℂ (H n)
      (ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :=
    fun q hq => (D.analytic n q (houter n hq)).prod analyticAt_snd
  have hHbij (n : ℤ) (q : DeletedCoeff p n × CoeffPair p)
      (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :
      Function.Bijective (fderiv ℂ (H n) q) := by
    rw [hHd n q hq]
    apply NLS.ComplexAnalysis.bijective_banach_triangular_derivative
    rw [← D.root_fderiv_eq n q (houter n hq)]
    exact D.bijective_root_fderiv n q (houter n hq)
  have hHLip (n : ℤ) (q : DeletedCoeff p n × CoeffPair p)
      (hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius)
      (u : DeletedCoeff p n × CoeffPair p)
      (hu : u ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius) :
      ‖fderiv ℂ (H n) q-fderiv ℂ (H n) u‖ ≤ L*‖q-u‖ := by
    rw [hHd n q hq,hHd n u hu]
    have heq : (fderiv ℂ (D.equation n) q).prod
        (ContinuousLinearMap.snd ℂ (DeletedCoeff p n) (CoeffPair p))-
        (fderiv ℂ (D.equation n) u).prod
        (ContinuousLinearMap.snd ℂ (DeletedCoeff p n) (CoeffPair p)) =
        (fderiv ℂ (D.equation n) q-fderiv ℂ (D.equation n) u).prod 0 := by
      apply ContinuousLinearMap.ext
      intro x
      apply Prod.ext <;> simp
    rw [heq,ContinuousLinearMap.opNorm_prod]
    change max ‖fderiv ℂ (D.equation n) q-fderiv ℂ (D.equation n) u‖
      ‖(0 : (DeletedCoeff p n × CoeffPair p) →L[ℂ] CoeffPair p)‖ ≤ L*‖q-u‖
    rw [ContinuousLinearMap.opNorm_zero,max_eq_left (ContinuousLinearMap.opNorm_nonneg _)]
    exact D.norm_fderiv_sub_le n q u hq hu
  have hTdata (n : ℤ) : ∃ T : (DeletedCoeff p n × CoeffPair p) ≃L[ℂ] (DeletedCoeff p n × CoeffPair p),
      (T : (DeletedCoeff p n × CoeffPair p) →L[ℂ] (DeletedCoeff p n × CoeffPair p)) =
        fderiv ℂ (H n) (sourcePsiGapRoot hp hp1 n φ,φ.val) ∧
      ‖(T.symm : (DeletedCoeff p n × CoeffPair p) →L[ℂ] (DeletedCoeff p n × CoeffPair p))‖ ≤ B := by
    let q := (sourcePsiGapRoot hp hp1 n φ,φ.val)
    have hq : q ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius := mem_ball_self hR
    obtain ⟨S,hQS,hSQ,hS⟩ := D.inverse n q (houter n hq)
    rw [D.root_fderiv_eq n q (houter n hq)] at hQS hSQ
    obtain ⟨T,hT,hTB⟩ := NLS.ComplexAnalysis.exists_triangularLinearEquiv_norm_bound
      (fderiv ℂ (D.equation n) q) S hQS hSQ
    refine ⟨T,hT.trans (hHd n q hq).symm,hTB.trans ?_⟩
    change ‖S‖*(1+‖fderiv ℂ (D.equation n) q‖)+1 ≤ D.inverseBound*(1+J)+1
    gcongr
    exact D.norm_fderiv_le n q hq
  choose T hT hTB using hTdata
  have hinverse (n : ℤ) := NLS.ComplexAnalysis.exists_analytic_inverse_on_uniform_ball
    (H n) (sourcePsiGapRoot hp hp1 n φ,φ.val) D.radius B L hR hB hL (hHana n)
      (T n) (hT n) (hTB n) (hHLip n) (hHbij n)
  choose g hgAna hgBase hgData using hinverse
  have hHbase (n : ℤ) : H n (sourcePsiGapRoot hp hp1 n φ,φ.val) = (0,φ.val) := by
    simp only [H,D.zero]
  have hmem (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val δ) :
      (0,ψ) ∈ ball (H n (sourcePsiGapRoot hp hp1 n φ,φ.val)) δ := by
    rw [hHbase n]
    simpa only [mem_ball,dist_prod_same_left] using hψ
  let s : (n : ℤ) → CoeffPair p → DeletedCoeff p n := fun n ψ => (g n (0,ψ)).1
  have hpoint (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val δ) :
      (s n ψ,ψ) = g n (0,ψ) := by
    apply Prod.ext
    · rfl
    · exact (congrArg Prod.snd (hgData n (0,ψ) (hmem n ψ hψ)).2.1).symm
  refine ⟨{
    sourceRadius := δ, rootRadius := ρ,
    sourceRadius_pos := hδ, rootRadius_pos := hρ,
    sourceRadius_le_rootRadius := hδρ, rootRadius_lt := hρR,
    branch := s, analytic := ?_, at_base := ?_, graph := ?_, equation_zero := ?_, unique := ?_
  }⟩
  · intro n ψ hψ
    have hmap : AnalyticAt ℂ (fun χ : CoeffPair p => ((0 : DeletedCoeff p n),χ)) ψ :=
      analyticAt_const.prod analyticAt_id
    exact analyticAt_fst.comp ((hgAna n (0,ψ) (hmem n ψ hψ)).comp hmap)
  · intro n
    change (g n (0,φ.val)).1 = _
    rw [← hHbase n,hgBase n]
  · intro n ψ hψ
    rw [hpoint n ψ hψ]
    exact (hgData n (0,ψ) (hmem n ψ hψ)).1
  · intro n ψ hψ
    have h := congrArg Prod.fst (hgData n (0,ψ) (hmem n ψ hψ)).2.1
    change D.equation n (g n (0,ψ)) = 0 at h
    rw [← hpoint n ψ hψ] at h
    exact h
  · intro n ψ hψ b hb hzero
    have hq : (b,ψ) ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) ρ := by
      rw [mem_ball,Prod.dist_eq]
      exact max_lt_iff.mpr ⟨mem_ball.mp hb,(mem_ball.mp hψ).trans_le hδρ⟩
    have hH : H n (b,ψ) = (0,ψ) := by simp only [H,hzero]
    exact congrArg Prod.fst ((hgData n (0,ψ) (hmem n ψ hψ)).2.2 (b,ψ) hq hH)

theorem SourcePsiUniformComplexBranchFamily.contour_equations
    {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : realTypeSourceLocus p}
    {D : SourcePsiUniformEquationTube hp hp1 φ} (S : SourcePsiUniformComplexBranchFamily D)
    (n : ℤ) (ψ : CoeffPair p) (hψ : ψ ∈ ball φ.val S.sourceRadius) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ m, sourcePsiEquationCoordinate hp hp1 n m (S.branch n ψ : Coeff p) ψ (c m) (R m) = 0 := by
  have houter : (S.branch n ψ,ψ) ∈ ball (sourcePsiGapRoot hp hp1 n φ,φ.val) (4*D.radius) :=
    (ball_subset_ball (by linarith [S.rootRadius_lt,D.radius_pos])) (S.graph n ψ hψ)
  obtain ⟨c,R,hfamily,hcoord⟩ := D.contours n (S.branch n ψ,ψ) houter
  refine ⟨c,R,hfamily,?_⟩
  intro m
  have h := hcoord m
  rw [S.equation_zero n ψ hψ] at h
  simpa using h.symm

end NLS.ZakharovShabat
