import NLS.ZakharovShabat.SourcePsiGlobalDistantDeletedRegularFactor
import NLS.ZakharovShabat.SourcePsiComplexContourAnalytic

/-!
# Uniform bounds for finitely many psi equation coordinates

Scalar holomorphy gives local continuity of each fixed equation
coordinate. A finite intersection makes its value bound uniform over
any finite set of deleted/selected index pairs.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Any finite family of fixed-circle psi equation coordinates has
one common local bound near a real-type source and any root input.
The circles may be the nonstandard head circles of a global contour
family. -/
theorem exists_local_sourcePsi_uniformFinitePairCoordinateBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (sN sM : Finset ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hR : ∀ m : ℤ, 0 ≤ R m)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ)
    (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
      (a₀,φ) ∈ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ U, ∀ n ∈ sN, ∀ m ∈ sM,
          ‖sourcePsiEquationCoordinate hp hp1 n m
            t.1 t.2 (c m) (R m)‖ ≤ M := by
  obtain ⟨W,_,_,hrealW,hdata⟩ :=
    exists_global_sourcePsiContourIntegrand_jointAnalytic hp hp1
  have hφW : φ ∈ W := hrealW hφ
  have hlocal (q : ℤ × ℤ) :
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧
        (a₀,φ) ∈ U ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ t ∈ U,
            ‖sourcePsiEquationCoordinate hp hp1 q.1 q.2
              t.1 t.2 (c q.2) (R q.2)‖ ≤ M := by
    let F : Coeff p × CoeffPair p → ℂ := fun t =>
      sourcePsiEquationCoordinate hp hp1 q.1 q.2
        t.1 t.2 (c q.2) (R q.2)
    have hdiff : DifferentiableAt ℂ F (a₀,φ) :=
      differentiableAt_sourcePsiEquationCoordinate_of_contour_domain
        hp hp1 q.1 q.2 a₀ φ (c q.2) (R q.2)
          (hR q.2) W hφW (hdata q.1).1 (hdata q.1).2
          (hcircle q.2)
    obtain ⟨δ,hδ,hnear⟩ :=
      Metric.continuousAt_iff.mp hdiff.continuousAt 1 (by norm_num)
    let U : Set (Coeff p × CoeffPair p) := ball (a₀,φ) δ
    let M : ℝ := ‖F (a₀,φ)‖+1
    have hM : 0 ≤ M := by dsimp [M]; positivity
    refine ⟨U,isOpen_ball,mem_ball_self hδ,M,hM,?_⟩
    intro t ht
    have hdist : ‖F t-F (a₀,φ)‖ < 1 := by
      simpa only [dist_eq_norm] using hnear (mem_ball.mp ht)
    have htri : ‖F t‖ ≤ ‖F (a₀,φ)‖+‖F t-F (a₀,φ)‖ := by
      have heq : F t = F (a₀,φ)+(F t-F (a₀,φ)) := by abel
      calc
        ‖F t‖ = ‖F (a₀,φ)+(F t-F (a₀,φ))‖ := congrArg norm heq
        _ ≤ _ := norm_add_le _ _
    dsimp [M]
    linarith
  choose U hUopen hbase M hM hbound using hlocal
  let s : Finset (ℤ × ℤ) := sN.product sM
  let V : Set (Coeff p × CoeffPair p) := ⋂ q ∈ s, U q
  let C : ℝ := ∑ q ∈ s, M q
  have hVopen : IsOpen V := isOpen_biInter_finset (fun q _ => hUopen q)
  have hbaseV : (a₀,φ) ∈ V := by
    simp only [V,Set.mem_iInter]
    intro q _
    exact hbase q
  have hC : 0 ≤ C := Finset.sum_nonneg (fun q _ => hM q)
  refine ⟨V,hVopen,hbaseV,C,hC,?_⟩
  intro t ht n hn m hm
  have hq : (n,m) ∈ s := Finset.mem_product.mpr ⟨hn,hm⟩
  simp only [V,Set.mem_iInter] at ht
  have htm : t ∈ U (n,m) := ht (n,m) hq
  have hMC : M (n,m) ≤ C :=
    Finset.single_le_sum (f := M) (fun q hq => hM q) hq
  exact (hbound (n,m) t htm).trans hMC

end NLS.ZakharovShabat
