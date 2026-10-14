import NLS.ZakharovShabat.SourcePsiOriginalSequenceBound
import NLS.ZakharovShabat.SourceGapFunctional
import NLS.ZakharovShabat.SourcePsiContourConjugation

/-!
# The contour-independent original psi equation

The equation is characterized by its literal coordinates on every original
circle. Existence of this lp sequence is proved on the whole original W,
for every deleted lp input. The total definition uses zero only when this
characterization has no witness; that branch is excluded everywhere on W.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePsiOriginalEquation (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) : DeletedCoeff p n := by
  classical
  exact if h : ∃ F : DeletedCoeff p n, ∀ m : ℤ,
      ∀ D : SourceCriticalRootPeriodCircle hp hp1 ψ m,
        (F:Coeff p) m = sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (D.center:ℂ) D.radius
    then Classical.choose h else 0

theorem SourceCorollary10_6Data.originalEquation_exists
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (a : DeletedCoeff p n) :
    ∃ F : DeletedCoeff p n, ∀ m : ℤ, ∀ D : SourceCriticalRootPeriodCircle hp hp1 ψ m,
      (F:Coeff p) m = sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (D.center:ℂ) D.radius := by
  obtain ⟨V,hV,_,hψV,_,D,c,hD⟩ := H.neighborhoods ψ hψ
  obtain ⟨d,r,hdr,U,_,hbase,_,C,_,hb⟩ :=
    H.original_equation_uniformNorm hW hD.toSourceIsolatingNeighborhoods hV ψ hψ hψV (a:Coeff p)
  obtain ⟨F,hF,_⟩ := hb n a ψ hbase
  refine ⟨F,?_⟩
  intro m E
  let P := hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψV m (d m) (r m) (hdr m).1 (hdr m).2
  exact (hF m).trans (P.psiEquation_eq E n (a:Coeff p))

/-- Every original circle computes the actual sequence coordinate on W. -/
theorem SourceCorollary10_6Data.originalEquation_apply
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (a : DeletedCoeff p n)
    (m : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m (a:Coeff p) ψ (D.center:ℂ) D.radius := by
  have h := H.originalEquation_exists hW ψ hψ n a
  simpa only [sourcePsiOriginalEquation,dif_pos h] using Classical.choose_spec h m D

/-- One neighborhood and one bound work before any deleted index is chosen. -/
theorem SourceCorollary10_6Data.originalEquation_uniformNorm
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
        ((a:Coeff p),ψ) ∈ U → ‖sourcePsiOriginalEquation hp hp1 n a ψ‖ ≤ C := by
  obtain ⟨V,hV,_,hφV,_,D,c,hD⟩ := H.neighborhoods φ hφ
  obtain ⟨d,r,hdr,U,hU,hbase,hUV,C,hC,hb⟩ :=
    H.original_equation_uniformNorm hW hD.toSourceIsolatingNeighborhoods hV φ hφ hφV a₀
  refine ⟨U,hU,hbase,(fun _ ht => ⟨mem_univ _,(hUV ht).2.1⟩),C,hC,?_⟩
  intro n a ψ ht
  obtain ⟨F,hF,hFn⟩ := hb n a ψ ht
  have he : sourcePsiOriginalEquation hp hp1 n a ψ = F := by
    apply Subtype.ext
    ext m
    let P := hD.toSourceIsolatingNeighborhoods.periodCircle ψ (hUV ht).2.2 m (d m) (r m) (hdr m).1 (hdr m).2
    exact (H.originalEquation_apply hW ψ (hUV ht).2.1 n a m P).trans (hF m).symm
  rwa [he]

/-- The printed power sum is strictly bounded by a positive constant,
locally in the original parameters and uniformly in the deleted index. -/
theorem SourceCorollary10_6Data.originalEquation_uniformPowerSum
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (φ : CoeffPair p) (hφ : φ ∈ W) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ W ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, ∀ a : DeletedCoeff p n, ∀ ψ : CoeffPair p,
        ((a:Coeff p),ψ) ∈ U →
          (∑' m : ℤ, ‖(sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m‖^p.toReal) < C := by
  obtain ⟨U,hU,hbase,hUW,C,hC,hb⟩ := H.originalEquation_uniformNorm hW φ hφ a₀
  refine ⟨U,hU,hbase,hUW,C^p.toReal+1,by positivity,?_⟩
  intro n a ψ ht
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  rw [← lp.norm_rpow_eq_tsum hp0]
  exact (Real.rpow_le_rpow (norm_nonneg _) (hb n a ψ ht) hp0.le).trans_lt (lt_add_one _)

theorem SourceCorollary10_6Data.originalEquation_circuit
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (a : DeletedCoeff p n)
    (m : ℤ) (D : SourceCriticalRootPeriodCircle hp hp1 ψ m)
    (Γ : PiecewiseC1Loop)
    (hΓ : Γ.Inside (ball (D.center:ℂ) D.radius \ sourcePeriodicSegment hp hp1 ψ m)) :
    sourceGapFunctional hp hp1 n m ψ Γ (fun z => sourcePsiCandidate n (z,(a:Coeff p))) =
      (sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m*
        Γ.windingIntegral (sourceStandardRootMidpoint hp hp1 ψ m) := by
  rw [H.originalEquation_apply hW ψ hψ n a m D]
  exact D.psiEquation_circuit n (a:Coeff p) Γ hΓ

theorem SourceCorollary10_6Data.originalEquation_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (a : DeletedCoeff p n) (ha : ∀ k : ℤ, ((a:Coeff p) k).im = 0) :
    ∀ m : ℤ, ((sourcePsiOriginalEquation hp hp1 n a ψ:Coeff p) m).im = 0 := by
  obtain ⟨V,_,_,hψV,_,D,c,hD⟩ := H.neighborhoods ψ hψ
  intro m
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.toSourceIsolatingNeighborhoods.periodCircle ψ hψV m d r hr he
  rw [H.originalEquation_apply hW ψ hψ n a m P]
  exact sourcePsiEquationCoordinate_im_eq_zero_of_realCenteredCircle hp hp1 ψ hreal n m (a:Coeff p)
    (fun k => by simp [displacedRoots,ha k]) d r hr P.sphere_subset_rootDomain

end NLS.ZakharovShabat
