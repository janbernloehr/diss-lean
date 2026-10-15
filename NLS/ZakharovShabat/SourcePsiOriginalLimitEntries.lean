import NLS.ZakharovShabat.SourcePsiOriginalLimitCanonical
import NLS.ZakharovShabat.SourcePsiOriginalEquationSup

/-!
# Original contour identities for Q*

Each intrinsic limit entry is twice an original psi period, with the
input index as the omitted numerator root. Off the diagonal, multiplying
by the index difference gives the original equation coordinate divided
by pi. The actual supremum of those equations yields one lp row majorant.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal limit integral is twice the psi contour on every original circle. -/
theorem SourceIsolatingNeighborhoods.originalLimitMatrixEntry_eq_two_mul_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφV : φ ∈ V)
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    sourcePsiLimitMatrixEntry hp hp1 m k a φ (d:ℂ) r =
      2*sourcePsiContour hp hp1 k a φ (d:ℂ) r := by
  let P := hD.periodCircle φ hφV m d r hr he
  have hInt : EqOn (sourcePsiLimitMatrixIntegrand hp hp1 m k a φ)
      (fun z => sourcePsiContourIntegrandJoint hp hp1 k (z,(a,φ))) (sphere (d:ℂ) r) := by
    intro z hz
    rw [sourcePsiLimitMatrixIntegrand_eq_fullProductVariation_single hp hp1 m k a φ z
      (P.sphere_subset_rootDomain hz) (hD.originalRootPlacement_avoids_sphere a ha m k d r hr he z hz),
      sourcePsiFullProductVariation_single hp hp1]
    simp [sourcePsiContourIntegrandJoint,div_eq_mul_inv]
  unfold sourcePsiLimitMatrixEntry
  rw [circleIntegral.integral_congr hr.le hInt]
  simp [sourcePsiContour,div_eq_mul_inv]
  ring

/-- Every original circle gives the intrinsic Q* entry with the exact factor two. -/
theorem SourceLemma12_4Data.originalLimitOperator_entry_contour
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (m k : ℤ) (d r : ℝ) (hr : 0 < r) (he : D m = ball (d:ℂ) r) :
    (sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m =
      2*sourcePsiContour hp hp1 k a φ (d:ℂ) r := by
  rw [H.originalLimitOperator_entry hD φ hφW hφV hφ a ha m k d r hr he]
  exact hD.originalLimitMatrixEntry_eq_two_mul_contour φ hφV a ha m k d r hr he

/-- The weighted off-diagonal entry is an actual original equation coordinate. -/
theorem SourceLemma12_4Data.originalLimitOperator_weighted_entry
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) (m k : ℤ) :
    ((k-m:ℤ):ℂ)*(sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m =
      (Real.pi:ℂ)⁻¹*(sourcePsiOriginalEquation hp hp1 k (Coeff.deleteCoordinateTo k a) φ:Coeff p) m := by
  obtain ⟨d,r,hr,he⟩ := hD.discs m
  let P := hD.periodCircle φ hφV m d r hr he
  rw [H.originalLimitOperator_entry_contour hD φ hφW hφV hφ a ha m k d r hr he,
    H.originalEquation_fullInput φ hφW k m a P]
  unfold sourcePsiEquationCoordinate
  dsimp only [P,SourceIsolatingNeighborhoods.periodCircle]
  field_simp

/-- An actual equation majorant bounds the weighted limit entries. -/
theorem SourceLemma12_4Data.originalLimitOperator_offDiagonal_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) (E : Coeff p)
    (hE : ∀ n m : ℤ, ‖(sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n a) φ:Coeff p) m‖ ≤ ‖E m‖) :
    ∀ m k : ℤ, m ≠ k →
      ‖(sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m‖ ≤
        ‖(((Real.pi:ℂ)⁻¹ • E):Coeff p) m‖/‖((m-k:ℤ):ℂ)‖ := by
  intro m k hmk
  have he := H.originalLimitOperator_weighted_entry hD φ hφW hφV hφ a ha m k
  have hn : ‖((k-m:ℤ):ℂ)‖ = ‖((m-k:ℤ):ℂ)‖ := by
    simp only [Int.cast_sub]
    exact norm_sub_rev _ _
  have hd : 0 < ‖((m-k:ℤ):ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast sub_ne_zero.mpr hmk)
  apply (le_div_iff₀ hd).mpr
  have he' := congrArg norm he
  rw [norm_mul,norm_mul,hn] at he'
  calc
    _ = ‖(Real.pi:ℂ)⁻¹‖*‖(sourcePsiOriginalEquation hp hp1 k (Coeff.deleteCoordinateTo k a) φ:Coeff p) m‖ := by
      rw [mul_comm,he']
    _ ≤ ‖(Real.pi:ℂ)⁻¹‖*‖E m‖ := mul_le_mul_of_nonneg_left (hE k m) (norm_nonneg _)
    _ = _ := by simp only [lp.coeFn_smul,Pi.smul_apply,norm_smul]


/-- The off-diagonal part of (2.29), with one actual lp row majorant. -/
theorem SourceLemma12_4Data.originalLimitOperator_offDiagonal_majorant
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D) :
    ∃ B : Coeff p, ∀ m k : ℤ, m ≠ k →
      ‖(sourcePsiOriginalLimitOperator hp hp1 a φ (lp.single p k 1)) m‖ ≤
        ‖B m‖/‖((m-k:ℤ):ℂ)‖ := by
  obtain ⟨U,_,hbase,_,C,_,hb⟩ := H.previous.quotients.originalEquation_commonMajorant hW φ hφW a
  obtain ⟨E,_,hE⟩ := hb (a,φ) hbase
  exact ⟨(Real.pi:ℂ)⁻¹ • E,H.originalLimitOperator_offDiagonal_bound hD φ hφW hφV hφ a ha E hE⟩

/-- One neighborhood and one lp norm bound control the off-diagonal majorants. -/
theorem SourceLemma12_4Data.originalLimitOperator_offDiagonal_locally_bounded
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ U, IsRealType (CoeffPair.toMax p t.2) →
        t.1 ∈ sourcePsiOriginalRootPlacement D →
        ∃ B : Coeff p, ‖B‖ ≤ C ∧ ∀ m k : ℤ, m ≠ k →
          ‖(sourcePsiOriginalLimitOperator hp hp1 t.1 t.2 (lp.single p k 1)) m‖ ≤
            ‖B m‖/‖((m-k:ℤ):ℂ)‖ := by
  obtain ⟨U₀,ho,hbase,hUW,C,hC,hb⟩ := H.previous.quotients.originalEquation_commonMajorant hW φ hφW a₀
  let U := U₀ ∩ (univ ×ˢ V)
  refine ⟨U,ho.inter (isOpen_univ.prod hV),⟨hbase,mem_univ _,hφV⟩,
    (fun t ht => ⟨mem_univ _,(hUW ht.1).2,ht.2.2⟩),‖(Real.pi:ℂ)⁻¹‖*C,
    mul_nonneg (norm_nonneg _) hC,?_⟩
  intro t ht hreal ha
  obtain ⟨E,hE,hpoint⟩ := hb t ht.1
  refine ⟨(Real.pi:ℂ)⁻¹ • E,?_,
    H.originalLimitOperator_offDiagonal_bound hD t.2 (hUW ht.1).2 ht.2.2 hreal t.1 ha E hpoint⟩
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left hE (norm_nonneg _)

end NLS.ZakharovShabat
