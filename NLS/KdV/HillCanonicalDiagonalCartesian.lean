import NLS.KdV.HillOnIndexSourceBallCompatibility
import NLS.KdV.HillCanonicalPhysicalAbelianValue

/-! Intrinsic diagonal gap-times-phase Cartesian factors on the SAME
OPEN CONNECTED native complex source domain as the physical off-index
Abelian family. Gluing precedes ALL indices and includes complex gap
collapse. These are not yet the full Birkhoff coordinates. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillHminusDiagonalCartesianPlus (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusPhysicalAbelianDomain then (Classical.choose (mem_iUnion.mp hq)).diagonalPlus n q else 0

def hillHminusDiagonalCartesianMinus (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  if hq : q ∈ hillHminusPhysicalAbelianDomain then (Classical.choose (mem_iUnion.mp hq)).diagonalMinus n q else 0

namespace HillPhysicalAbelianSourceBall

theorem canonical_diagonalPlus_eq (B : HillPhysicalAbelianSourceBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : hillHminusDiagonalCartesianPlus n q = B.diagonalPlus n q := by
  have hdom : q ∈ hillHminusPhysicalAbelianDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusDiagonalCartesianPlus,dif_pos hdom]
  let C := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.diagonalPlus_eq_on_overlap B n ⟨hC,hq⟩

theorem canonical_diagonalMinus_eq (B : HillPhysicalAbelianSourceBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) : hillHminusDiagonalCartesianMinus n q = B.diagonalMinus n q := by
  have hdom : q ∈ hillHminusPhysicalAbelianDomain := mem_iUnion.mpr ⟨B,hq⟩
  rw [hillHminusDiagonalCartesianMinus,dif_pos hdom]
  let C := Classical.choose (mem_iUnion.mp hdom)
  have hC : q ∈ C.source := Classical.choose_spec (mem_iUnion.mp hdom)
  exact C.diagonalMinus_eq_on_overlap B n ⟨hC,hq⟩

end HillPhysicalAbelianSourceBall

theorem analyticOnNhd_hillHminusDiagonalCartesianPlus (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDiagonalCartesianPlus n) hillHminusPhysicalAbelianDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_diagonalPlus n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_diagonalPlus_eq n a ha).symm

theorem analyticOnNhd_hillHminusDiagonalCartesianMinus (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDiagonalCartesianMinus n) hillHminusPhysicalAbelianDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  apply (B.analytic_diagonalMinus n q hB).congr
  filter_upwards [B.source_open.mem_nhds hB] with a ha
  exact (B.canonical_diagonalMinus_eq n a ha).symm

theorem hillHminusDiagonalCartesian_product (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) :
    hillHminusDiagonalCartesianPlus n q*hillHminusDiagonalCartesianMinus n q = hillHminusCanonicalGapSquare n q := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  rw [B.canonical_diagonalPlus_eq n q hB,B.canonical_diagonalMinus_eq n q hB]
  exact B.patch.physicalOnIndexCartesian_product_eq_original_gap_square n q (B.subset hB)

theorem hillHminusDiagonalCartesian_eq_patch_of_real (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    hillHminusDiagonalCartesianPlus n q = P.physicalOnIndexCartesianPlus n q ∧
      hillHminusDiagonalCartesianMinus n q = P.physicalOnIndexCartesianMinus n q := by
  obtain ⟨B,hP,_,hB⟩ := exists_hillPhysicalAbelianSourceBall_of_patch P q hq hr
  rw [B.canonical_diagonalPlus_eq n q hB,B.canonical_diagonalMinus_eq n q hB]
  change B.patch.physicalOnIndexCartesianPlus n q = _ ∧ B.patch.physicalOnIndexCartesianMinus n q = _
  rw [hP]
  exact ⟨rfl,rfl⟩

theorem hillHminusDiagonalCartesian_zero_of_real_closed_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (hg : hillHminusCanonicalGapSquare n q = 0) :
    hillHminusDiagonalCartesianPlus n q = 0 ∧ hillHminusDiagonalCartesianMinus n q = 0 := by
  obtain ⟨P,hq,_⟩ := exists_hillProductEquationPatch q hr
  have he := hillHminusDiagonalCartesian_eq_patch_of_real P n q hq hr
  have hz := P.physicalOnIndexCartesian_zero_of_real_closed_gap n q hq hr hg
  exact ⟨he.1.trans hz.1,he.2.trans hz.2⟩

theorem exists_common_intrinsic_diagonal_Cartesian_patch_ball (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r : ℝ, 0 < r ∧ ball q r ⊆ P.physicalDirichletSource ∩ hillHminusPhysicalAbelianDomain ∧
      ∀ n : ℕ+, ∀ a ∈ ball q r,
        hillHminusDiagonalCartesianPlus n a = P.physicalOnIndexCartesianPlus n a ∧
          hillHminusDiagonalCartesianMinus n a = P.physicalOnIndexCartesianMinus n a := by
  obtain ⟨B,hP,hcenter,_⟩ := exists_hillPhysicalAbelianSourceBall_of_patch P q hq hr
  have hsource : B.source = ball q B.radius := by rw [HillPhysicalAbelianSourceBall.source,hcenter]
  refine ⟨B.radius,B.radius_pos,?_,?_⟩
  · intro a ha
    have haB : a ∈ B.source := hsource.symm ▸ ha
    exact ⟨hP ▸ B.subset haB,mem_iUnion.mpr ⟨B,haB⟩⟩
  · intro n a ha
    rw [B.canonical_diagonalPlus_eq n a (hsource.symm ▸ ha),B.canonical_diagonalMinus_eq n a (hsource.symm ▸ ha)]
    change B.patch.physicalOnIndexCartesianPlus n a = _ ∧ B.patch.physicalOnIndexCartesianMinus n a = _
    rw [hP]
    exact ⟨rfl,rfl⟩

def hillHminusDiagonalPhaseSquare (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusDiagonalCartesianPlus n q/hillHminusDiagonalCartesianMinus n q

theorem hillHminusDiagonalCartesian_ne_zero_of_gap (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusDiagonalCartesianPlus n q ≠ 0 ∧ hillHminusDiagonalCartesianMinus n q ≠ 0 :=
  mul_ne_zero_iff.mp ((hillHminusDiagonalCartesian_product n q hq).symm ▸ hg)

theorem analyticOnNhd_hillHminusDiagonalPhaseSquare (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusDiagonalPhaseSquare n)
      {q | q ∈ hillHminusPhysicalAbelianDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} := by
  intro q hq
  exact (analyticOnNhd_hillHminusDiagonalCartesianPlus n q hq.1).div
    (analyticOnNhd_hillHminusDiagonalCartesianMinus n q hq.1) (hillHminusDiagonalCartesian_ne_zero_of_gap n q hq.1 hq.2).2

theorem hillHminusPhysicalAbelianDomain_subset_gapDomain : hillHminusPhysicalAbelianDomain ⊆ hillHminusCanonicalGapDomain := by
  intro q hq
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  exact mem_iUnion.mpr ⟨B.patch.parent.parent.miuraBall,(B.patch.parent.subset (B.patch.subset (B.subset hB).1)).1⟩

theorem isOpen_hillHminusDiagonalPhaseDomain (n : ℕ+) :
    IsOpen {q | q ∈ hillHminusPhysicalAbelianDomain ∧ hillHminusCanonicalGapSquare n q ≠ 0} :=
  ((analyticOnNhd_hillHminusCanonicalGapSquare n).mono hillHminusPhysicalAbelianDomain_subset_gapDomain).continuousOn.isOpen_inter_preimage
    isOpen_hillHminusPhysicalAbelianDomain (isOpen_ne (x := (0:ℂ)))

theorem hillHminusDiagonalPhaseSquare_eq_local (B : HillPhysicalAbelianSourceBall) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ B.source) :
    hillHminusDiagonalPhaseSquare n q = B.patch.physicalOnIndexPhaseSquare n q := by
  rw [hillHminusDiagonalPhaseSquare,B.canonical_diagonalPlus_eq n q hq,B.canonical_diagonalMinus_eq n q hq]
  rfl

theorem hillHminusDiagonalPhaseSquare_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusPhysicalAbelianDomain) (hg : hillHminusCanonicalGapSquare n q ≠ 0) :
    hillHminusDiagonalPhaseSquare n q ≠ 0 := by
  have h := hillHminusDiagonalCartesian_ne_zero_of_gap n q hq hg
  exact div_ne_zero h.1 h.2

end NLS.KdV
