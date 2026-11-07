import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! Quantitative gap comparison for two real scalar branches close to the identity. -/
noncomputable section
open Set
open scoped NNReal
namespace NLS.RealAnalysis

/-- Construct both roots,including a collapsed pair,and compare their separation
with the nonnegative splitting coefficient at the actual diagonal root. -/
theorem exists_split_roots_gap_comparison (a b : ℝ → ℝ) (c R α : ℝ) (hR : 0 < R)
    (ha : ∀ x ∈ Icc (c-R) (c+R), ∀ y ∈ Icc (c-R) (c+R), |a x-a y| ≤ (1/8:ℝ)*|x-y|)
    (hb : ∀ x ∈ Icc (c-R) (c+R), ∀ y ∈ Icc (c-R) (c+R), |b x-b y| ≤ (1/8:ℝ)*|x-y|)
    (haB : ∀ x ∈ Icc (c-R) (c+R), |a x| ≤ R/4)
    (hbB : ∀ x ∈ Icc (c-R) (c+R), 0 ≤ b x ∧ b x ≤ R/4)
    (hα : α ∈ Icc (c-R) (c+R)) (heα : α-c-a α = 0) :
    ∃ l ∈ Icc (c-R) (c+R), ∃ r ∈ Icc (c-R) (c+R),
      l ≤ α ∧ α ≤ r ∧
      (∀ x ∈ Icc (c-R) (c+R), (x-c-a x+b x = 0 ↔ x = l) ∧ (x-c-a x-b x = 0 ↔ x = r)) ∧
      b α ≤ r-l ∧ r-l ≤ 3*b α := by
  let I := Icc (c-R) (c+R)
  let F : ℝ → ℝ := fun x => x-c-a x+b x
  let G : ℝ → ℝ := fun x => x-c-a x-b x
  have haL : LipschitzOnWith (1/8:ℝ≥0) a I := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using ha x hx y hy
  have hbL : LipschitzOnWith (1/8:ℝ≥0) b I := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hb x hx y hy
  have hFc : ContinuousOn F I := ((continuousOn_id.sub continuousOn_const).sub haL.continuousOn).add hbL.continuousOn
  have hGc : ContinuousOn G I := ((continuousOn_id.sub continuousOn_const).sub haL.continuousOn).sub hbL.continuousOn
  have hFm : StrictMonoOn F I := by
    intro x hx y hy hxy
    have hax := abs_le.mp (ha y hy x hx)
    have hbx := abs_le.mp (hb y hy x hx)
    rw [abs_of_pos (sub_pos.mpr hxy)] at hax hbx
    dsimp [F]
    linarith
  have hGm : StrictMonoOn G I := by
    intro x hx y hy hxy
    have hax := abs_le.mp (ha y hy x hx)
    have hbx := abs_le.mp (hb y hy x hx)
    rw [abs_of_pos (sub_pos.mpr hxy)] at hax hbx
    dsimp [G]
    linarith
  have hI : c-R ≤ c+R := by linarith
  have hL : c-R ∈ I := ⟨le_rfl,hI⟩
  have hU : c+R ∈ I := ⟨hI,le_rfl⟩
  have hFa : F (c-R) ≤ 0 := by
    have hh := abs_le.mp (haB _ hL)
    have hh' := hbB _ hL
    dsimp [F]
    linarith
  have hFb : 0 ≤ F (c+R) := by
    have hh := abs_le.mp (haB _ hU)
    have hh' := hbB _ hU
    dsimp [F]
    linarith
  have hGa : G (c-R) ≤ 0 := by
    have hh := abs_le.mp (haB _ hL)
    have hh' := hbB _ hL
    dsimp [G]
    linarith
  have hGb : 0 ≤ G (c+R) := by
    have hh := abs_le.mp (haB _ hU)
    have hh' := hbB _ hU
    dsimp [G]
    linarith
  obtain ⟨l, hl, hfl⟩ := intermediate_value_Icc hI hFc ⟨hFa,hFb⟩
  obtain ⟨r, hr, hgr⟩ := intermediate_value_Icc hI hGc ⟨hGa,hGb⟩
  have hlα : l ≤ α := by
    by_contra hh
    have hh' := hFm hα hl (lt_of_not_ge hh)
    have hba := (hbB α hα).1
    dsimp [F] at hfl hh'
    linarith
  have hαr : α ≤ r := by
    by_contra hh
    have hh' := hGm hr hα (lt_of_not_ge hh)
    have hba := (hbB α hα).1
    dsimp [G] at hgr hh'
    linarith
  refine ⟨l, hl, r, hr, hlα, hαr, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨fun hh => hFm.injOn hx hl (hh.trans hfl.symm), fun hh => hh ▸ hfl⟩,
      ⟨fun hh => hGm.injOn hx hr (hh.trans hgr.symm), fun hh => hh ▸ hgr⟩⟩
  · have hal := abs_le.mp (ha l hl α hα)
    have hbl := abs_le.mp (hb l hl α hα)
    have har := abs_le.mp (ha r hr α hα)
    have hbr := abs_le.mp (hb r hr α hα)
    rw [abs_of_nonpos (sub_nonpos.mpr hlα)] at hal hbl
    rw [abs_of_nonneg (sub_nonneg.mpr hαr)] at har hbr
    dsimp [F] at hfl
    dsimp [G] at hgr
    linarith
  · have hal := abs_le.mp (ha l hl α hα)
    have hbl := abs_le.mp (hb l hl α hα)
    have har := abs_le.mp (ha r hr α hα)
    have hbr := abs_le.mp (hb r hr α hα)
    rw [abs_of_nonpos (sub_nonpos.mpr hlα)] at hal hbl
    rw [abs_of_nonneg (sub_nonneg.mpr hαr)] at har hbr
    have hba := (hbB α hα).1
    dsimp [F] at hfl
    dsimp [G] at hgr
    linarith

end NLS.RealAnalysis
