import NLS.FunctionalAnalysis.CubeFixedPoint
import Mathlib.Topology.Metrizable.Basic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal ComplexConjugate

namespace NLS.FunctionalAnalysis



def countableIntervalBox (l u : ℕ → ℝ) : Set (ℕ → ℝ) :=
  {x | ∀ j, x j ∈ Icc (l j) (u j)}

theorem isCompact_countableIntervalBox (l u : ℕ → ℝ) : IsCompact (countableIntervalBox l u) :=
  isCompact_pi_infinite (s := fun j => Icc (l j) (u j)) (fun _ => isCompact_Icc)

def intervalBoxFiniteLift (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j) (N : ℕ)
    (a : @NLS.CubicalSperner.unit_cube N) : countableIntervalBox l u :=
  ⟨fun j => if h : j < N then l j+(u j-l j)*a.val ⟨j,h⟩ else l j,by
    intro j
    dsimp only []
    split_ifs with hj
    · have ha0 := a.property.1 ⟨j,hj⟩
      have ha1 := a.property.2 ⟨j,hj⟩
      change 0 ≤ a.val ⟨j,hj⟩ at ha0
      change a.val ⟨j,hj⟩ ≤ 1 at ha1
      have hw : 0 ≤ u j-l j := sub_nonneg.mpr (hle j)
      constructor
      · nlinarith [mul_nonneg hw ha0]
      · nlinarith [mul_nonneg hw (show 0 ≤ 1-a.val ⟨j,hj⟩ by linarith)]
    · exact ⟨le_rfl,hle j⟩⟩

theorem continuous_intervalBoxFiniteLift (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j) (N : ℕ) :
    Continuous (intervalBoxFiniteLift l u hle N) := by
  have hc : Continuous (fun a : @NLS.CubicalSperner.unit_cube N => fun j =>
      if h : j < N then l j+(u j-l j)*a.val ⟨j,h⟩ else l j) := by
    apply continuous_pi
    intro j
    by_cases hj : j < N
    · simp only [dif_pos hj]
      exact continuous_const.add (continuous_const.mul ((continuous_apply (⟨j,hj⟩ : Fin N)).comp continuous_subtype_val))
    · simp only [dif_neg hj]
      exact continuous_const
  exact hc.subtype_mk (fun a => (intervalBoxFiniteLift l u hle N a).property)

def intervalBoxFiniteProjection (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j) (N : ℕ)
    (x : countableIntervalBox l u) : @NLS.CubicalSperner.unit_cube N :=
  ⟨fun i => if l i = u i then 0 else (x.val i-l i)/(u i-l i),by
    constructor
    · intro i
      dsimp only []
      split_ifs
      · exact le_rfl
      · exact div_nonneg (sub_nonneg.mpr (x.property i).1) (sub_nonneg.mpr (hle i))
    · intro i
      dsimp only []
      split_ifs with he
      · exact zero_le_one
      · have hw : 0 < u i-l i := sub_pos.mpr (lt_of_le_of_ne (hle i) he)
        exact (div_le_one hw).mpr (sub_le_sub_right (x.property i).2 _)⟩

theorem continuous_intervalBoxFiniteProjection (l u : ℕ → ℝ) (hle : ∀ j, l j ≤ u j) (N : ℕ) :
    Continuous (intervalBoxFiniteProjection l u hle N) := by
  have hc : Continuous (fun x : countableIntervalBox l u => fun i : Fin N =>
      if l i = u i then 0 else (x.val i-l i)/(u i-l i)) := by
    apply continuous_pi
    intro i
    by_cases hi : l i = u i
    · simp only [if_pos hi]
      exact continuous_const
    · simp only [if_neg hi]
      exact (((continuous_apply (i:ℕ)).comp continuous_subtype_val).sub continuous_const).div_const _
  exact hc.subtype_mk (fun x => (intervalBoxFiniteProjection l u hle N x).property)

end NLS.FunctionalAnalysis
