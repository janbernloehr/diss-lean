import NLS.SequenceSpaces.FourierRealZeroMultiplier
import Mathlib.Topology.Sequences

/-! A strongly compact set containing all independent signed mode flips
must have vanishing weighted coordinates. This retains the actual infinity
norm and the physical conjugacy of the two signed coordinates. -/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.WeightedCoeff

private def pairedFlipSymbol (n : ℕ) (k : ℤ) : ℂ := if k.natAbs=n then -1 else 1
private theorem pairedFlipSymbol_bound (w : Weight) (n : ℕ) (k : ℤ) :
    w k*‖pairedFlipSymbol n k‖≤1*w k := by
  unfold pairedFlipSymbol
  split_ifs <;> norm_num
private theorem pairedFlipSymbol_conj (n : ℕ) (k : ℤ) :
    pairedFlipSymbol n (-k)=(starRingEnd ℂ) (pairedFlipSymbol n k) := by
  simp only [pairedFlipSymbol,Int.natAbs_neg]
  split_ifs <;> simp

def pairedSignFlip (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ)
    (a : fourierRealZeroSubmodule w ⊤) : fourierRealZeroSubmodule w ⊤ :=
  fourierRealZeroMultiplier w w hw (pairedFlipSymbol n) 1 zero_le_one
    (pairedFlipSymbol_bound w n) (pairedFlipSymbol_conj n) a

theorem pairedSignFlip_apply (w : Weight) (hw : ∀ k, w (-k)=w k) (n : ℕ)
    (a : fourierRealZeroSubmodule w ⊤) (k : ℤ) :
    (pairedSignFlip w hw n a).val.val.val k=
      if k.natAbs=n then -a.val.val.val k else a.val.val.val k := by
  rw [pairedSignFlip,fourierRealZeroMultiplier_apply]
  unfold pairedFlipSymbol
  split_ifs <;> simp

/-- The precise positive-index weighted c0 condition. -/
def PositiveWeightedC0 (w : Weight) (a : fourierRealZeroSubmodule w ⊤) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n : ℕ, N≤n → w n*‖a.val.val.val n‖<ε

theorem positiveWeightedC0_of_compact_pairedFlips (w : Weight) (hw : ∀ k, w (-k)=w k)
    (a : fourierRealZeroSubmodule w ⊤) (K : Set (fourierRealZeroSubmodule w ⊤))
    (hK : IsCompact K) (hflip : ∀ n : ℕ, 1≤n → pairedSignFlip w hw n a ∈ K) :
    PositiveWeightedC0 w a := by
  by_contra h
  unfold PositiveWeightedC0 at h
  push Not at h
  obtain ⟨ε,hε,hbad⟩ := h
  choose b hbIndex hbBad using fun j : ℕ => hbad (j+1)
  obtain ⟨y,_,φ,hφ,hlim⟩ := hK.tendsto_subseq (fun j => hflip (b j) (by have hh:=hbIndex j; omega))
  have hy : y=a := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    have heval : Continuous (fun z : fourierRealZeroSubmodule w ⊤ => z.val.val.val k) :=
      (evalCLM w ⊤ k).continuous.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hcoord := (heval.tendsto y).comp hlim
    have hevent : (fun j => (pairedSignFlip w hw (b (φ j)) a).val.val.val k)=ᶠ[atTop]
        (fun _ : ℕ => a.val.val.val k) := by
      filter_upwards [eventually_ge_atTop k.natAbs] with j hj
      have hneq : k.natAbs≠b (φ j) := by
        have hi := hbIndex (φ j)
        have hp : j≤φ j := hφ.id_le j
        omega
      rw [pairedSignFlip_apply,if_neg hneq]
    have hconst : Tendsto (fun j => (pairedSignFlip w hw (b (φ j)) a).val.val.val k) atTop
        (𝓝 (a.val.val.val k)) := (tendsto_congr' hevent).mpr tendsto_const_nhds
    exact tendsto_nhds_unique hcoord hconst
  rw [hy] at hlim
  obtain ⟨J,hJ⟩ := Metric.tendsto_atTop.mp hlim ε hε
  have hclose := hJ J le_rfl
  have hb := hbBad (φ J)
  let m := b (φ J)
  have hraw := norm_apply_le w ⊤ ((pairedSignFlip w hw m a).val.val-a.val.val) (m:ℤ)
  have hdist : 2*(w m*‖a.val.val.val m‖)≤dist (pairedSignFlip w hw m a) a := by
    have hv := (le_div_iff₀ (w.positive (m:ℤ))).mp hraw
    rw [sub_val,pairedSignFlip_apply,if_pos (Int.natAbs_natCast m)] at hv
    have he : -a.val.val.val (m:ℤ)-a.val.val.val (m:ℤ)=(-2:ℂ)*a.val.val.val (m:ℤ) := by ring
    rw [he,norm_mul] at hv
    norm_num only [norm_neg,Complex.norm_ofNat] at hv
    rw [dist_eq_norm]
    change 2*(w m*‖a.val.val.val m‖)≤‖(pairedSignFlip w hw m a).val.val-a.val.val‖
    nlinarith
  change dist (pairedSignFlip w hw m a) a<ε at hclose
  change ε≤w m*‖a.val.val.val m‖ at hb
  linarith

end NLS.WeightedCoeff
