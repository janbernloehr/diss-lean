import NLS.SequenceSpaces.WeightedSingle
import Mathlib.Topology.Order.MonotoneConvergence

/-! A uniformly bounded stronger diagonal error on one ORIGINAL open
neighborhood forces two growing real sign symbols to agree eventually. -/
noncomputable section
open Set Metric Filter Topology Complex
namespace NLS

theorem eventually_eq_signs_of_bounded_diagonal_error
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (l : Filter ι) (a : ι → ℝ) (ha : ∀ i,0≤a i) (hat : Tendsto a l atTop)
    (e d : ι → Bool) (L : ι → E →L[ℂ] ℂ) (v : ι → E)
    (hv : ∀ i,‖v i‖≤1) (hLv : ∀ i,L i (v i)=1)
    (U : Set E) (hU : IsOpen U) (q : E) (hq : q∈U)
    (f : ι → E → ℂ) (B : ℝ) (hb : ∀ i,∀ p∈U,‖f i p‖≤B)
    (hf : ∀ i,∀ p∈U,f i p=
      (if e i then -(a i:ℂ)*L i p else (a i:ℂ)*L i p)-
      (if d i then -(a i:ℂ)*L i p else (a i:ℂ)*L i p)) :
    ∀ᶠ i in l,e i=d i := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq)
  let δ := r/2
  have hδ : 0<δ := by dsimp only [δ];positivity
  have hδn : ‖(δ:ℂ)‖=δ := by rw [Complex.norm_real,Real.norm_of_nonneg hδ.le]
  filter_upwards [hat.eventually_gt_atTop (B/δ)] with i hi
  by_contra hne
  let t := q+(δ:ℂ) • v i
  have ht : t∈U := by
    apply hball
    rw [mem_ball,dist_eq_norm]
    have he : t-q=(δ:ℂ) • v i := by dsimp only [t];abel
    rw [he,norm_smul,hδn]
    exact (mul_le_mul_of_nonneg_left (hv i) hδ.le).trans_lt (by dsimp only [δ];linarith)
  have he : f i t-f i q=if e i then (-2:ℂ)*(a i:ℂ)*(δ:ℂ) else (2:ℂ)*(a i:ℂ)*(δ:ℂ) := by
    rw [hf i t ht,hf i q hq]
    have hLt : L i t=L i q+(δ:ℂ) := by simp only [t,map_add,map_smul,hLv,smul_eq_mul,mul_one]
    rw [hLt]
    cases he : e i <;> cases hd : d i <;> simp only [he,hd,Bool.false_eq_true,↓reduceIte] at hne ⊢ <;> first | contradiction | ring
  have hn : ‖f i t-f i q‖=2*a i*δ := by
    rw [he]
    cases e i <;> simp only [Bool.false_eq_true,↓reduceIte,norm_mul,norm_neg,Complex.norm_ofNat,
      Complex.norm_real,Real.norm_of_nonneg (ha i),Real.norm_of_nonneg hδ.le]
  have hb' := (norm_sub_le (f i t) (f i q)).trans (add_le_add (hb i t ht) (hb i q hq))
  rw [hn] at hb'
  have hi' : B<a i*δ := (div_lt_iff₀ hδ).mp hi
  nlinarith

end NLS
