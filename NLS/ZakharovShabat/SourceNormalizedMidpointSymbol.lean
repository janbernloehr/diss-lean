import NLS.ZakharovShabat.SourceDirichletTerminalSequence
import NLS.SequenceSpaces.EvenUnitExtension

/-! The actual midpoint divided by its positive free frequency is an
analytic bounded symbol with unit tails. The signed extension is even,
retains every positive label, and has central value one. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourcePositiveNormalizedMidpoint (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℕ+) (ψ : CoeffPair p) : ℂ :=
  canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) ((n:ℕ):ℤ)/
    ((Real.pi : ℂ)*(n:ℕ))

def sourceNormalizedMidpointSymbol (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (Coeff.evenUnitExtension (fun n => sourcePositiveNormalizedMidpoint hp hp1 n ψ))

/-- Normalizing by a positive free frequency contracts the displacement error. -/
theorem norm_sourcePositiveNormalizedMidpoint_sub_one_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℕ+) (ψ : CoeffPair p) :
    ‖sourcePositiveNormalizedMidpoint hp hp1 n ψ-1‖ ≤
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ ((n:ℕ):ℤ)‖ := by
  have hn : (1 : ℝ) ≤ (n:ℕ) := by exact_mod_cast (Nat.succ_le_of_lt n.pos)
  have hd : 1 ≤ ‖(Real.pi : ℂ)*(n:ℕ)‖ := by
    simp only [norm_mul,norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_natCast]
    nlinarith [Real.pi_gt_three]
  have hne : (Real.pi : ℂ)*(n:ℕ) ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : sourcePositiveNormalizedMidpoint hp hp1 n ψ-1 =
      sourcePeriodicMidpointDisplacement hp hp1 ψ ((n:ℕ):ℤ)/((Real.pi : ℂ)*(n:ℕ)) := by
    simp only [sourcePositiveNormalizedMidpoint,sourcePeriodicMidpointDisplacement_apply,Int.cast_natCast]
    field_simp
  rw [he,norm_div]
  exact div_le_self (norm_nonneg _) hd

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The exact even midpoint symbol is analytic in the bounded-sequence norm. -/
theorem normalized_midpoint_symbol_data (H : SourceLemma12_12Data hp hp1 W₀ W s) :
    (∀ ψ ∈ W, ∀ k, sourceNormalizedMidpointSymbol hp hp1 ψ k =
      Coeff.evenUnitExtension (fun n => sourcePositiveNormalizedMidpoint hp hp1 n ψ) k) ∧
    AnalyticOnNhd ℂ (sourceNormalizedMidpointSymbol hp hp1) W := by
  let D := H.original_theta_common_domain
  apply Coeff.analytic_evenUnit_realization_of_local_bounds _ D.source_open
    (fun n ψ hψ => ((D.symmetric_analytic ψ (D.source_subset hψ) ((n:ℕ):ℤ)).1).div_const)
  intro φ hφ
  have hc := (H.periodic_midpoint_displacement_analytic φ hφ).continuousAt
  have hb : ∀ᶠ ψ in 𝓝 φ,
      ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ < ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+1 :=
    hc.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨V,hVsub,hV,hφV⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (D.source_open.mem_nhds hφ) hb)
  refine ⟨V,hV,hφV,fun ψ hψ => (hVsub hψ).1,
    ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+2,by linarith [norm_nonneg (sourcePeriodicMidpointDisplacement hp hp1 φ)],?_⟩
  intro ψ hψ n
  change ‖sourcePositiveNormalizedMidpoint hp hp1 n ψ‖ ≤ ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+2
  have hdis := (norm_sourcePositiveNormalizedMidpoint_sub_one_le hp hp1 n ψ).trans
    (lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ ((n:ℕ):ℤ))
  have ht := norm_add_le (sourcePositiveNormalizedMidpoint hp hp1 n ψ-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at ht
  have hnorm : ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ <
      ‖sourcePeriodicMidpointDisplacement hp hp1 φ‖+1 := (hVsub hψ).2
  linarith

/-- Every fixed actual symbol tends to one on both signed tails. -/
theorem normalized_midpoint_symbol_unit_tail (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    ∀ ε > (0 : ℝ), ∃ K : ℕ, ∀ k : ℤ, K ≤ k.natAbs →
      ‖sourceNormalizedMidpointSymbol hp hp1 ψ k-1‖ ≤ ε := by
  intro ε hε
  obtain ⟨K,V,_,hψV,hsmall⟩ := Coeff.exists_local_uniform_small_coordinates hp
    (sourcePeriodicMidpointDisplacement hp hp1) ψ
    (H.periodic_midpoint_displacement_analytic ψ hψ).continuousAt ε hε
  refine ⟨K+1,fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by intro h; subst k; simp only [Int.natAbs_zero] at hk; omega
  let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr hk0⟩
  rw [H.normalized_midpoint_symbol_data.1 ψ hψ k]
  change ‖Coeff.evenUnitExtension (fun n => sourcePositiveNormalizedMidpoint hp hp1 n ψ) k-1‖ ≤ ε
  rw [Coeff.evenUnitExtension,dif_neg hk0]
  exact (norm_sourcePositiveNormalizedMidpoint_sub_one_le hp hp1 n ψ).trans
    (hsmall ψ hψV ((n:ℕ):ℤ) (by simp only [Int.natAbs_natCast]; exact Nat.lt_of_succ_le hk)).le

end SourceLemma12_12Data
end NLS.ZakharovShabat
