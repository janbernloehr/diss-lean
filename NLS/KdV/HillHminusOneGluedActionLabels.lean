import NLS.KdV.HillHminusOneUniformGluedActions
import NLS.KdV.HillHminusOneCanonicalRealLabels

/-! # The glued high gap square uses the actual canonical label slots -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem exists_hillHminusGluedHighGapSquare_eq_labels
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      q ∈ hillHminusHighActionDomain n ∧
      hillHminusGluedHighGapSquare n q =
        ((hillHminusLabels q hq (2*(n : ℕ)) : ℂ)-(hillHminusLabels q hq (2*(n : ℕ)-1) : ℂ))^2 := by
  obtain ⟨M,s,hlabels⟩ := hillHminusLabels_spec q hq
  obtain ⟨r,_,_,hfamily⟩ := exists_hillHminus_uniform_action_neighborhoods q
  obtain ⟨L,V,_,_,hqV,hfamily⟩ := hfamily 1 (by norm_num)
  refine ⟨max M L,hlabels.cutoff_ge_two.trans (le_max_left _ _),?_⟩
  intro n hn
  have hnM : M ≤ (n : ℕ) := (le_max_left _ _).trans hn
  have hnL : L ≤ (n : ℕ) := (le_max_right _ _).trans hn
  obtain ⟨K,hK,_⟩ := hfamily n hnL
  obtain ⟨p,hl,hu⟩ := hlabels.high_pair (n : ℕ) hnM
  have hp : HillHminusHighGapPair q n s (p.left : ℂ) (p.right : ℂ) := p.pair
  obtain ⟨l,u,hpair⟩ := (hK.valid hqV).2.2.2.2.2.2
  have hp' := hp.align_other_radius hpair
  refine ⟨hK.mem_highActionDomain hqV,?_⟩
  rw [hl,hu]
  exact hK.glued_gap_square_eq_pair hqV (p.left : ℂ) (p.right : ℂ) hp'

end NLS.KdV
