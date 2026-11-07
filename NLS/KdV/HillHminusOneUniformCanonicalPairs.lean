import NLS.KdV.HillHminusOneCanonicalRealLabels

/-! # Uniform SAME-index original real high pairs

One complex source neighborhood and one cutoff precede ALL real inputs
and ALL high indices. The complete ordered labeling, with exact central
counts and repetitions, is identified with the intrinsic original labels
before its high pairs are used in any action comparison.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.KdV

theorem exists_hillHminus_uniform_canonical_label_pairs (q : PeriodOneHminusOne) :
    ∃ r : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ ha : IsRealPeriodOneHminusOne a, ∀ n : ℕ+, N ≤ (n : ℕ) →
        HillHminusHighGapPair a n r
          (hillHminusLabels a ha (2*(n : ℕ)-1) : ℂ) (hillHminusLabels a ha (2*(n : ℕ)) : ℂ) := by
  obtain ⟨r,N,V,hr,hrpi,hN,hV,hqV,hlabels⟩ := exists_hillHminus_global_real_characteristic_labels q
  refine ⟨r,N,V,hr,hrpi,hN,hV,hqV,?_⟩
  intro a ha har n hn
  obtain ⟨lambda,hm,hroots,hpairs,hcounts,hmem⟩ := hlabels a ha har
  have hraw : HillHminusRealCharacteristicLabeling a N r lambda := by
    refine ⟨hN,hr,hrpi,hm,hroots,?_,hcounts,hmem⟩
    intro k hk
    have he : (N : ℕ)+(k-(N : ℕ)) = k := Nat.add_sub_of_le hk
    have hp := hpairs (k-(N : ℕ))
    have hpn : (⟨(N : ℕ)+(k-(N : ℕ)),by omega⟩ : ℕ+) = ⟨k,by omega⟩ := by
      apply PNat.coe_injective
      exact he
    rw [hpn] at hp
    simpa only [he] using hp
  have hcan := hillHminusLabels_spec_at a har N r lambda hraw
  obtain ⟨p,hl,hu⟩ := hcan.high_pair (n : ℕ) hn
  have hp : HillHminusHighGapPair a n r (p.left : ℂ) (p.right : ℂ) := p.pair
  rw [hl,hu]
  exact hp

end NLS.KdV
