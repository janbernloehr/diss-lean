import NLS.KdV.HillCanonicalEnergyMidpoints
import NLS.KdV.HillHminusOneCanonicalGapSquares
import NLS.KdV.HillHminusOneActionRatio

/-! ONE native complex neighborhood and cutoff identify the intrinsic
canonical energy midpoint and squared gap with EVERY actual high two-root
cluster. Unordered complex and collapsed pairs are both included. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem exists_uniform_hillHminusLabels_real_high_pairs (q : PeriodOneHminusOne) :
    ∃ rho : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < rho ∧ rho ≤ Real.pi/4 ∧ 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ ha : IsRealPeriodOneHminusOne a, ∀ n : ℕ+, N ≤ (n:ℕ) →
        ∃ p : HillHminusRealHighPair a n rho,
          hillHminusLabels a ha (2*(n:ℕ)-1)=p.left ∧ hillHminusLabels a ha (2*(n:ℕ))=p.right := by
  obtain ⟨rho,N,V,hrho,hrhop,hN,hV,hq,hlabels⟩ := exists_hillHminus_global_real_characteristic_labels q
  refine ⟨rho,N,V,hrho,hrhop,hN,hV,hq,?_⟩
  intro a ha har n hn
  obtain ⟨lambda,hm,hroots,hpairs,hcounts,hmem⟩ := hlabels a ha har
  have hlabel : HillHminusRealCharacteristicLabeling a N rho lambda := by
    refine ⟨hN,hrho,hrhop,hm,hroots,?_,hcounts,hmem⟩
    intro j hj
    have he : (N:ℕ)+(j-(N:ℕ))=j := Nat.add_sub_of_le hj
    have hp := hpairs (j-(N:ℕ))
    have hpn : (⟨(N:ℕ)+(j-(N:ℕ)),by omega⟩ : ℕ+)=⟨j,by omega⟩ := by
      apply PNat.coe_injective
      exact he
    rw [hpn] at hp
    simpa only [he] using hp
  exact (hillHminusLabels_spec_at a har N rho lambda hlabel).high_pair (n:ℕ) hn

theorem exists_common_canonical_high_symmetric_comparison (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    ∃ rho : ℝ, ∃ N : ℕ, ∃ U : Set PeriodOneHminusOne,
      0 < rho ∧ rho ≤ Real.pi/4 ∧ 2 ≤ N ∧ IsOpen U ∧ q ∈ U ∧
      U ⊆ hillHminusCanonicalGapDomain ∩ hillHminusCanonicalZeroSequenceDomain ∧
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ a ∈ U, ∃ l u : ℂ,
        HillHminusHighGapPair a n rho l u ∧
        hillHminusCanonicalEnergyMidpoint n a=(l+u)/2 ∧ hillHminusCanonicalGapSquare n a=(u-l)^2 := by
  obtain ⟨rho,NP,V,hrho,hrhop,hNP,hV,hqV,hcomplex⟩ := exists_hillHminus_high_gap_pairs q
  have hpairs : ∀ n : ℕ+, NP ≤ (n:ℕ) → ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n rho l u := by
    intro n hn a ha
    obtain ⟨K,_,_,_,_,_,hK⟩ := hcomplex n hn
    obtain ⟨l,u,hpair,_⟩ := (hK a ha).2
    exact ⟨l,u,hpair⟩
  obtain ⟨rhoR,NR,W,_,_,hNR,hW,hqW,hreal⟩ := exists_uniform_hillHminusLabels_real_high_pairs q
  have hqG := real_mem_hillHminusCanonicalGapDomain q hr
  have hqZ := real_mem_hillHminusCanonicalZeroSequenceDomain q hr
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp
    (((hV.inter hW).inter (isOpen_hillHminusCanonicalGapDomain.inter isOpen_hillHminusCanonicalZeroSequenceDomain)).mem_nhds
      ⟨⟨hqV,hqW⟩,hqG,hqZ⟩)
  let U := ball q s
  let N := max NP NR
  have hUV : U ⊆ V := fun a ha => (hsub ha).1.1
  have hUW : U ⊆ W := fun a ha => (hsub ha).1.2
  have hUD : U ⊆ hillHminusCanonicalGapDomain ∩ hillHminusCanonicalZeroSequenceDomain := fun a ha => (hsub ha).2
  refine ⟨rho,N,U,hrho,hrhop,hNR.trans (le_max_right _ _),isOpen_ball,mem_ball_self hs,hUD,?_⟩
  intro n hn
  have hnP : NP ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnR : NR ≤ (n:ℕ) := (le_max_right _ _).trans hn
  have hrealdata (a : PeriodOneHminusOne) (ha : a ∈ U) (har : IsRealPeriodOneHminusOne a)
      (l u : ℂ) (hp : HillHminusHighGapPair a n rho l u) :
      hillHminusCanonicalEnergyMidpoint n a=(l+u)/2 ∧ hillHminusCanonicalGapSquare n a=(u-l)^2 := by
    obtain ⟨p,hl,hu⟩ := hreal a (hUW ha) har n hnR
    rw [hillHminusCanonicalEnergyMidpoint_real n a har,hillHminusCanonicalGapSquare_eq_real a har n,hl,hu]
    rcases hp.eq_or_swap p.pair with h | h <;> rw [h.1,h.2] <;> constructor <;> ring
  have hsym := analyticOnNhd_hillHminus_symmetric_gap_data n rho hrho V hV (hpairs n hnP)
  have hmid : EqOn (hillHminusCanonicalEnergyMidpoint n) (hillHminusGapMidpoint n rho) U := by
    apply analytic_eqOn_of_real_periodOneHminus U isOpen_ball (convex_ball q s).isPreconnected
      ⟨q,mem_ball_self hs,hr⟩ _ _
      ((analyticOnNhd_hillHminusCanonicalEnergyMidpoint n).mono (fun a ha => (hUD ha).2)) (hsym.1.mono hUV)
    intro a ha har
    obtain ⟨l,u,hp⟩ := hpairs n hnP a (hUV ha)
    exact (hrealdata a ha har l u hp).1.trans (hp.symmetric_gap_data hrho).1.symm
  have hgap : EqOn (hillHminusCanonicalGapSquare n) (fun a => 4*hillHminusSquaredHalfGap n rho a) U := by
    apply analytic_eqOn_of_real_periodOneHminus U isOpen_ball (convex_ball q s).isPreconnected
      ⟨q,mem_ball_self hs,hr⟩ _ _
      ((analyticOnNhd_hillHminusCanonicalGapSquare n).mono (fun a ha => (hUD ha).1))
      (analyticOnNhd_const.mul (hsym.2.mono hUV))
    intro a ha har
    obtain ⟨l,u,hp⟩ := hpairs n hnP a (hUV ha)
    rw [(hrealdata a ha har l u hp).2,(hp.symmetric_gap_data hrho).2]
    ring
  intro a ha
  obtain ⟨l,u,hp⟩ := hpairs n hnP a (hUV ha)
  refine ⟨l,u,hp,(hmid ha).trans (hp.symmetric_gap_data hrho).1,?_⟩
  rw [hgap ha]
  change 4*hillHminusSquaredHalfGap n rho a=(u-l)^2
  rw [(hp.symmetric_gap_data hrho).2]
  ring

end NLS.KdV
