import NLS.KdV.HillHminusOneGlobalRealLabels

/-! # Common real H^-1 label families with arbitrarily large cutoffs

The central source control and actual high pairs are retained in one
labeling interface. A prescribed finite minimum cutoff can be imposed
before choosing the common complex potential neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped Classical
namespace NLS.KdV

structure HillHminusRealCharacteristicLabeling
    (q : PeriodOneHminusOne) (N : ℕ) (r : ℝ) (lambda : ℕ → ℝ) : Prop where
  central_control : HillHminusCentralControl q N
  radius_pos : 0 < r
  radius_le : r ≤ Real.pi/4
  monotone : Monotone lambda
  roots : ∀ z : ℂ, hillHminusRadicand q z = 0 ↔ ∃ j : ℕ, z = (lambda j : ℂ)
  high_pair : ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ p : HillHminusRealHighPair q n r,
    lambda (2*(n : ℕ)-1) = p.left ∧ lambda (2*(n : ℕ)) = p.right
  central_counts : ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if lambda j = x then 1 else 0) =
    if (x : ℂ) ∈ hillCentralDisc N then analyticOrderNatAt (hillHminusRadicand q) x else 0
  central_mem : ∀ j < 2*N-1, lambda j ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N)

theorem exists_hillHminus_labelings_near (q : PeriodOneHminusOne) (L : ℕ) :
    ∃ N : ℕ, ∃ r : ℝ, ∃ V : Set PeriodOneHminusOne,
      L ≤ N ∧ 2 ≤ N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, IsRealPeriodOneHminusOne a →
        ∃ lambda : ℕ → ℝ, HillHminusRealCharacteristicLabeling a N r lambda := by
  obtain ⟨r,hr,hrpi,Np,Vp,_,hVp,hqp,hpairs⟩ := exists_hillHminus_real_high_pairs q
  obtain ⟨Nc,Vc,hNc,hVc,hqc,hregions⟩ := exists_hillHminus_source_root_regions q r hr
  let N := max (max Np Nc) L
  have hNp : Np ≤ N := (le_max_left Np Nc).trans (le_max_left _ _)
  have hNc' : Nc ≤ N := (le_max_right Np Nc).trans (le_max_left _ _)
  have hN : 2 ≤ N := hNc.trans hNc'
  refine ⟨N,r,Vp ∩ Vc,le_max_right _ _,hN,hVp.inter hVc,⟨hqp,hqc⟩,?_⟩
  intro a ha hreal
  have hcontrol : HillHminusCentralControl a N := by
    refine ⟨hN,?_,?_⟩
    · intro s hs z hz
      exact (hregions N hNc' a ha.2 s hs z hz).1
    · intro s hs z hzc hz
      rcases (hregions N hNc' a ha.2 s hs z hz).2 with h | ⟨_,_,_,h⟩ <;> linarith
  have hp : ∀ k : ℕ, Nonempty (HillHminusRealHighPair a ⟨N+k,by omega⟩ r) := by
    intro k
    exact hpairs _ (by change Np ≤ N+k; omega) a ha.1 hreal
  have hcover : ∀ z : ℂ, hillHminusRadicand a z = 0 → hillCentralSeparator N ≤ z.re →
      ∃ k : ℕ, z ∈ hillHminusGapSquareDisc ⟨N+k,by omega⟩ r := by
    intro z hz hzc
    have hz' : hillHminusRadicand (((1 : ℝ) : ℂ) • a) z = 0 := by simpa using hz
    rcases (hregions N hNc' a ha.2 1 (by norm_num) z hz').2 with h | ⟨n,hn,hzn,_⟩
    · linarith
    · refine ⟨(n : ℕ)-N,?_⟩
      have he : (⟨N+((n : ℕ)-N),by omega⟩ : ℕ+) = n := by
        apply PNat.coe_injective
        change N+((n : ℕ)-N) = (n : ℕ)
        omega
      rw [he]
      have hc : ((Real.pi : ℂ)*(n : ℕ))^2 = (freeHillValue (n : ℕ) : ℂ) := by
        dsimp only [freeHillValue]; push_cast; ring
      change z ∈ closedBall (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)
      rw [hc]
      exact ball_subset_closedBall hzn
  obtain ⟨lambda,hm,hroots,hhigh,hcounts,hmem⟩ :=
    exists_hillHminus_characteristic_labels_of_control a hreal N hcontrol r hrpi hp hcover
  refine ⟨lambda,⟨hcontrol,hr,hrpi,hm,hroots,?_,hcounts,hmem⟩⟩
  intro n hn
  have he : N+((n : ℕ)-N) = (n : ℕ) := by omega
  have he' : (⟨N+((n : ℕ)-N),by omega⟩ : ℕ+) = n := by
    apply PNat.coe_injective
    exact he
  let P : ℕ+ → Prop := fun m => ∃ p : HillHminusRealHighPair a m r,
    lambda (2*(m : ℕ)-1) = p.left ∧ lambda (2*(m : ℕ)) = p.right
  have hp' : P ⟨N+((n : ℕ)-N),by omega⟩ := hhigh ((n : ℕ)-N)
  exact Eq.mp (congrArg P he') hp'

theorem exists_hillHminus_real_characteristic_labeling
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, ∃ r : ℝ, ∃ lambda : ℕ → ℝ, HillHminusRealCharacteristicLabeling q N r lambda := by
  obtain ⟨N,r,_,_,_,_,hqV,hlabels⟩ := exists_hillHminus_labelings_near q 0
  obtain ⟨lambda,h⟩ := hlabels q hqV hq
  exact ⟨N,r,lambda,h⟩

end NLS.KdV
