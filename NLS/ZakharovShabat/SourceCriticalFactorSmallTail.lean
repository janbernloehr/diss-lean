import NLS.ZakharovShabat.SourceCriticalMidpointRowsSmall
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A numerical bound on every sufficiently distant complex gap factor -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A small reciprocal row controls the midpoint product without discarding its decay. -/
theorem norm_midpoint_product_le_exp_of_row (σ τ : ℤ → ℂ) (n : ℤ) (z : ℂ)
    (C ε : ℝ) (hC : 1 ≤ C) (s : Finset ℤ) (hs : ∀ m ∈ s, m ≠ n)
    (hsep : ∀ m ∈ s, |((n-m:ℤ):ℝ)| ≤ C*‖τ m-z‖)
    (hrow : (∑ m ∈ s, ‖σ m-τ m‖/|((m-n:ℤ):ℝ)|) ≤ ε) :
    ‖∏ m ∈ s, (σ m-z)/(τ m-z)‖ ≤ Real.exp (C*ε) := by
  let u : ℤ → ℂ := fun m => (σ m-τ m)/(τ m-z)
  have hden (m : ℤ) (hm : m ∈ s) : τ m ≠ z := by
    intro he
    have hd : 0 < |((n-m:ℤ):ℝ)| := by
      apply abs_pos.mpr
      exact_mod_cast sub_ne_zero.mpr (hs m hm).symm
    have h := hsep m hm
    rw [he,sub_self,norm_zero,mul_zero] at h
    linarith
  have hsum : (∑ m ∈ s, ‖u m‖) ≤ C*ε := by
    calc
      _ ≤ ∑ m ∈ s, C*(‖σ m-τ m‖/|((m-n:ℤ):ℝ)|) := by
        apply Finset.sum_le_sum
        intro m hm
        exact norm_midpoint_displacement_div_le C hC n m (hs m hm).symm _ _ _ (hsep m hm)
      _ = C*(∑ m ∈ s, ‖σ m-τ m‖/|((m-n:ℤ):ℝ)|) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hrow (by linarith)
  have he : (∏ m ∈ s, (σ m-z)/(τ m-z)) = ∏ m ∈ s, (1+u m) := by
    apply Finset.prod_congr rfl
    intro m hm
    exact midpoint_quotient_eq_one_add _ _ _ (hden m hm)
  rw [he]
  have hprod := (s.norm_prod_one_add_sub_one_le u).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)
  have h := norm_add_le ((∏ m ∈ s, (1+u m))-1) (1:ℂ)
  rw [sub_add_cancel,norm_one] at h
  linarith

/-- Small critical and squared-gap rows bound every finite deleted product by three. -/
theorem sourceCriticalQuotientPartialProduct_le_three_of_rows
    (φ ψ : CoeffPair 2) (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j → ∀ z ∈ sourceIsolatingDisc (by simp) (by norm_num) φ N ε i,
      |((i-j:ℤ):ℝ)| ≤ C*‖canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z‖)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourceIsolatingDisc (by simp) (by norm_num) φ N ε n)
    (hcrit : ∀ s : Finset ℤ, (∀ m ∈ s, m ≠ n) →
      (∑ m ∈ s, ‖canonicalCriticalPoints (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m-
        canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m‖/|((m-n:ℤ):ℝ)|) ≤ 1/(2*C))
    (hgap : (∑' m : ℤ, sourceSquaredGapReciprocalTerm (by simp) (by norm_num) ψ n m) ≤ 1/C^2)
    (M : ℕ) :
    ‖sourceSingleRootQuotientPartialProduct (by simp) (by norm_num) n M
      (z,(sourceCriticalDisplacement (by simp) (by norm_num) ψ,ψ))‖ ≤ 3 := by
  let s := (Finset.Icc (-(M:ℤ)) (M:ℤ)).erase n
  let a := sourceCriticalDisplacement (by simp) (by norm_num) ψ
  let P := sourceSingleRootMidpointPartialProduct (by simp) (by norm_num) n M (z,(a,ψ))
  let G := sourceSingleRootGapCorrectionPartialProduct (by simp) (by norm_num) n M (z,(a,ψ))
  have hCpos : 0 < C := by linarith
  have hC2 : 0 < C^2 := sq_pos_of_pos hCpos
  have hrowSmall : (C^2/4)*(∑' m : ℤ, sourceSquaredGapReciprocalTerm
      (by simp) (by norm_num) ψ n m) ≤ 1/2 := by
    have h := (le_div_iff₀ hC2).mp hgap
    nlinarith
  have hs (m : ℤ) (hm : m ∈ s) : m ≠ n := Finset.ne_of_mem_erase hm
  have he (m : ℤ) : displacedRoots a m = canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    simp only [displacedRoots,a,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply]
    ring
  have hP : ‖P‖ ≤ Real.exp (1/2:ℝ) := by
    have h := norm_midpoint_product_le_exp_of_row (displacedRoots a)
      (fun m => canonicalPeriodicMidpoint (by simp) (by norm_num)
        (periodOnePotential ψ) (periodOnePotential_mem ψ) m) n z C (1/(2*C)) hC s hs
      (fun m hm => hsep n m (hs m hm).symm z hz)
      (by simpa only [he] using hcrit s hs)
    have hc : C*(1/(2*C)) = (1/2:ℝ) := by field_simp
    simpa only [hc,P,sourceSingleRootMidpointPartialProduct,s] using h
  have hG : ‖G‖ ≤ Real.exp (1/2:ℝ) := by
    have hsmall (m : ℤ) (hm : m ∈ s) := sourceSingleRootGapRadicand_le_half_of_row_bound
      (by simp) (by norm_num) φ ψ N ε C hC hsep n m (hs m hm).symm z hz hrowSmall
    have h := norm_sourceSingleRootGapCorrectionPartialProduct_sub_one_le
      (by simp) (by norm_num) n M (z,(a,ψ)) hsmall
    have hr := sourceSingleRootGapRadicand_sum_le_reciprocal_row
      (by simp) (by norm_num) φ ψ N ε C hC hsep n z hz s hs
    have hg := (le_div_iff₀ hC2).mp hgap
    have hb : 2*(∑ m ∈ s, ‖sourceSingleRootGapRadicand (by simp) (by norm_num) ψ m z‖) ≤ (1/2:ℝ) := by
      nlinarith
    have hx := h.trans (sub_le_sub_right (Real.exp_le_exp.mpr hb) 1)
    have ht := norm_add_le (G-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at ht
    change ‖G-1‖ ≤ _ at hx
    linarith
  rw [sourceSingleRootQuotientPartialProduct_factor,norm_mul]
  change ‖P‖*‖G‖ ≤ 3
  calc
    _ ≤ Real.exp (1/2:ℝ)*Real.exp (1/2:ℝ) := mul_le_mul hP hG (norm_nonneg G) (Real.exp_nonneg _)
    _ = Real.exp 1 := by rw [← Real.exp_add]; norm_num
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- On a single neighborhood, all sufficiently distant gap factors are bounded by three,
uniformly over their entire complex segments, including collapsed segments. -/
theorem exists_local_sourceCriticalFactor_tail_le_three
    (φ : CoeffPair 2) (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ φ ∈ V ∧ ∃ K : ℕ,
      ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs → ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n,
        ‖sourceCriticalRootRatioExtension (by simp) (by norm_num) n ψ z‖ ≤ 3 := by
  obtain ⟨N,ε,_,_,Vs,hVs,_,hφs,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation (by simp) (by norm_num) φ hφ
  have hCpos : 0 < C := by linarith
  obtain ⟨Vc,hVc,hφc,Kc,hcrit⟩ := exists_uniform_sourceCriticalMidpoint_reciprocal_rows
    φ hφ (1/(2*C)) (by positivity)
  obtain ⟨Vg,hVg,hφg,Kg,hgap⟩ := exists_uniform_sourceSquaredGapPhysicalRows_lt
    (by simp) (by norm_num) φ (show 0 < 1/C^2 by positivity)
  obtain ⟨Ng,εg,_,_,Vd,hVd,_,hφd,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs (by simp) (by norm_num) φ hφ
  let V := (Vs ∩ Vc) ∩ (Vg ∩ Vd)
  let K := max (max Kc Kg) (max (N+1) (Ng+1))
  refine ⟨V,(hVs.inter hVc).inter (hVg.inter hVd),⟨⟨hφs,hφc⟩,⟨hφg,hφd⟩⟩,K,?_⟩
  intro ψ hψ n hn z hz
  have hnN : N < n.natAbs := by dsimp [K] at hn; omega
  have hnNg : Ng < n.natAbs := by dsimp [K] at hn; omega
  have hzgeom := sourcePeriodicSegment_subset_isolatingDisc (by simp) (by norm_num)
    φ ψ Ng εg n (hcluster ψ hψ.2.2 n) hz
  have hzdisc : z ∈ sourceIsolatingDisc (by simp) (by norm_num) φ N ε n := by
    simpa only [sourceIsolatingDisc,if_neg (not_le.mpr hnNg),if_neg (not_le.mpr hnN)] using hzgeom
  let a := sourceCriticalDisplacement (by simp) (by norm_num) ψ
  have hdom := sourceSingleRootQuotientJointDomain_of_tail_isolation (by simp) (by norm_num)
    φ ψ a N Ng ε εg (hcluster ψ hψ.2.2) hdisjoint n hnN hnNg z hzdisc
  have hlim := ((tendsto_sourceSingleRootQuotientPartialProduct (by simp) (by norm_num)
    n Set.univ (z,(a,ψ)) hdom)).norm
  have hb : ‖sourceSingleRootQuotientJointProduct (by simp) (by norm_num) n (z,(a,ψ))‖ ≤ 3 := by
    apply le_of_tendsto hlim
    apply Filter.Eventually.of_forall
    intro M
    exact sourceCriticalQuotientPartialProduct_le_three_of_rows φ ψ N ε C hC (hsep ψ hψ.1.1)
      n z hzdisc (hcrit ψ hψ.1.2 n (by dsimp [K] at hn; omega))
      (hgap ψ hψ.2.1 n (by dsimp [K] at hn; omega)).le M
  simpa only [sourceCriticalRootRatioExtension,norm_mul,norm_neg,norm_I,one_mul,a,
    sourceCriticalDisplacement] using hb

end NLS.ZakharovShabat
