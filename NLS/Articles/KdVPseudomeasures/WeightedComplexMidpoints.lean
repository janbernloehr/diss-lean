import NLS.Articles.KdVPseudomeasures.WeightedComplexMidpointTail
import NLS.Articles.KdVPseudomeasures.ComplexDirichletLabelBounds

/-! FULL complex source Theorem2.1(ii): the actual entire midpoint sequence
in every original weighted endpoint space, including its locally bounded map.
The signed extension is even and zero at zero; positive indices are literal n. -/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue NLS.ComplexAnalysis

/-- The actual source tau_n-minus-mu_n, evenly extended to both original
Fourier tails, with the harmless central coefficient fixed to zero. -/
def sourceWeightedDirichletMidpointValues (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (k : ℤ) : ℂ :=
  if hk : k = 0 then 0 else sourceComplexDirichletMidpoint r hr (sourceForgetWeight w r q)
    (by rw [sourceForgetWeight_val];exact hp) ⟨k.natAbs,Int.natAbs_pos.mpr hk⟩

/-- One common cutoff precedes the weight, with an explicit bound for the
ENTIRE actual weighted midpoint sequence on each original weighted norm ball. -/
theorem exists_uniform_sourceWeightedDirichletMidpointValues_bound
    (r : ℝ) (hr : AdmissiblePredualOrder r) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ w : SpectralWeight, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ∀ k : ℤ,
        ‖(w.negativeSobolev r k:ℂ)*sourceWeightedDirichletMidpointValues w r hr q hp k‖ ≤ C := by
  obtain ⟨NT,hNT,_,hT⟩ := exists_uniform_sourceWeightedComplexMidpoint_high_bound r hr R 2
  obtain ⟨NL,_,hL⟩ := source_uniform_canonical_complex_labels r hr R
  obtain ⟨ND,_,hD⟩ := exists_uniform_sourceEndpointDirichlet_sourceCircles r hr R
  let N := max NT (max NL ND)
  have hN : 2 ≤ N := hNT.trans (le_max_left _ _)
  let B := sourceSpectralBound r hr R
  let T := 128*(6*Real.sqrt 6+12)
  have hB : 0 ≤ B := sourceSpectralBound_nonneg r hr R
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue;positivity
  have hTpos : 0 ≤ T := by dsimp [T];positivity
  refine ⟨N,hN,?_⟩
  intro w
  let C := w (N:ℤ)*(4*freeHillValue N+14*(N:ℝ)+8*B)+T*|R|
  have hC : 0 ≤ C := by dsimp [C];positivity [w.positive (N:ℤ)]
  refine ⟨C,hC,?_⟩
  intro q hq hp k
  by_cases hk0 : k = 0
  · subst k
    simpa [sourceWeightedDirichletMidpointValues] using hC
  let n : ℕ+ := ⟨k.natAbs,Int.natAbs_pos.mpr hk0⟩
  let u := sourceForgetWeight w r q
  have hu : ‖u‖ ≤ R := (norm_sourceForgetWeight_le w r q).trans hq
  have hup : IsPeriodicDistribution 1 u.val.toTempered := by rw [sourceForgetWeight_val];exact hp
  have hval : sourceWeightedDirichletMidpointValues w r hr q hp k =
      sourceComplexDirichletMidpoint r hr u hup n := by rw [sourceWeightedDirichletMidpointValues,dif_neg hk0]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((w.negativeSobolev r).positive k),hval]
  by_cases hk : N ≤ k.natAbs
  · have hnT : NT ≤ (n:ℕ) := (le_max_left _ _).trans hk
    have ht := hT w q hq hp n hnT
    have hw : w.negativeSobolev r k = w.negativeSobolev r (n:ℤ) := by
      change w.negativeSobolev r k = w.negativeSobolev r (k.natAbs:ℤ)
      simp only [Int.natCast_natAbs,SpectralWeight.negativeSobolev_apply,
        SpectralWeight.apply_abs,Weight.sobolev_apply,Int.cast_abs,abs_abs]
    rw [hw]
    apply ht.trans
    dsimp only [C,T] at *
    nlinarith [le_abs_self R,mul_nonneg (w.positive (N:ℤ)).le
      (show 0 ≤ 4*freeHillValue N+14*(N:ℝ)+8*B by positivity)]
  · let NN : ℕ+ := ⟨N,by omega⟩
    have hnN : n ≤ NN := by change k.natAbs ≤ N;omega
    have hnD : ND ≤ (NN:ℕ) := by dsimp [N,NN];omega
    have hnL : NL ≤ N := by dsimp [N];omega
    have hmu := sourceComplexDirichletLabel_low_norm_le r hr R u hu hup NN n hnN
      (hD u hu hup NN hnD).2.1
    obtain ⟨p,_,hpr⟩ := (hL u hu).high_pair N hnL
    have hpstrip : |p.right.re-freeHillValue N| ≤ 6*(N:ℝ) := p.right_mem
    have hright : (sourceHillComplexLabels r hr u (2*N)).re ≤ freeHillValue N+6*(N:ℝ) := by
      rw [hpr]
      linarith [(abs_le.mp hpstrip).2]
    have hlabel (j : ℕ) (hj : j ≤ 2*N) :
        ‖sourceHillComplexLabels r hr u j‖ ≤ 2*freeHillValue N+12*(N:ℝ)+4*B := by
      have hs := sourceHillSpectrum_norm_le_on_ball r hr R u hu _
        ((sourceHillComplexLabels_spec r hr u).spectral j)
      have hm := re_le_of_complexLexLE (ordered_sourceHillComplexLabels r hr u j (2*N) hj)
      dsimp only [B] at *
      linarith
    have hplus := hlabel (2*(n:ℕ)) (by dsimp [n];omega)
    have hminus := hlabel (2*(n:ℕ)-1) (by dsimp [n];omega)
    have htau : ‖(sourceHillComplexLabels r hr u (2*(n:ℕ))+
        sourceHillComplexLabels r hr u (2*(n:ℕ)-1))/2‖ ≤ 2*freeHillValue N+12*(N:ℝ)+4*B := by
      rw [norm_div,Complex.norm_ofNat]
      have ht := norm_add_le (sourceHillComplexLabels r hr u (2*(n:ℕ)))
        (sourceHillComplexLabels r hr u (2*(n:ℕ)-1))
      linarith
    have hmid : ‖sourceComplexDirichletMidpoint r hr u hup n‖ ≤
        4*freeHillValue N+14*(N:ℝ)+8*B := by
      have ht := norm_sub_le ((sourceHillComplexLabels r hr u (2*(n:ℕ))+
        sourceHillComplexLabels r hr u (2*(n:ℕ)-1))/2)
          (originalComplexDirichletLabels (sourceOriginalComplexPotential r hr u hup) n)
      change ‖sourceComplexDirichletMidpoint r hr u hup n‖ ≤ _ at ht
      change ‖originalComplexDirichletLabels (sourceOriginalComplexPotential r hr u hup) n‖ ≤
        2*freeHillValue N+2*(N:ℝ)+4*B at hmu
      linarith
    have hw : w.negativeSobolev r k ≤ w (N:ℤ) := by
      have hkw : w k ≤ w (N:ℤ) := by
        have he := w.monotone_nat (show k.natAbs ≤ N by omega)
        simpa only [Int.natCast_natAbs,SpectralWeight.apply_abs] using he
      rw [SpectralWeight.negativeSobolev_eq_product]
      have hs : Weight.sobolev (-r) k ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (abs_nonneg _)) (neg_nonpos.mpr hr.1)
      exact (mul_le_mul_of_nonneg_left hs (w.positive k).le).trans (by simpa only [mul_one] using hkw)
    apply (mul_le_mul hw hmid (norm_nonneg _) (w.positive (N:ℤ)).le).trans
    dsimp only [C]
    exact le_add_of_nonneg_right (mul_nonneg hTpos (abs_nonneg R))

/-- The entire actual original weighted midpoint sequence belongs to the
genuine endpoint space, for every complex physically period-one potential. -/
theorem sourceWeightedDirichletMidpointValues_mem (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) :
    Memℓp (fun k => (w.negativeSobolev r k:ℂ)*sourceWeightedDirichletMidpointValues w r hr q hp k) ⊤ := by
  obtain ⟨_,_,hb⟩ := exists_uniform_sourceWeightedDirichletMidpointValues_bound r hr ‖q‖
  obtain ⟨C,_,hC⟩ := hb w
  apply memℓp_infty
  exact ⟨C,by rintro _ ⟨k,rfl⟩;exact hC q le_rfl hp k⟩

/-- The ACTUAL full original complex midpoint sequence in its weighted infinity norm. -/
def sourceWeightedDirichletMidpoints (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) : WeightedCoeff (w.negativeSobolev r) ⊤ :=
  ⟨sourceWeightedDirichletMidpointValues w r hr q hp,sourceWeightedDirichletMidpointValues_mem w r hr q hp⟩

/-- Every original positive index is exactly its actual tau_n-minus-mu_n. -/
theorem sourceWeightedDirichletMidpoints_nat_apply (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r)
    (q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤)
    (hp : IsPeriodicDistribution 1 q.val.toTempered) (n : ℕ+) :
    (sourceWeightedDirichletMidpoints w r hr q hp).val (n:ℤ) =
      sourceComplexDirichletMidpoint r hr (sourceForgetWeight w r q)
        (by rw [sourceForgetWeight_val];exact hp) n := by
  have hn : (n:ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt n.property)
  simp only [sourceWeightedDirichletMidpoints,sourceWeightedDirichletMidpointValues,
    dif_neg hn,Int.natAbs_natCast]
  rw [show (⟨(n:ℕ),n.property⟩ : ℕ+) = n from Subtype.ext rfl]

/-- FULL source Theorem2.1(ii), on all complex physically period-one
sources, hence in particular on the original complex mean-zero source.
The complete actual sequence is bounded on EVERY original weighted norm ball. -/
theorem sourceTheorem2_1_ii (w : SpectralWeight) (r : ℝ) (hr : AdmissiblePredualOrder r) :
    (∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤,
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered,
      Memℓp (fun k => (w.negativeSobolev r k:ℂ)*sourceWeightedDirichletMidpointValues w r hr q hp k) ⊤) ∧
    ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤, ‖q‖ ≤ R →
      ∀ hp : IsPeriodicDistribution 1 q.val.toTempered, ‖sourceWeightedDirichletMidpoints w r hr q hp‖ ≤ C := by
  refine ⟨sourceWeightedDirichletMidpointValues_mem w r hr,?_⟩
  intro R
  obtain ⟨_,_,hbound⟩ := exists_uniform_sourceWeightedDirichletMidpointValues_bound r hr R
  obtain ⟨C,hC,hb⟩ := hbound w
  refine ⟨C,hC,?_⟩
  intro q hq hp
  change ‖WeightedCoeff.weightEquiv (w.negativeSobolev r) ⊤ _‖ ≤ C
  apply lp.norm_le_of_forall_le hC
  intro k
  exact hb q hq hp k

/-- Literal local boundedness in the ORIGINAL weighted norm topology on
the physical period-one source subtype, with its ACTUAL weighted target norm. -/
theorem sourceWeightedDirichletMidpoints_locallyBounded (w : SpectralWeight) (r : ℝ)
    (hr : AdmissiblePredualOrder r)
    (q : {q : PeriodicFourierLebesgue (2:ℝ) (w.negativeSobolev r) ⊤ |
      IsPeriodicDistribution 1 q.val.toTempered}) :
    ∃ U ∈ 𝓝 q, ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ U,
      ‖sourceWeightedDirichletMidpoints w r hr p.val p.property‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := (sourceTheorem2_1_ii w r hr).2 (‖q.val‖+1)
  refine ⟨Metric.ball q 1,Metric.ball_mem_nhds q (by norm_num),C,hC,?_⟩
  intro p hp
  apply hbound p.val _ p.property
  have hd : ‖p.val-q.val‖ < 1 := by simpa only [Metric.mem_ball,Subtype.dist_eq,dist_eq_norm] using hp
  have ht := norm_le_norm_sub_add p.val q.val
  linarith

end NLS.Articles.KdVPseudomeasures
