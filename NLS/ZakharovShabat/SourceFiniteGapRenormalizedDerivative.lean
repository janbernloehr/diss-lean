import NLS.ZakharovShabat.SourceHilbertActionReductionWeighted
import NLS.ZakharovShabat.SourceFiniteGapOpenFrequency
import NLS.ZakharovShabat.SourceFiniteGapRenormalizedHamiltonian
import NLS.ZakharovShabat.SourceSecondMomentFrequencyAnalytic

/-! # The physical renormalized Hamiltonian's action derivative

Along the actual curve decreasing an open action at unit speed, the
physical correction has derivative minus the renormalized frequency.
The mass and weighted-action terms are differentiated explicitly.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W X V : Set (CoeffPair 2)}
  {s u : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- A usable derivative statement for physical H3 at every open finite-gap action. -/
theorem hasDerivAt_physicalActionReductionHamiltonian_three_frequency
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 3) (-D.finiteGapOpenFrequency φ hf n hn) 0 := by
  obtain ⟨Y,Z,_,F⟩ := exists_sourceFullAbelianDifferentialData (p := 2) (by simp) (by norm_num)
  obtain ⟨V₁,B₁,V₂,_,_,_,_,_,_,v,E⟩ := exists_sourceAngularTheta_theorem13_1_iv (p := 2) (by simp) (by norm_num)
  obtain ⟨R,hR,_,hcircle,hseg⟩ := exists_sourceCanonicalRoot_circle_enclosing_finite_gaps
    (by simp) (by norm_num) φ.val hf.toFinset 0
  have hd := D.hasDerivAt_physicalActionReductionHamiltonian_three E F φ hf n hn R hR hcircle hseg
  simpa only [finiteGapOpenFrequency,neg_neg] using hd.differentiableAt.hasDerivAt

/-- Evaluate the literal physical correction on the actual reduction curve. -/
def physicalActionReductionRenormalizedHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (t : ℝ) : ℂ :=
  sourceFiniteGapRenormalizedHamiltonian (by simp) (by norm_num) (D.hilbertActionReduction φ n t)
    (D.hilbertActionReduction_mem_finiteGap φ hf n t)

/-- Differentiating the physical finite-gap correction gives minus the
actual normalized moment-sum frequency. -/
theorem hasDerivAt_physicalActionReductionRenormalizedHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) X u)
    (hs : SourcePsiNormalizedComplexExtension (by simp) (by norm_num) V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem φ.val) n ≠ 0) :
    HasDerivAt (D.physicalActionReductionRenormalizedHamiltonian φ hf n)
      (-A.renormalizedFrequency n φ.val) 0 := by
  have hact := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) φ.val φ.property n
  have ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
    apply lt_of_le_of_ne hact.1
    intro he
    have hz := hact.2.2.mp (Complex.ext he.symm hact.2.1)
    exact hn (by simpa only [sourcePeriodicGapDisplacement_apply] using hz)
  let M := sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1
  let S := ∑' k : ℤ, (2*(k:ℂ)*Real.pi)^2*sourceComplexAction (by simp) (by norm_num) k φ.val
  let c := (2*(n:ℂ)*Real.pi)^2
  have ht : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 0 := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := (0:ℝ)))
  have hm := (((hasDerivAt_const (0:ℝ) M).sub ht).pow 2).const_mul (2:ℂ)
  have hw := (hasDerivAt_const (0:ℝ) S).sub (ht.const_mul c)
  have hthree := D.hasDerivAt_physicalActionReductionHamiltonian_three_frequency φ hf n hn
  have he := D.finiteGapOpenFrequency_renormalized_eq_moments A hs φ hf n hn
  have hd : HasDerivAt
      (fun t : ℝ => D.physicalActionReductionHamiltonian φ hf n 3 t - 2*(M-(t:ℂ))^2 - (S-c*(t:ℂ)))
      (-A.renormalizedFrequency n φ.val) 0 := by
    convert (hthree.sub hm).sub hw using 1
    all_goals try rfl
    all_goals
      dsimp only [SourceAbelianMomentAtlas.renormalizedFrequency,M,c]
      simp only [Pi.sub_apply,ofReal_zero,sub_zero]
      linear_combination he
  apply hd.congr_of_eventuallyEq
  filter_upwards [gt_mem_nhds ha] with t ht
  dsimp only [physicalActionReductionRenormalizedHamiltonian,sourceFiniteGapRenormalizedHamiltonian,
    physicalActionReductionHamiltonian,M,S,c]
  rw [D.hilbertActionReduction_physical_mass φ hf n hn ha t ht.le,
    D.hilbertActionReduction_weighted_actions φ hf n hn ha _ t ht.le]

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
