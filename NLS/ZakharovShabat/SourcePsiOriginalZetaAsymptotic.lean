import NLS.ZakharovShabat.SourcePsiOriginalQuotientError
import NLS.ZakharovShabat.SourcePsiOriginalRatioEstimate
import NLS.ZakharovShabat.SourcePsiDoubleOmittedProduct

/-!
# Equation (2.26) on the original disks

The weighted literal double-omitted product splits exactly into i/pi,
an O(1/(n-m)) term, and an lp error, uniformly in the omitted index.
Every complex base source in W and every full lp root input are allowed.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reciprocal-distance term uses only the fixed base midpoint. -/
def sourcePsiZetaReciprocalTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n m : ℤ) (z : ℂ) : ℂ :=
  I*(((n-m:ℤ):ℂ)/(sourceStandardRootMidpoint hp hp1 φ n-z)-(Real.pi:ℂ)⁻¹)

/-- The remaining, sequence-controlled term in (2.26). -/
def sourcePsiZetaSequenceTerm (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z-I/(Real.pi:ℂ)-
    sourcePsiZetaReciprocalTerm hp hp1 φ n m z

theorem sourcePsi_zeta_decomposition (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    ((n-m:ℤ):ℂ)*sourcePsiZeta hp hp1 n m a ψ z = I/(Real.pi:ℂ)+
      sourcePsiZetaReciprocalTerm hp hp1 φ n m z+sourcePsiZetaSequenceTerm hp hp1 φ n m a ψ z := by
  unfold sourcePsiZetaSequenceTerm
  ring

theorem SourceCorollary10_6Data.zeta_originalAsymptotic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (hV : IsOpen V) (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ t ∈ U, ∀ n : ℤ, ∃ E : Coeff p, ‖E‖ ≤ C ∧
        ∀ m : ℤ, m ≠ n → ∀ z ∈ D m,
          ‖sourcePsiZetaReciprocalTerm hp hp1 φ n m z‖ ≤ K/‖((n-m:ℤ):ℂ)‖ ∧
          ‖sourcePsiZetaSequenceTerm hp hp1 φ n m t.1 t.2 z‖ ≤ ‖E m‖ := by
  let b := sourcePeriodicMidpointDisplacement hp hp1 φ
  obtain ⟨U₀,hU₀,hbase,L,hL,hbound⟩ := H.local_replaced_allDisk_quotient_errorBound hD hV φ hφW hφV a₀ b
  obtain ⟨A,hA,hAbound⟩ := hD.exists_uniform_lattice_bound
  let U := U₀ ∩ (univ ×ˢ (W ∩ V))
  let K := (A+‖b‖)/Real.pi*c
  have hc : 0 ≤ c := zero_le_one.trans hD.one_le
  refine ⟨U,hU₀.inter (isOpen_univ.prod (hW.inter hV)),⟨hbase,mem_univ _,hφW,hφV⟩,
    (fun _ ht => ht.2),K,c*L,by dsimp [K]; positivity,mul_nonneg hc hL,?_⟩
  intro t ht n
  obtain ⟨E,hE,_,hQ⟩ := hbound t ht.1 n
  let F : Coeff p := (c:ℂ) • E
  have hF (m : ℤ) : ‖F m‖ = c*‖E m‖ := by
    simp only [F,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hc]
  refine ⟨F,?_,?_⟩
  · rw [show ‖F‖ = c*‖E‖ from by simp only [F,norm_smul,Complex.norm_real,Real.norm_of_nonneg hc]]
    exact mul_le_mul_of_nonneg_left hE hc
  intro m hmn z hz
  let ξ := sourceStandardRootMidpoint hp hp1 φ n
  let a := Coeff.deleteCoordinate n t.1+lp.single p n (b n)
  have hξ : ξ ∈ D n := hD.gap φ hφV n (sourcePeriodicMidpoint_mem_segment hp hp1 φ n)
  have hs := hD.weighted_separation_closure n m hmn ξ hξ z (subset_closure hz)
  have hξb : ‖ξ-(Real.pi:ℂ)*n‖ ≤ ‖b‖ := by
    simpa only [b,sourcePeriodicMidpointDisplacement_apply,ξ,sourceStandardRootMidpoint] using
      lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' b n
  have hroot : displacedRoots a n = ξ := by
    simp only [a,displacedRoots,lp.coeFn_add,Pi.add_apply,Coeff.deleteCoordinate_apply_same,
      lp.single_apply_self,zero_add,b,sourcePeriodicMidpointDisplacement_apply,ξ,sourceStandardRootMidpoint]
    ring
  have hdom : z ∈ sourceStandardRootOmittedDomain hp hp1 t.2 m := by
    intro k hkm hzkg
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) hz (hD.gap t.2 ht.2.2.2 k hzkg)
  have hreg : sourcePsiGapRegularFactor hp hp1 n m a t.2 z = sourcePsiZeta hp hp1 n m t.1 t.2 z := by
    rw [sourcePsiGapRegularFactor_eq_zeta hp hp1 n m hmn a t.2 z hdom (by simpa only [hroot] using hs.1)]
    apply sourcePsiZeta_congr
    intro k hkn _
    simp only [a,lp.coeFn_add,Pi.add_apply,Coeff.deleteCoordinate_apply_other n k hkn,
      lp.single_apply_ne _ _ _ hkn,add_zero]
  have hrec : ‖sourcePsiZetaReciprocalTerm hp hp1 φ n m z‖ ≤ K/‖((n-m:ℤ):ℂ)‖ := by
    simp only [sourcePsiZetaReciprocalTerm,norm_mul,norm_I,one_mul]
    exact sourcePsi_indexRatio_error_bound n m hmn ξ z hs.1.symm A ‖b‖ c (hAbound m z hz) hξb hs.2
  have he : sourcePsiZetaSequenceTerm hp hp1 φ n m t.1 t.2 z =
      I*(((n-m:ℤ):ℂ)/(ξ-z))*(sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,t.2))-1) := by
    unfold sourcePsiZetaSequenceTerm sourcePsiZetaReciprocalTerm
    rw [← hreg]
    simp only [sourcePsiGapRegularFactor,hroot]
    dsimp only [ξ]
    ring
  refine ⟨hrec,?_⟩
  rw [he,hF,norm_mul,norm_mul,norm_I,one_mul,norm_div]
  exact mul_le_mul hs.2 (hQ m z hz) (norm_nonneg _) hc

end NLS.ZakharovShabat
