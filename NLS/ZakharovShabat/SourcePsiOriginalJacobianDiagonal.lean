import NLS.ZakharovShabat.SourcePsiOriginalJacobianNonzero
import NLS.ZakharovShabat.SourceEquation2_26

/-!
# Uniform diagonal decomposition on the original real domain

The actual diagonal is exactly 2 plus a reciprocal-distance error and
an lp sequence. The neighborhood and both bounds precede the omitted
index. Evaluating (2.26) at the mean-value points preserves its disk
majorants and includes every finite head coordinate.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceLemma12_4Data.originalJacobian_diagonal_decomposition
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V) (a₀ : Coeff p) :
    ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a₀,φ) ∈ U ∧ U ⊆ univ ×ˢ (W ∩ V) ∧
      ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ t ∈ U,
        IsRealType (CoeffPair.toMax p t.2) →
        t.1 ∈ sourcePsiOriginalRootPlacement D → (∀ k : ℤ, (t.1 k).im = 0) →
        ∀ n : ℤ, ∃ R : ℤ → ℂ, ∃ S : Coeff p, R n = 0 ∧ S n = 0 ∧ ‖S‖ ≤ C ∧
          ∀ m : ℤ, m ≠ n →
            sourcePsiOriginalJacobianEntry hp hp1 n m m t.1 t.2 = 2+R m+S m ∧
            ‖R m‖ ≤ K/‖((n-m:ℤ):ℂ)‖ := by
  classical
  obtain ⟨U,hU,hbase,hUV,K,C,hK,hC,hb⟩ :=
    H.previous.quotients.zeta_originalAsymptotic hW hD hV φ hφW hφV a₀
  have hscale : ‖-(2*(Real.pi:ℂ)*I)‖ = 2*Real.pi := by
    simp [Real.pi_pos.le]
  have hconst : -(2*(Real.pi:ℂ)*I)*(I/(Real.pi:ℂ)) = 2 := by
    field_simp
    simp [Complex.I_sq]
  refine ⟨U,hU,hbase,hUV,2*Real.pi*K,2*Real.pi*C,by positivity,by positivity,?_⟩
  intro t ht hreal ha haReal n
  obtain ⟨E,hE,hEb⟩ := hb t ht n
  have hmean (m : ℤ) (hmn : m ≠ n) := H.originalJacobianEntry_diagonal_meanValue
    hD t.2 (hUV ht).2.1 (hUV ht).2.2 hreal n m hmn t.1 ha haReal
  choose μ hμ hJ using hmean
  let R : ℤ → ℂ := fun m => if h : m = n then 0 else
    -(2*(Real.pi:ℂ)*I)*sourcePsiZetaReciprocalTerm hp hp1 φ n m (μ m h)
  let s : ℤ → ℂ := fun m => if h : m = n then 0 else
    -(2*(Real.pi:ℂ)*I)*sourcePsiZetaSequenceTerm hp hp1 φ n m t.1 t.2 (μ m h)
  let A : Coeff p := (2*(Real.pi:ℂ)) • E
  have hA (m : ℤ) : ‖A m‖ = (2*Real.pi)*‖E m‖ := by
    simp [A,Real.pi_pos.le]
  have hdom (m : ℤ) : ‖s m‖ ≤ ‖A m‖ := by
    rw [hA]
    by_cases hm : m = n
    · simp only [s,dif_pos hm,norm_zero]
      positivity
    · simp only [s,dif_neg hm,norm_mul,hscale]
      exact mul_le_mul_of_nonneg_left
        (hEb m hm (μ m hm) (hD.gap t.2 (hUV ht).2.2 m (hμ m hm))).2 (by positivity)
  let S : Coeff p := ⟨s,(lp.memℓp A).mono' hdom⟩
  refine ⟨R,S,by simp [R],by simp [S,s],?_,?_⟩
  · apply (lp.norm_mono (zero_lt_one.trans hp1).ne' hdom).trans
    simpa only [A,norm_smul,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le] using mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 2*Real.pi)
  · intro m hm
    have hbounds := hEb m hm (μ m hm) (hD.gap t.2 (hUV ht).2.2 m (hμ m hm))
    constructor
    · change _ = 2+R m+s m
      simp only [R,s,dif_neg hm]
      rw [hJ m hm, sourcePsi_zeta_decomposition hp hp1 φ n m t.1 t.2 (μ m hm), mul_add, mul_add, hconst]
    · simp only [R,dif_neg hm,norm_mul,hscale]
      exact (mul_le_mul_of_nonneg_left hbounds.1 (by positivity : 0 ≤ 2*Real.pi)).trans_eq (by ring)

end NLS.ZakharovShabat
