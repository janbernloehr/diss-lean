import NLS.ZakharovShabat.SourcePsiOriginalJacobianDiagonal
import NLS.ZakharovShabat.SourcePsiOriginalJacobianOffDiagonal

/-!
# Lemma 12.5 on the original real domain

The matrix belongs to the actual bounded root derivative from Lemma
12.4. It is real, has nonzero retained diagonals, and admits the printed
diagonal and off-diagonal estimates. One open neighborhood in the full
real source/root topology and both constants work before choosing any
omitted index. The supplied original source domain and disks are retained.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Exact decompositions and common bounds for the actual Jacobian. -/
structure SourcePsiOriginalJacobianBounds (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (ψ : CoeffPair p) (K C : ℝ) : Prop where
  real : ∀ n m r : ℤ, (sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ).im = 0
  diagonal_nonzero : ∀ n m : ℤ, m ≠ n → sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ ≠ 0
  diagonal : ∀ n : ℤ, ∃ R : ℤ → ℂ, ∃ S : Coeff p,
    R n = 0 ∧ S n = 0 ∧ ‖S‖ ≤ C ∧ ∀ m : ℤ, m ≠ n →
      sourcePsiOriginalJacobianEntry hp hp1 n m m a ψ = 2+R m+S m ∧
      ‖R m‖ ≤ K/‖((n-m:ℤ):ℂ)‖
  off_diagonal : ∃ B : Coeff p, ‖B‖ ≤ C ∧
    (∀ m : ℤ, B m = (sourcePsiOriginalOffDiagonalRowSup hp hp1 a ψ m:ℂ)) ∧
    ∀ n m r : ℤ, m ≠ r →
      ‖((m-r:ℤ):ℂ)*sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ‖ ≤ ‖B m‖

/-- The off-diagonal estimate in the source's reciprocal-distance form. -/
theorem SourcePsiOriginalJacobianBounds.offDiagonal_div_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {a : Coeff p} {ψ : CoeffPair p} {K C : ℝ}
    (H : SourcePsiOriginalJacobianBounds hp hp1 a ψ K C) :
    ∃ B : Coeff p, ‖B‖ ≤ C ∧ ∀ n m r : ℤ, m ≠ r →
      ‖sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ‖ ≤ ‖B m‖/‖((m-r:ℤ):ℂ)‖ := by
  obtain ⟨B,hB,_,hb⟩ := H.off_diagonal
  refine ⟨B,hB,?_⟩
  intro n m r hmr
  have hd : 0 < ‖((m-r:ℤ):ℂ)‖ := norm_pos_iff.mpr (by exact_mod_cast sub_ne_zero.mpr hmr)
  apply (le_div_iff₀ hd).mpr
  simpa only [norm_mul,mul_comm] using hb n m r hmr

structure SourceLemma12_5Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceLemma12_4Data hp hp1 W
  originalOmega : ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
    SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
    ∀ t₀ : realTypeSourceSubmodule p × RealCoeff p, (t₀.1:CoeffPair p) ∈ W →
      t₀ ∈ sourcePsiOriginalOmega V D →
      ∃ U : Set (realTypeSourceSubmodule p × RealCoeff p), IsOpen U ∧ t₀ ∈ U ∧
        U ⊆ sourcePsiOriginalOmega V D ∧ ∃ K C : ℝ, 0 ≤ K ∧ 0 ≤ C ∧
          ∀ t ∈ U, SourcePsiOriginalJacobianBounds hp hp1
            (RealCoeff.complexCLM p t.2) (t.1:CoeffPair p) K C

theorem SourceLemma12_4Data.lemma12_5
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (hW : IsOpen W) : SourceLemma12_5Data hp hp1 W := by
  refine ⟨H,?_⟩
  intro V D c hD hV t₀ hφW hbase
  obtain ⟨Ud,hUd,hbased,hUdV,K,Cd,hK,hCd,hd⟩ := H.originalJacobian_diagonal_decomposition
    hW hD hV t₀.1 hφW hbase.1 (RealCoeff.complexCLM p t₀.2)
  obtain ⟨Uo,hUo,hbaseo,_,Co,hCo,ho⟩ := H.originalJacobian_offDiagonal_rowSup
    hW hD hV t₀.1 hφW hbase.1 (RealCoeff.complexCLM p t₀.2)
  let inc : realTypeSourceSubmodule p × RealCoeff p → Coeff p × CoeffPair p :=
    fun t => (RealCoeff.complexCLM p t.2,(t.1:CoeffPair p))
  have hic : Continuous inc := ((RealCoeff.complexCLM p).continuous.comp continuous_snd).prodMk
    (continuous_subtype_val.comp continuous_fst)
  let U := sourcePsiOriginalOmega V D ∩ inc ⁻¹' (Ud ∩ Uo)
  refine ⟨U,(hD.isOpen_originalOmega hV).inter ((hUd.inter hUo).preimage hic),
    ⟨hbase,hbased,hbaseo⟩,(fun _ ht => ht.1),K,Cd+Co,hK,add_nonneg hCd hCo,?_⟩
  intro t ht
  have hψW : (t.1:CoeffPair p) ∈ W := (hUdV ht.2.1).2.1
  have ha : RealCoeff.complexCLM p t.2 ∈ sourcePsiOriginalRootPlacement D := ht.1.2
  have haReal (k : ℤ) : ((RealCoeff.complexCLM p t.2) k).im = 0 := by simp
  refine ⟨(fun n m r => H.originalJacobianEntry_real t.1 hψW t.1.property n m r _ haReal),
    (fun n m hmn => H.originalJacobianEntry_diagonal_ne_zero hD t.1 hψW ht.1.1 t.1.property
      n m hmn _ ha haReal),?_,?_⟩
  · intro n
    obtain ⟨R,S,hRn,hSn,hS,hentry⟩ := hd (inc t) ht.2.1 t.1.property ha haReal n
    exact ⟨R,S,hRn,hSn,hS.trans (le_add_of_nonneg_right hCo),hentry⟩
  · obtain ⟨B,hB,hBm,hentry⟩ := ho (inc t) ht.2.2 t.1.property ha
    exact ⟨B,hB.trans (le_add_of_nonneg_left hCd),hBm,hentry⟩

/-- The original source neighborhood is unchanged and contains every real source. -/
theorem sourceLemma12_5 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceLemma12_5Data hp hp1 W := by
  obtain ⟨W,hW,hc,hr,H⟩ := sourceLemma12_4 hp hp1
  exact ⟨W,hW,hc,hr,H.lemma12_5 hW⟩

end NLS.ZakharovShabat
