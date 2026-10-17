import NLS.ZakharovShabat.SourceBirkhoffComplexClosingBound
import NLS.ZakharovShabat.NormalizedWeightedClosingCompatibility
import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexSequence
import NLS.SequenceSpaces.FiniteHeadTailBound

/-! # Constructed complex weighted sequence bounds

Uniform compatibility of the adapted maps transfers the complex coordinate
bound to normalized weighted sources. A fixed finite head and two bounded
adapted sequences control the entire weighted output on an open complex
neighborhood of each weighted real source.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem pullback_intersection
    {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (J : E → F) (hJ : Continuous J) (a : E) (U : Set F) (V : Set E)
    (hU : IsOpen U) (hV : IsOpen V) (haU : J a ∈ U) (haV : a ∈ V) :
    ∃ Z : Set E, IsOpen Z ∧ a ∈ Z ∧ ∀ x ∈ Z, J x ∈ U ∧ x ∈ V := by
  exact ⟨(J ⁻¹' U) ∩ V,(hU.preimage hJ).inter hV,⟨haU,haV⟩,fun _ hx => hx⟩

private theorem weighted_coordinate_bound (w : SpectralWeight) (P : CoeffPair p)
    (n : ℤ) (z : ℂ) (C : ℝ)
    (hb : ‖z‖ ≤ C*(‖(normalizedWeightedSource w P).fst (-n)‖+
      ‖(normalizedWeightedSource w P).snd n‖)) :
    ‖(w (2*n):ℂ)*z‖ ≤ C*(‖P.fst (-n)‖+‖P.snd n‖) := by
  simp only [normalizedWeightedSource_fst,normalizedWeightedSource_snd,mul_neg,
    SpectralWeight.apply_neg,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (w.toWeight.positive _)] at hb
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.toWeight.positive _)]
  calc
    w (2*n)*‖z‖ ≤ w (2*n)*(C*(‖P.fst (-n)‖/w (2*n)+‖P.snd n‖/w (2*n))) :=
      mul_le_mul_of_nonneg_left hb (w.toWeight.positive _).le
    _ = _ := by field_simp [(w.toWeight.positive (2*n)).ne']

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Actual weighted complex membership and a local bound, with no spectral majorant premises. -/
theorem exists_local_normalizedWeightedBirkhoffMap_bound
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (φ : realTypeSourceLocus p) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ.val ∈ U ∧
      (∀ ψ ∈ U, normalizedWeightedSource w ψ ∈ W) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U,
        (Memℓp (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n) p ∧
         Memℓp (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n) p) ∧
        ‖normalizedWeightedBirkhoffMap hp hp1 s w ψ‖ ≤ M := by
  let φu : realTypeSourceLocus p :=
    ⟨normalizedWeightedSource w φ.val,normalizedWeightedSource_realType w φ.val φ.property⟩
  obtain ⟨C,hC,Nc,_,hclosing⟩ := D.exists_uniform_complex_closing_bound φu
  obtain ⟨Nd,_,Vd,hoD,hφD,hdecode⟩ := exists_uniform_normalizedWeightedClosingMap_decode hp hp1 w φ.val
  obtain ⟨r,hr,Nw,_,hw⟩ := exists_fixedBall_normalizedWeightedClosingMap_derivative hp hp1 w φ.val 1 (by norm_num)
  let N := max Nc (max Nd Nw)
  obtain ⟨K,hNK,Uc,hoC,hφC,hCW,hbound⟩ := hclosing N (by dsimp [N]; omega)
  obtain ⟨Ub,hoB,hφB,_,M₀,hM₀,hbase⟩ := D.locally_bounded φu.val (D.real_subset φu.property)
  obtain ⟨U,hoU,hφU,hsub⟩ := pullback_intersection (normalizedWeightedSource w)
    (continuous_normalizedWeightedSource w) φ.val (Uc ∩ Ub) (Vd ∩ ball φ.val (4*r))
    (hoC.inter hoB) (hoD.inter isOpen_ball) ⟨hφC,hφB⟩ ⟨hφD,mem_ball_self (by positivity)⟩
  let A := fun ψ => normalizedWeightedClosingMap hp w ψ N
  let B₀ := ‖φ.val‖+4*r+resonantCenterRemainderBallConstant p (‖φ.val‖+1)*r^2
  have hB₀ : 0 ≤ B₀ := by
    have hK := (resonantCenterRemainderBallConstant_pos (p := p) (‖φ.val‖+1)
      (by positivity : 0 < ‖φ.val‖+1)).le
    dsimp [B₀]
    positivity
  have hAnorm (ψ : CoeffPair p) (hψ : ψ ∈ U) : ‖A ψ‖ ≤ B₀ := by
    have hψb := (hsub ψ hψ).2.2
    have hR := ((hw N (by dsimp [N]; omega)).2.1 ψ hψb).2
    have hd : ‖ψ-φ.val‖ < 4*r := by simpa only [mem_ball,dist_eq_norm] using hψb
    have hψnorm := norm_le_norm_sub_add ψ φ.val
    have ha := norm_le_norm_sub_add (A ψ) ψ
    change ‖A ψ-ψ‖ ≤ resonantCenterRemainderBallConstant p (‖φ.val‖+1)*r^2 at hR
    dsimp [B₀]
    linarith
  let S := Finset.Icc (-(K:ℤ)) K
  let H : ℤ → ℂ := fun n => (w (2*n):ℂ)*(M₀:ℂ)
  let M := ‖Coeff.finiteHead (p := p) S H‖+C*(2*B₀)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨U,hoU,hφU,(fun ψ hψ => hCW (hsub ψ hψ).1.1),M,hM,?_⟩
  intro ψ hψ
  have hψC := (hsub ψ hψ).1.1
  have hF : ‖sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)‖ ≤ M₀ := hbase _ (hsub ψ hψ).1.2
  have he := hdecode N (by dsimp [N]; omega) ψ (hsub ψ hψ).2.1
  have htail (n : ℤ) (hn : n ∉ S) :
      ‖(w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n‖ ≤
        C*(‖(A ψ).fst (-n)‖+‖(A ψ).snd n‖) ∧
      ‖(w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n‖ ≤
        C*(‖(A ψ).fst (-n)‖+‖(A ψ).snd n‖) := by
    have hKn : K ≤ n.natAbs := by simp only [S,Finset.mem_Icc] at hn; omega
    have hb := hbound _ hψC n hKn
    rw [← he] at hb
    exact ⟨weighted_coordinate_bound w (A ψ) n _ C hb.1,
      weighted_coordinate_bound w (A ψ) n _ C hb.2⟩
  have hhead (n : ℤ) :
      ‖(w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n‖ ≤ ‖H n‖ ∧
      ‖(w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n‖ ≤ ‖H n‖ := by
    have hx := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' _ n).trans
      ((norm_fst_le _).trans hF)
    have hy := (lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' _ n).trans
      ((norm_snd_le _).trans hF)
    constructor
    · simpa only [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hM₀,abs_of_pos (w.toWeight.positive _)] using
        mul_le_mul_of_nonneg_left hx (w.toWeight.positive (2*n)).le
    · simpa only [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg hM₀,abs_of_pos (w.toWeight.positive _)] using
        mul_le_mul_of_nonneg_left hy (w.toWeight.positive (2*n)).le
  have hx := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n)
    H S (Coeff.reflection (A ψ).fst) (A ψ).snd C hC (fun n _ => (hhead n).1)
    (fun n hn => (htail n hn).1)
  have hy := Coeff.memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n)
    H S (Coeff.reflection (A ψ).fst) (A ψ).snd C hC (fun n _ => (hhead n).2)
    (fun n hn => (htail n hn).2)
  have hab : ‖Coeff.reflection (A ψ).fst‖+‖(A ψ).snd‖ ≤ 2*B₀ := by
    rw [Coeff.reflection.norm_map]
    have ha := (WithLp.norm_fst_le (Coeff p) (A ψ)).trans (hAnorm ψ hψ)
    have hb := (WithLp.norm_snd_le (Coeff p) (A ψ)).trans (hAnorm ψ hψ)
    linarith
  have htot := add_le_add (le_refl ‖Coeff.finiteHead (p := p) S H‖)
    (mul_le_mul_of_nonneg_left hab hC)
  exact ⟨⟨hx.1,hy.1⟩,max_le (hx.2.trans htot) (hy.2.trans htot)⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
