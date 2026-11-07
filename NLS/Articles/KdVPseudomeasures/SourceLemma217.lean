import NLS.Articles.KdVPseudomeasures.SourceLemma216
import NLS.Articles.KdVPseudomeasures.SpectralDiagonalRoot

/-! The unique analytic root on exactly the printed closed source ball,
with the literal threshold (35) and displacement constant of Lemma 2.17. -/
noncomputable section
open Set NLS.KdV
open NLS.Fourier NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def SourceDiagonalBall (r m : ℝ) :=
  {q : FourierLebesgueSpace (2:ℝ) (-r) ⊤ // ‖q‖≤2*m ∧ q.val (mode 0)=0}

/-- Analyticity on a closed ball means a single ambient extension is
analytic at every point, including boundary points. -/
def SourceLemma217RootOnBall (r : ℝ) (hr : AdmissiblePredualOrder r) (m : ℝ) (n : ℕ)
    (α : SourceDiagonalBall r m → ℂ) : Prop :=
  (∃ A : FourierLebesgueSpace (2:ℝ) (-r) ⊤ → ℂ,
    ∀ q : SourceDiagonalBall r m, A q.val=α q ∧ AnalyticAt ℝ A q.val) ∧
  ∀ q : SourceDiagonalBall r m,
    α q-(freeHillValue n:ℂ)-(sourceEndpointEntries r hr n (q.val,α q)).1=0 ∧
    ‖α q-(freeHillValue n:ℂ)‖≤8*sourceCoefficientConstant r*m^2/(n:ℝ)^(1/2-r)

theorem source_threshold35_radius (r C m : ℝ) (hr1 : r<1/2)
    (hC : sourceCoefficientConstant r≤C) (hm : 1≤m) (n : ℕ) (hn : 1≤n)
    (h35 : 16*C*m/(n:ℝ)^(1/2-r)≤1/2) :
    8*sourceCoefficientConstant r*m^2/(n:ℝ)^(1/2-r)≤m/4 := by
  have hscale := source_threshold35_bound r C m n hn h35
  have hcs : sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*m≤1/32 :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) (by linarith)).trans hscale
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n:ℝ)^(r-1/2)=((n:ℝ)^(1/2-r))⁻¹ := by
    rw [← Real.rpow_neg hnR.le]
    congr 1
    ring
  have hcpos := sourceCoefficientConstant_one_le r hr1
  rw [div_eq_mul_inv,← he]
  nlinarith [mul_le_mul_of_nonneg_right hcs (by linarith : (0:ℝ)≤m)]

theorem source_threshold35_source_small (r : ℝ) (hr : AdmissiblePredualOrder r)
    (C m : ℝ) (hC : sourceCoefficientConstant r≤C) (hm : 1≤m)
    (n : ℕ) (hn : 2≤n) (h35 : 16*C*m/(n:ℝ)^(1/2-r)≤1/2)
    (q : FourierLebesgueSpace (2:ℝ) (-r) ⊤) (hq : ‖q‖≤2*m) :
    endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖<1/2 := by
  have hw := source_threshold35_small r C m hC hr.2 hm n hn h35 ‖q‖ hq
  have h0 : 0≤endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ := by
    positivity [endpointHillConstant_pos r hr.2]
  unfold sourceCoefficientConstant at hw
  nlinarith

/-- Full Lemma 2.17. Uniqueness is equality of functions on the entire
closed source ball, among all root selections obeying the printed bound. -/
theorem sourceLemma2_17_threshold35 (r : ℝ) (hr : AdmissiblePredualOrder r)
    (C m : ℝ) (hC : sourceCoefficientConstant r≤C) (hm : 1≤m)
    (n : ℕ) (hn : 2≤n) (h35 : 16*C*m/(n:ℝ)^(1/2-r)≤1/2) :
    (8*sourceCoefficientConstant r*m^2/(n:ℝ)^(1/2-r)≤m/4) ∧
    ∃! α : SourceDiagonalBall r m → ℂ, SourceLemma217RootOnBall r hr m n α := by
  have hn1 : 1≤n := by omega
  have hbound := source_threshold35_radius r C m hr.2 hC hm n hn1 h35
  have hcpos : 0≤sourceCoefficientConstant r := by
    linarith [sourceCoefficientConstant_one_le r hr.2]
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn1
  have hnp : (0:ℝ)<n := by linarith
  have hmindex : m≤(n:ℝ)/32 := by
    have hpow : (n:ℝ)^(1/2-r)≤n := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hnR (show 1/2-r≤(1:ℝ) by have hh:=hr.1; linarith)
    have ht := (div_le_iff₀ (Real.rpow_pos_of_pos hnp (1/2-r))).mp h35
    have hCp : 1≤C := (sourceCoefficientConstant_one_le r hr.2).trans hC
    nlinarith [mul_le_mul_of_nonneg_right hCp (by linarith : (0:ℝ)≤m)]
  let A := sourceDiagonalRoot r hr n hn1
  let α := fun q : SourceDiagonalBall r m => A q.val
  have hsmall (q : SourceDiagonalBall r m) :=
    source_threshold35_source_small r hr C m hC hm n hn h35 q.val q.property.1
  refine ⟨hbound,α,?_,?_⟩
  · constructor
    · exact ⟨A,fun q => ⟨rfl,realAnalyticAt_sourceDiagonalRoot r hr n hn1 q.val (hsmall q)⟩⟩
    · intro q
      have hs := sourceDiagonalRoot_spec r hr n hn1 q.val (hsmall q).le
      refine ⟨hs.2.1,?_⟩
      have he := sourceDiagonalRoot_error_le r hr n hn1 q.val (hsmall q).le
      rw [q.property.2,sub_zero] at he
      have hQ : ‖q.val‖^2≤4*m^2 := by nlinarith [norm_nonneg q.val,q.property.1]
      have heq : (n:ℝ)^(r-1/2)=((n:ℝ)^(1/2-r))⁻¹ := by
        rw [← Real.rpow_neg hnp.le]
        congr 1
        ring
      have hbase : endpointHillConstant r≤sourceCoefficientConstant r := by
        unfold sourceCoefficientConstant
        linarith [endpointHillConstant_pos r hr.2]
      calc
        _ ≤ 2*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q.val‖^2 := by convert he using 1; ring
        _ ≤ 2*sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*‖q.val‖^2 := by
          gcongr
        _ ≤ 2*sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*(4*m^2) :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
        _ = _ := by rw [heq]; ring
  · intro β hβ
    funext q
    have hb := hβ.2 q
    have hloc : ‖β q-(freeHillValue n:ℂ)‖≤m/4 := hb.2.trans hbound
    have hz : β q ∈ reducedHillStrip n := by
      have hre := (Complex.abs_re_le_norm (β q-(freeHillValue n:ℂ))).trans hloc
      simp only [Complex.sub_re,Complex.ofReal_re] at hre
      change |(β q).re-freeHillValue n|≤6*(n:ℝ)
      linarith
    exact sourceDiagonalRoot_unique r hr n hn1 q.val (hsmall q).le (β q) hz hb.1

end NLS.Articles.KdVPseudomeasures
