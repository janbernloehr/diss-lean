import NLS.ZakharovShabat.NLSWKBFullPlaneComparison
import NLS.ZakharovShabat.ClassicalSwapSymmetry
import NLS.ZakharovShabat.NLSHamiltonianPhaseReflection

/-! # Both actual WKB columns and the monodromy Dirichlet entry -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem exists_nlsWKB_both_endpoint_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, 1≤‖z‖ →
      let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
      let m := exp (nlsHamiltonianPhase a b N z)
      let v := nlsWKBVector a b N z 0
      let u := (nlsWKBVector (-b) (-a) N (-z) 0).swap
      ‖classicalSolution Φ z v 1-m • v‖≤C/(2*‖z‖)^N*Real.exp |z.im| ∧
      ‖classicalSolution Φ z u 1-m⁻¹ • u‖≤C/(2*‖z‖)^N*Real.exp |z.im| := by
  obtain ⟨C₁,hC₁,h₁⟩ := exists_nlsWKBVector_full_plane_endpoint_error_bound a b ha hb hpa hpb N
  obtain ⟨C₂,hC₂,h₂⟩ := exists_nlsWKBVector_full_plane_endpoint_error_bound (-b) (-a) hb.neg ha.neg
    (fun x => congrArg Neg.neg (hpb x)) (fun x => congrArg Neg.neg (hpa x)) N
  refine ⟨C₁+C₂,by positivity,?_⟩
  intro z hz
  dsimp only
  constructor
  · have h := h₁ z hz
    change ‖classicalSolution _ z _ 1-exp (nlsHamiltonianPhase a b N z) • _‖≤_ at h
    exact h.trans (by gcongr;linarith)
  · have h := h₂ (-z) (by simpa only [norm_neg] using hz)
    have he := classicalSolution_swap (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
      z (nlsWKBVector (-b) (-a) N (-z) 0) ⟨1,by norm_num⟩
    rw [classicalSwapPotential_ofFunctions] at he
    change classicalSolution _ z _ 1=(classicalSolution _ (-z) _ 1).swap at he
    rw [he]
    have hn (x y : ℂ × ℂ) (m : ℂ) : ‖x.swap-m • y.swap‖=‖x-m • y‖ := by
      simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,Prod.fst_swap,Prod.snd_swap,
        Prod.smul_fst,Prod.smul_snd,max_comm]
    rw [hn]
    rw [← exp_nlsHamiltonianPhase_signedSwap a b ha hb hpa hpb N z]
    change ‖classicalSolution _ (-z) _ 1-exp (nlsHamiltonianPhase (-b) (-a) N (-z)) • _‖≤_ at h
    simp only [norm_neg,neg_im,abs_neg] at h
    exact h.trans (by gcongr;linarith)

private theorem norm_two_column_entry_error (p q ℓ u m : ℂ) (E : ℝ)
    (hE : 0≤E) (hd : 1-ℓ*u≠0) (hu : ‖u‖≤1) (hi : ‖(1-ℓ*u)⁻¹‖≤2)
    (he : ‖p+q*ℓ-m‖≤E) (hf : ‖p*u+q-m⁻¹*u‖≤E) :
    ‖q-u*(m⁻¹-m)/(1-ℓ*u)‖≤4*E := by
  have hid : q-u*(m⁻¹-m)/(1-ℓ*u)=((p*u+q-m⁻¹*u)-u*(p+q*ℓ-m))*(1-ℓ*u)⁻¹ := by
    apply (mul_right_cancel₀ hd)
    rw [sub_mul,div_mul_cancel₀ _ hd,mul_assoc,inv_mul_cancel₀ hd,mul_one]
    ring
  have hn : ‖(p*u+q-m⁻¹*u)-u*(p+q*ℓ-m)‖≤2*E := by
    calc
      _ ≤ ‖p*u+q-m⁻¹*u‖+‖u‖*‖p+q*ℓ-m‖ := by simpa only [norm_mul] using norm_sub_le (p*u+q-m⁻¹*u) (u*(p+q*ℓ-m))
      _ ≤ E+1*E := add_le_add hf (mul_le_mul hu he (norm_nonneg _) (by norm_num))
      _ = _ := by ring
  rw [hid,norm_mul]
  exact (mul_le_mul hn hi (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem exists_nlsWKB_initial_basis_small (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (N : ℕ) :
    ∃ R : ℝ, 1≤R ∧ ∀ z : ℂ, R≤‖z‖ →
      let ℓ := -I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
      let u := -I*nlsRiccatiApproximation (-b) (-a) N (2*I*(-z))⁻¹ 0
      ‖ℓ‖≤1/2 ∧ ‖u‖≤1/2 ∧ 1-ℓ*u≠0 ∧ ‖(1-ℓ*u)⁻¹‖≤2 := by
  obtain ⟨A,hA,h₁⟩ := exists_nlsRiccatiApproximation_bound a b ha hb N
  obtain ⟨B,hB,h₂⟩ := exists_nlsRiccatiApproximation_bound (-b) (-a) hb.neg ha.neg N
  refine ⟨max 1 (A+B),le_max_left _ _,?_⟩
  intro z hz
  let ℓ := -I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
  let u := -I*nlsRiccatiApproximation (-b) (-a) N (2*I*(-z))⁻¹ 0
  have hz1 : 1≤‖z‖ := (le_max_left _ _).trans hz
  have hzpos : 0<‖z‖ := by linarith
  have hAzn : A≤‖z‖ := by have := (le_max_right _ _).trans hz;linarith
  have hBzn : B≤‖z‖ := by have := (le_max_right _ _).trans hz;linarith
  have hw (v : ℂ) (hv : 1≤‖v‖) : ‖(2*I*v)⁻¹‖≤1 := by
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hn₁ := h₁ 0 (by norm_num) _ (hw z hz1)
  have hn₂ := h₂ 0 (by norm_num) _ (hw (-z) (by simpa using hz1))
  have hℓ : ‖ℓ‖≤1/2 := by
    dsimp only [ℓ]
    simp only [norm_mul,norm_neg,norm_I,one_mul]
    apply hn₁.trans
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity : 0<2*‖z‖)).mpr (by linarith)
  have hu : ‖u‖≤1/2 := by
    dsimp only [u]
    simp only [norm_mul,norm_neg,norm_I,one_mul]
    apply hn₂.trans
    simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one,norm_neg]
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ (by positivity : 0<2*‖z‖)).mpr (by linarith)
  have hp : ‖ℓ*u‖≤1/4 := by rw [norm_mul];nlinarith [norm_nonneg ℓ,norm_nonneg u]
  have hd : 1/2≤‖(1:ℂ)-ℓ*u‖ := by
    have he := norm_sub_norm_le (1:ℂ) (ℓ*u)
    rw [norm_one] at he
    linarith
  have hdpos : 0<‖(1:ℂ)-ℓ*u‖ := by linarith
  refine ⟨hℓ,hu,norm_pos_iff.mp hdpos,?_⟩
  rw [norm_inv]
  exact (inv_le_comm₀ hdpos (by norm_num : 0<(2:ℝ))).mpr (by norm_num;exact hd)

theorem exists_classicalMonodromy_upper_right_wkb_error_bound (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (N : ℕ) :
    ∃ R C : ℝ, 1≤R ∧ 0<C ∧ ∀ z : ℂ, R≤‖z‖ →
      let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
      let m := exp (nlsHamiltonianPhase a b N z)
      let ℓ := -I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
      let u := -I*nlsRiccatiApproximation (-b) (-a) N (2*I*(-z))⁻¹ 0
      ‖(classicalMonodromy Φ z) 0 1-u*(m⁻¹-m)/(1-ℓ*u)‖≤
        C/(2*‖z‖)^N*Real.exp |z.im| := by
  obtain ⟨R,hR,hbasis⟩ := exists_nlsWKB_initial_basis_small a b ha hb N
  obtain ⟨C,hC,hboth⟩ := exists_nlsWKB_both_endpoint_error_bound a b ha hb hpa hpb N
  refine ⟨R,4*C,hR,by positivity,?_⟩
  intro z hz
  dsimp only
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let m := exp (nlsHamiltonianPhase a b N z)
  let ℓ := -I*nlsRiccatiApproximation a b N (2*I*z)⁻¹ 0
  let u := -I*nlsRiccatiApproximation (-b) (-a) N (2*I*(-z))⁻¹ 0
  let p := (classicalMonodromy Φ z) 0 0
  let q := (classicalMonodromy Φ z) 0 1
  let E := C/(2*‖z‖)^N*Real.exp |z.im|
  obtain ⟨_hℓ,hu,hd,hi⟩ := hbasis z hz
  have hv := hboth z (hR.trans hz)
  dsimp only at hv
  simp only [nlsWKBVector,nlsWKBCarrier_zero,mul_one] at hv
  change ‖classicalSolution Φ z (1,ℓ) 1-m • (1,ℓ)‖≤E ∧
    ‖classicalSolution Φ z (u,1) 1-m⁻¹ • (u,1)‖≤E at hv
  have hlinear (x y : ℂ) : (classicalSolution Φ z (x,y) 1).1=x*p+y*q := by
    rw [classicalSolution_eq_columns Φ z (x,y) ⟨1,by norm_num⟩]
    rfl
  have he := (norm_fst_le (classicalSolution Φ z (1,ℓ) 1-m • (1,ℓ))).trans hv.1
  have hf := (norm_fst_le (classicalSolution Φ z (u,1) 1-m⁻¹ • (u,1))).trans hv.2
  simp only [Prod.fst_sub,Prod.smul_fst,smul_eq_mul,hlinear,one_mul,mul_one] at he hf
  have hh := norm_two_column_entry_error p q ℓ u m E (by dsimp only [E];positivity) hd (hu.trans (by norm_num)) hi (by simpa only [mul_comm] using he)
    (by simpa only [mul_comm] using hf)
  change ‖q-u*(m⁻¹-m)/(1-ℓ*u)‖≤_
  exact hh.trans_eq (by dsimp only [E];ring)

end NLS.ZakharovShabat
