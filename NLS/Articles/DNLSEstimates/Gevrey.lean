import NLS.Articles.DNLSEstimates.MainEstimates
import NLS.Fourier.PeriodOneSmoothSynthesis
import NLS.Fourier.SmoothPeriodOneCoefficientAlgebra
import NLS.SequenceSpaces.SpectralWeightHierarchy
/-!
# Physical meaning of the Gevrey weights

Stretched-exponential Fourier decay constructs an actual smooth periodic
function with order-1/sigma factorial derivative growth. Integer-order
optimization proves the converse. The union over positive Fourier radii
is exactly the classical Gevrey class, with every fixed polynomial Sobolev
factor and the paper's even-frequency weight convention retained.
-/
noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.DNLSEstimates

/-- Exponential decay controls every derivative moment with precisely
the factorial growth of Gevrey order 1/sigma. -/
theorem stretched_moment_bound (a σ x : ℝ) (ha : 0 < a) (hσ : 0 < σ) (hx : 0 ≤ x) (k : ℕ) :
    x^k ≤ ((a*σ)^(-1/σ))^k * (k.factorial : ℝ)^(1/σ) * Real.exp (a*x^σ) := by
  let y := a*σ*x^σ
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hh := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp y hy k)
  have hr := Real.rpow_le_rpow (pow_nonneg hy k) hh (by positivity : 0 ≤ 1/σ)
  have hp : (0 : ℝ) < a*σ := mul_pos ha hσ
  have hexp : Real.exp y ^ (1/σ) = Real.exp (a*x^σ) := by
    rw [← Real.exp_mul]
    congr 1
    dsimp [y]
    field_simp
  have hleft : (y^k)^(1/σ) = (a*σ)^((k : ℝ)/σ)*x^k := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hy]
    dsimp [y]
    rw [Real.mul_rpow hp.le (Real.rpow_nonneg hx σ),← Real.rpow_mul hx]
    congr 1
    · congr 1; ring
    · rw [show σ*((k : ℝ)*(1/σ)) = (k : ℝ) by field_simp]
      exact Real.rpow_natCast x k
  rw [hleft,Real.mul_rpow (Real.exp_pos y).le hfac.le,hexp] at hr
  have he : ((a*σ)^(-1/σ))^k*(a*σ)^((k : ℝ)/σ) = 1 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hp.le,← Real.rpow_add hp]
    rw [show (-1/σ)*(k : ℝ)+(k : ℝ)/σ = 0 by ring,Real.rpow_zero]
  have hmul := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ ((a*σ)^(-1/σ))^k)
  calc
    x^k = ((a*σ)^(-1/σ))^k*((a*σ)^((k : ℝ)/σ)*x^k) := by rw [← mul_assoc,he,one_mul]
    _ ≤ _ := hmul
    _ = _ := by ring

/-- Stretched exponential tails are summable at every positive exponent. -/
theorem summable_stretched_exponential (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    Summable (fun n : ℤ => Real.exp (-a*|(n : ℝ)|^σ)) := by
  have hlim : Tendsto (fun x : ℝ => (1+x)^2/Real.exp (a*x^σ)) atTop (𝓝 0) := by
    simpa only [zero_mul,Real.exp_zero,mul_one,Real.rpow_two] using
      NLS.SpectralWeight.polynomial_exp_ratio_tendsto_zero (fun _ : ℝ => 0) (fun x : ℝ => x^σ)
        2 0 a ha (_root_.tendsto_rpow_atTop hσ)
        (NLS.SpectralWeight.log_one_add_div_rpow_tendsto_zero σ hσ) (by simp)
  have hseq : Tendsto (fun n : ℕ => NLS.SpectralWeight.sobolev 2 (by norm_num) n /
      NLS.SpectralWeight.stretchedExponential a σ ha.le hσ.le hσ1 n) atTop (𝓝 0) := by
    simpa only [NLS.SpectralWeight.sobolev_apply,NLS.Weight.sobolev_apply,
      NLS.SpectralWeight.stretchedExponential_apply,Int.cast_natCast,Nat.abs_cast,
      Function.comp_def,Real.rpow_two] using
      hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨C,hC,hbound⟩ := NLS.SpectralWeight.le_mul_of_ratio_tendsto_zero _ _ hseq
  apply ((NLS.summable_inverse_bracket (by norm_num : (1 : ℝ) < 2)).mul_left C).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro n
  rw [neg_mul,Real.exp_neg,mul_one_div,← one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity : 0 < (1+|(n : ℝ)|)^ (2 : ℝ))).mpr
  simpa only [NLS.SpectralWeight.sobolev_apply,NLS.Weight.sobolev_apply,
    NLS.SpectralWeight.stretchedExponential_apply,one_mul] using hbound n

/-- Stretched-exponential Fourier decay gives a smooth periodic physical
representative with the classical Gevrey derivative bounds. -/
theorem gevrey_synthesis (c : ℤ → ℂ) (M a σ : ℝ) (hM : 0 ≤ M) (ha : 0 < a)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-a*|(n : ℝ)|^σ)) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ n : ℤ, periodOneCoefficient f n = c n) ∧
      ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ k : ℕ, ∀ x : ℝ,
        ‖iteratedDeriv k f x‖ ≤ C*R^k*(k.factorial : ℝ)^(1/σ) := by
  let A := (a/2*σ)^(-1/σ)
  let R := 2*Real.pi*A
  let E : ℤ → ℝ := fun n => Real.exp (-(a/2)*|(n : ℝ)|^σ)
  let D : ℕ → ℤ → ℂ := fun k n => (2*I*(Real.pi : ℂ)*n)^k*c n
  let G : ℕ → ℝ := fun k => M*R^k*(k.factorial : ℝ)^(1/σ)
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hR : 0 < R := by dsimp [R]; positivity
  have hG (k : ℕ) : 0 ≤ G k := by dsimp [G]; positivity
  have hE : Summable E := summable_stretched_exponential (a/2) σ (by positivity) hσ hσ1
  have hnorm (k : ℕ) (n : ℤ) : ‖D k n‖ ≤ G k*E n := by
    have ht : 0 ≤ |(n : ℝ)| := abs_nonneg _
    have hm := stretched_moment_bound (a/2) σ |(n : ℝ)| (by positivity) hσ ht k
    have hn : ‖(n : ℂ)‖ = |(n : ℝ)| := by simpa only [Complex.ofReal_intCast,Real.norm_eq_abs] using Complex.norm_real (n : ℝ)
    have hdn : ‖D k n‖ = (2*Real.pi)^k*|(n : ℝ)|^k*‖c n‖ := by
      simp only [D,norm_mul,norm_pow,norm_I,Complex.norm_ofNat,
        Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,hn,mul_pow,one_pow,mul_one]
    calc
      ‖D k n‖ = (2*Real.pi)^k*|(n : ℝ)|^k*‖c n‖ := hdn
      _ ≤ (2*Real.pi)^k*|(n : ℝ)|^k*(M*Real.exp (-a*|(n : ℝ)|^σ)) := by gcongr; exact hc n
      _ ≤ (2*Real.pi)^k*(A^k*(k.factorial : ℝ)^(1/σ)*Real.exp (a/2*|(n : ℝ)|^σ))*
          (M*Real.exp (-a*|(n : ℝ)|^σ)) := by gcongr
      _ = G k*E n := by
        dsimp [G,E,R]
        rw [show -(a/2)*|(n : ℝ)|^σ = a/2*|(n : ℝ)|^σ + -a*|(n : ℝ)|^σ by ring,Real.exp_add,mul_pow]
        ring
  have hs (k : ℕ) : Summable (fun n => ‖D k n‖) :=
    (hE.mul_left (G k)).of_nonneg_of_le (fun n => norm_nonneg _) (hnorm k)
  let d : ℕ → NLS.Coeff 1 := fun k => ⟨D k,(memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
    (by simpa only [ENNReal.toReal_one,Real.rpow_one] using hs k)⟩
  have hd (k : ℕ) (n : ℤ) : d (k+1) n = 2*I*(Real.pi : ℂ)*n*d k n := by
    change (2*I*(Real.pi : ℂ)*n)^(k+1)*c n = 2*I*(Real.pi : ℂ)*n*((2*I*(Real.pi : ℂ)*n)^k*c n)
    rw [pow_succ]; ring
  let f := periodOneSynthesis (d 0)
  have hder (k : ℕ) : iteratedDeriv k f = periodOneSynthesis (d k) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [iteratedDeriv_succ,ih]
      funext x
      exact (hasDerivAt_periodOneSynthesis_of_coefficients (d k) (d (k+1)) (hd k) x).deriv
  refine ⟨f,contDiff_periodOneSynthesis_of_derivative_chain d hd,periodOneSynthesis_periodic _,?_,
    M*(∑' n : ℤ, E n),R,mul_nonneg hM (tsum_nonneg (fun n => (Real.exp_pos _).le)),hR,?_⟩
  · intro n
    rw [periodOneCoefficient_synthesis]
    change (2*I*(Real.pi : ℂ)*n)^0*c n = c n
    simp
  · intro k x
    rw [hder k,periodOneSynthesis_eq_tsum]
    have hw (n : ℤ) : ‖d k n*wave (2*n) x‖ = ‖D k n‖ := by
      change ‖D k n*wave (2*n) x‖ = ‖D k n‖
      simp [wave,Complex.norm_exp]
    have hsum : Summable (fun n : ℤ => ‖d k n*wave (2*n) x‖) := by simpa only [hw] using hs k
    calc
      _ ≤ ∑' n : ℤ, ‖d k n*wave (2*n) x‖ := norm_tsum_le_tsum_norm hsum
      _ = ∑' n : ℤ, ‖D k n‖ := tsum_congr hw
      _ ≤ ∑' n : ℤ, G k*E n := (hs k).tsum_le_tsum (hnorm k) (hE.mul_left _)
      _ = _ := by rw [tsum_mul_left]; dsimp [G]; ring

/-- Every Fourier-weighted Gevrey sequence represents an actual smooth
periodic function with the classical order-1/sigma derivative bounds. -/
theorem weighted_gevrey_synthesis {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s a σ : ℝ) (hs : 0 ≤ s) (ha : 0 < a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (c : NLS.WeightedCoeff (NLS.SpectralWeight.gevrey s a σ hs ha.le hσ.le hσ1).toWeight p) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ n : ℤ, periodOneCoefficient f n = c.val n) ∧
      ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ k : ℕ, ∀ x : ℝ,
        ‖iteratedDeriv k f x‖ ≤ C*R^k*(k.factorial : ℝ)^(1/σ) := by
  apply gevrey_synthesis c.val ‖c‖ a σ (norm_nonneg _) ha hσ hσ1
  intro n
  have hw : Real.exp (a*|(n : ℝ)|^σ) ≤ (NLS.SpectralWeight.gevrey s a σ hs ha.le hσ.le hσ1) n := by
    rw [NLS.SpectralWeight.gevrey_apply]
    exact le_mul_of_one_le_left (Real.exp_pos _).le (Real.one_le_rpow (by linarith [abs_nonneg (n : ℝ)]) hs)
  have hb := (NLS.WeightedCoeff.norm_apply_le _ _ c n).trans
    (div_le_div_of_nonneg_left (norm_nonneg c) (Real.exp_pos _) hw)
  simpa only [div_eq_mul_inv,← Real.exp_neg,neg_mul] using hb

/-- Optimizing the integer derivative order turns factorial moment
bounds into stretched-exponential decay. -/
theorem gevrey_moments_decay (v L C R σ : ℝ) (_hv : 0 ≤ v) (hL : 0 < L)
    (hC : 0 ≤ C) (hR : 0 < R) (hσ : 0 < σ)
    (h : ∀ k : ℕ, L^k*v ≤ C*R^k*(k.factorial : ℝ)^(1/σ)) :
    v ≤ 2*C*Real.exp (-Real.log 2*(L/(2*R))^σ) := by
  let t := (L/(2*R))^σ
  let k := ⌊t⌋₊
  have ht : 0 ≤ t := Real.rpow_nonneg (by positivity) _
  have hkt : (k : ℝ) ≤ t := Nat.floor_le ht
  have htk : t < (k : ℝ)+1 := Nat.lt_floor_add_one t
  have hkp : (k : ℝ)^(1/σ) ≤ L/(2*R) := by
    have hh := Real.rpow_le_rpow (Nat.cast_nonneg k) hkt (by positivity : 0 ≤ 1/σ)
    dsimp [t] at hh
    rw [← Real.rpow_mul (by positivity : 0 ≤ L/(2*R)),
      show σ*(1/σ) = 1 by field_simp,Real.rpow_one] at hh
    exact hh
  have hfac : (k.factorial : ℝ)^(1/σ) ≤ ((k : ℝ)^(1/σ))^k := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (k.factorial : ℝ))
      (show (k.factorial : ℝ) ≤ (k : ℝ)^k by exact_mod_cast k.factorial_le_pow)
      (by positivity : 0 ≤ 1/σ)
    simpa only [← Real.rpow_natCast,← Real.rpow_mul (Nat.cast_nonneg k),mul_comm (k : ℝ) (1/σ)] using hh
  have hmoment : L^k*v ≤ C*(L/2)^k := by
    calc
      L^k*v ≤ C*R^k*(k.factorial : ℝ)^(1/σ) := h k
      _ ≤ C*R^k*((k : ℝ)^(1/σ))^k := by gcongr
      _ ≤ C*R^k*(L/(2*R))^k := by gcongr
      _ = _ := by rw [mul_assoc,← mul_pow]; congr 2; field_simp
  have hhalf : v ≤ C*(1/2 : ℝ)^k := by
    apply le_of_mul_le_mul_left (a := L^k) ?_ (pow_pos hL k)
    calc
      L^k*v ≤ C*(L/2)^k := hmoment
      _ = L^k*(C*(1/2 : ℝ)^k) := by simp only [div_eq_mul_inv]; ring
  have hexp : (1/2 : ℝ)^k = Real.exp (-Real.log 2*(k : ℝ)) := by
    rw [mul_comm,Real.exp_nat_mul]
    norm_num [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : (1/2 : ℝ)^k ≤ 2*Real.exp (-Real.log 2*t) := by
    rw [hexp]
    calc
      _ ≤ Real.exp (Real.log 2+-Real.log 2*t) := Real.exp_le_exp.mpr (by nlinarith)
      _ = _ := by rw [Real.exp_add,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact hhalf.trans (by have hh := mul_le_mul_of_nonneg_left he hC; nlinarith)

/-- Unit-period Fourier coefficients are bounded by any pointwise norm
bound on the physical function. -/
theorem periodOneCoefficient_norm_le (f : ℝ → ℂ) (M : ℝ) (h : ∀ x : ℝ, ‖f x‖ ≤ M) (n : ℤ) :
    ‖periodOneCoefficient f n‖ ≤ M := by
  rw [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,unitFourierCoefficient]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := M) (f := fun x => f x*wave (-2*n) x) (fun x _ => by
      simpa [wave,Complex.norm_exp] using h x)
  simpa using hh

/-- Iterated physical differentiation has the exact period-one Fourier
multiplier at every order. -/
theorem periodOneCoefficient_iteratedDeriv (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (k : ℕ) (n : ℤ) :
    periodOneCoefficient (iteratedDeriv k f) n = (2*I*(Real.pi : ℂ)*n)^k*periodOneCoefficient f n := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ',ih (deriv f) (contDiff_infty_iff_deriv.mp hf).2
      (NLS.ZakharovShabat.periodic_deriv_of_periodic f 1 hp),
      periodOneCoefficient_deriv_of_smooth_periodic f hf hp,pow_succ]
    ring

/-- Classical Gevrey derivative growth forces stretched-exponential
Fourier decay, with an explicit positive decay radius. -/
theorem gevrey_coefficients_decay (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : Function.Periodic f 1) (C R σ : ℝ) (hC : 0 ≤ C) (hR : 0 < R) (hσ : 0 < σ)
    (h : ∀ k : ℕ, ∀ x : ℝ, ‖iteratedDeriv k f x‖ ≤ C*R^k*(k.factorial : ℝ)^(1/σ)) :
    ∃ b : ℝ, 0 < b ∧ ∀ n : ℤ,
      ‖periodOneCoefficient f n‖ ≤ 2*C*Real.exp (-b*|(n : ℝ)|^σ) := by
  let b := Real.log 2*(Real.pi/R)^σ
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨b,hb,?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    have hh := periodOneCoefficient_norm_le f C (by simpa using h 0) 0
    simpa only [Int.cast_zero,abs_zero,Real.zero_rpow hσ.ne',mul_zero,neg_zero,Real.exp_zero,mul_one] using
      hh.trans (by linarith : C ≤ 2*C)
  · have hL : 0 < 2*Real.pi*|(n : ℝ)| := by
      apply mul_pos (by positivity)
      exact abs_pos.mpr (by exact_mod_cast hn)
    have hmoment (k : ℕ) : (2*Real.pi*|(n : ℝ)|)^k*‖periodOneCoefficient f n‖ ≤
        C*R^k*(k.factorial : ℝ)^(1/σ) := by
      have hh := periodOneCoefficient_norm_le (iteratedDeriv k f) _ (h k) n
      rw [periodOneCoefficient_iteratedDeriv f hf hp,norm_mul,norm_pow] at hh
      have hn' : ‖(n : ℂ)‖ = |(n : ℝ)| := by
        simpa only [Complex.ofReal_intCast,Real.norm_eq_abs] using Complex.norm_real (n : ℝ)
      simpa only [norm_mul,norm_I,Complex.norm_ofNat,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_pos Real.pi_pos,hn'] using hh
    have hh := gevrey_moments_decay ‖periodOneCoefficient f n‖ (2*Real.pi*|(n : ℝ)|) C R σ
      (norm_nonneg _) hL hC hR hσ hmoment
    have he : (2*Real.pi*|(n : ℝ)|/(2*R))^σ = (Real.pi/R)^σ*|(n : ℝ)|^σ := by
      rw [show 2*Real.pi*|(n : ℝ)|/(2*R) = (Real.pi/R)*|(n : ℝ)| by ring]
      exact Real.mul_rpow (by positivity) (abs_nonneg _)
    rw [he] at hh
    simpa only [b,mul_assoc,neg_mul] using hh

/-- Any strictly positive Fourier decay radius supplies every polynomial
Sobolev factor at a smaller positive Gevrey radius. -/
theorem memlp_gevrey_of_decay {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (c : ℤ → ℂ) (M b σ s : ℝ) (_hM : 0 ≤ M) (hb : 0 < b)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hs : 0 ≤ s)
    (hc : ∀ n : ℤ, ‖c n‖ ≤ M*Real.exp (-b*|(n : ℝ)|^σ)) :
    Memℓp (fun n : ℤ => (((1+|(n : ℝ)|)^s*Real.exp ((b/2)*|(n : ℝ)|^σ) : ℝ) : ℂ)*c n) p := by
  let v := NLS.SpectralWeight.gevrey s (b/2) σ hs (by positivity) hσ.le hσ1
  let w := NLS.SpectralWeight.stretchedExponential (3*b/4) σ (by positivity) hσ.le hσ1
  have hlim : Tendsto (fun x : ℝ => (1+x)^s/Real.exp ((b/4)*x^σ)) atTop (𝓝 0) := by
    simpa only [zero_mul,Real.exp_zero,mul_one] using
      NLS.SpectralWeight.polynomial_exp_ratio_tendsto_zero (fun _ : ℝ => 0) (fun x : ℝ => x^σ)
        s 0 (b/4) (by positivity) (_root_.tendsto_rpow_atTop hσ)
        (NLS.SpectralWeight.log_one_add_div_rpow_tendsto_zero σ hσ) (by simp)
  have hseq : Tendsto (fun n : ℕ => v n/w n) atTop (𝓝 0) := by
    apply (hlim.comp (tendsto_natCast_atTop_atTop (R := ℝ))).congr
    intro n
    dsimp [v,w]
    simp only [NLS.SpectralWeight.gevrey_apply,Int.cast_natCast,Nat.abs_cast]
    rw [mul_div_assoc,← Real.exp_sub,
      show b/2*(n : ℝ)^σ-3*b/4*(n : ℝ)^σ = -(b/4*(n : ℝ)^σ) by ring,Real.exp_neg]
    ring
  obtain ⟨K,hK,hbound⟩ := NLS.SpectralWeight.le_mul_of_ratio_tendsto_zero v w hseq
  have hnorm (n : ℤ) : ‖((v n : ℝ) : ℂ)*c n‖ ≤ K*M*Real.exp (-(b/4)*|(n : ℝ)|^σ) := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (v.positive n)]
    calc
      v n*‖c n‖ ≤ (K*w n)*(M*Real.exp (-b*|(n : ℝ)|^σ)) :=
        mul_le_mul (hbound n) (hc n) (norm_nonneg _) (mul_pos hK (w.positive n)).le
      _ = _ := by
        dsimp [w]
        rw [show -(b/4)*|(n : ℝ)|^σ = 3*b/4*|(n : ℝ)|^σ + -b*|(n : ℝ)|^σ by ring,Real.exp_add]
        ring
  have hsum := ((summable_stretched_exponential (b/4) σ (by positivity) hσ hσ1).mul_left (K*M)).of_nonneg_of_le
    (fun n => norm_nonneg (((v n : ℝ) : ℂ)*c n)) hnorm
  have hmem : Memℓp (fun n : ℤ => ((v n : ℝ) : ℂ)*c n) 1 :=
    (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr
      (by simpa only [ENNReal.toReal_one,Real.rpow_one] using hsum)
  simpa only [v,NLS.SpectralWeight.gevrey_apply] using hmem.of_exponent_ge (Fact.out : (1 : ℝ≥0∞) ≤ p)

/-- For continuous periodic physical functions, the union over positive
Fourier radii is exactly the classical Gevrey class of order 1/sigma.
A fixed radius implies a derivative bound; the converse chooses a smaller
positive radius and retains any prescribed polynomial Sobolev factor. -/
theorem physical_gevrey_iff (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (s σ : ℝ) (hs : 0 ≤ s) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (∃ a : ℝ, 0 < a ∧ Memℓp (fun n : ℤ =>
      (((1+|(n : ℝ)|)^s*Real.exp (a*|(n : ℝ)|^σ) : ℝ) : ℂ)*periodOneCoefficient f n) 2) ↔
    ContDiff ℝ ∞ f ∧ ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ k : ℕ, ∀ x : ℝ,
      ‖iteratedDeriv k f x‖ ≤ C*R^k*(k.factorial : ℝ)^(1/σ) := by
  constructor
  · rintro ⟨a,ha,hm⟩
    let c : NLS.WeightedCoeff (NLS.SpectralWeight.gevrey s a σ hs ha.le hσ.le hσ1).toWeight 2 :=
      ⟨periodOneCoefficient f,by
        change Memℓp (fun n : ℤ => (((NLS.SpectralWeight.gevrey s a σ hs ha.le hσ.le hσ1) n : ℝ) : ℂ)*periodOneCoefficient f n) 2
        simpa only [NLS.SpectralWeight.gevrey_apply] using hm⟩
    obtain ⟨g,hg,hgp,hgc,hgb⟩ := weighted_gevrey_synthesis s a σ hs ha hσ hσ1 c
    have he : g = f := eq_of_periodOneCoefficient_eq g f hg.continuous hf hgp hp hgc
    exact he ▸ ⟨hg,hgb⟩
  · rintro ⟨hfd,C,R,hC,hR,hbound⟩
    obtain ⟨b,hb,hdecay⟩ := gevrey_coefficients_decay f hfd hp C R σ hC hR hσ hbound
    exact ⟨b/2,by positivity,memlp_gevrey_of_decay (p := 2) _ (2*C) b σ s (by positivity) hb hσ hσ1 hs hdecay⟩

/-- Evaluating the source weight at the even Fourier index changes the
positive radius and a fixed polynomial factor, not the Gevrey class. -/
theorem gevrey_even_frequency_radius_iff (c : ℤ → ℂ) (s σ : ℝ)
    (hs : 0 ≤ s) (hσ : 0 < σ) :
    (∃ a : ℝ, 0 < a ∧ Memℓp (fun n : ℤ =>
      (((1+|((2*n : ℤ) : ℝ)|)^s*Real.exp (a*|((2*n : ℤ) : ℝ)|^σ) : ℝ) : ℂ)*c n) 2) ↔
    (∃ a : ℝ, 0 < a ∧ Memℓp (fun n : ℤ =>
      (((1+|(n : ℝ)|)^s*Real.exp (a*|(n : ℝ)|^σ) : ℝ) : ℂ)*c n) 2) := by
  constructor
  · rintro ⟨a,ha,hm⟩
    refine ⟨a,ha,hm.mono' ?_⟩
    intro n
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1+|(n : ℝ)|) s),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1+|((2*n : ℤ) : ℝ)|) s),
      abs_of_pos (Real.exp_pos (a*|(n : ℝ)|^σ)),
      abs_of_pos (Real.exp_pos (a*|((2*n : ℤ) : ℝ)|^σ))]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have ht : |(n : ℝ)| ≤ |((2*n : ℤ) : ℝ)| := by
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [abs_nonneg (n : ℝ)]
    apply mul_le_mul (Real.rpow_le_rpow (by positivity) (by linarith) hs)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) ht hσ.le) ha.le))
      (Real.exp_pos _).le (by positivity)
  · rintro ⟨a,ha,hm⟩
    let b := a/(2 : ℝ)^σ
    have hb : 0 < b := div_pos ha (Real.rpow_pos_of_pos (by norm_num) _)
    refine ⟨b,hb,(hm.const_mul (((2 : ℝ)^s : ℝ) : ℂ)).mono' ?_⟩
    intro n
    have hpoly : (1+|((2*n : ℤ) : ℝ)|)^s ≤ (2 : ℝ)^s*(1+|(n : ℝ)|)^s := by
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ 1+|(n : ℝ)|)]
      apply Real.rpow_le_rpow (by positivity) (by linarith) hs
    have he : b*|((2*n : ℤ) : ℝ)|^σ = a*|(n : ℝ)|^σ := by
      simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)]
      dsimp [b]
      field_simp
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,he,
      abs_of_pos (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1+|(n : ℝ)|) s),
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1+|((2*n : ℤ) : ℝ)|) s),
      abs_of_pos (Real.exp_pos (a*|(n : ℝ)|^σ))]
    have hh := mul_le_mul_of_nonneg_right hpoly (mul_nonneg (Real.exp_pos (a*|(n : ℝ)|^σ)).le (norm_nonneg (c n)))
    nlinarith

/-- The paper's exact even-frequency source convention has the same
classical Gevrey characterization, including the physical 2pi derivative. -/
theorem paper_physical_gevrey_iff (f : ℝ → ℂ) (hf : Continuous f) (hp : Function.Periodic f 1)
    (s σ : ℝ) (hs : 0 ≤ s) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    (∃ a : ℝ, 0 < a ∧ Memℓp (fun n : ℤ =>
      (((1+|((2*n : ℤ) : ℝ)|)^s*Real.exp (a*|((2*n : ℤ) : ℝ)|^σ) : ℝ) : ℂ)*periodOneCoefficient f n) 2) ↔
    ContDiff ℝ ∞ f ∧ ∃ C R : ℝ, 0 ≤ C ∧ 0 < R ∧ ∀ k : ℕ, ∀ x : ℝ,
      ‖iteratedDeriv k f x‖ ≤ C*R^k*(k.factorial : ℝ)^(1/σ) := by
  rw [gevrey_even_frequency_radius_iff _ s σ hs hσ]
  exact physical_gevrey_iff f hf hp s σ hs hσ hσ1

end NLS.Articles.DNLSEstimates
