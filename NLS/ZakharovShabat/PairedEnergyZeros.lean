import NLS.ZakharovShabat.PairedEnergyProduct

/-! # Exact simple zeros after descent from frequency to energy -/
noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.ZakharovShabat
variable {p : ENNReal} [Fact (1 ≤ p)]
variable (hp : p ≠ ⊤) (hp1 : 1 < p) (rho : ℤ → ℂ)
variable (hlp : Memℓp (fun j => rho j-(Real.pi : ℂ)*j) p)
variable (hzero : rho 0 = 0) (hneg : ∀ k : ℕ+, rho (-(k : ℤ)) = -rho (k : ℤ))
variable (hinj : Function.Injective rho)

include hp hp1 hlp hzero hinj in
theorem pairedEnergyProduct_zero_ne_zero : pairedEnergyProduct rho 0 ≠ 0 := by
  have hz : entireSingleSpectralProduct rho 0 = 0 :=
    (entireSingleSpectralProduct_eq_zero_iff_of_lp hp rho hlp 0).mpr ⟨0,hzero⟩
  have hd := entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 rho hlp hinj 0 hz
  simpa only [pairedEnergyProduct,oddSquareDescent,Complex.sqrt_zero,dslope_same,
    ne_eq,div_eq_zero_iff,or_false,OfNat.ofNat_ne_zero] using hd

include hp hp1 hlp hzero hneg hinj in
theorem pairedEnergyProduct_eq_zero_iff (lambda : ℂ) :
    pairedEnergyProduct rho lambda = 0 ↔ ∃ k : ℕ+, (rho (k : ℤ))^2 = lambda := by
  have hG0 := pairedEnergyProduct_zero_ne_zero hp hp1 rho hlp hzero hinj
  constructor
  · intro hG
    have hlam : lambda ≠ 0 := by intro he; subst lambda; exact hG0 hG
    let z := Complex.sqrt lambda
    have hzsq : z^2 = lambda := sq_sqrt lambda
    have hE : entireSingleSpectralProduct rho z = 0 := by
      rw [← pairedEnergyProduct_factor hp rho hlp hzero hneg z,hzsq,hG,mul_zero]
    obtain ⟨j,hj⟩ := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp rho hlp z).mp hE
    have hj0 : j ≠ 0 := by intro he; subst j; rw [hzero] at hj; apply hlam; rw [← hzsq,← hj]; norm_num
    by_cases hjpos : 0 < j
    · let k : ℕ+ := ⟨j.toNat,by omega⟩
      have hk : (k : ℤ) = j := by change (j.toNat : ℤ) = j; omega
      exact ⟨k,by rw [hk,hj,hzsq]⟩
    · let k : ℕ+ := ⟨(-j).toNat,by omega⟩
      have hk : -(k : ℤ) = j := by change -((-j).toNat : ℤ) = j; omega
      have hn := hneg k
      rw [hk,hj] at hn
      refine ⟨k,?_⟩
      rw [hn,neg_sq] at hzsq
      exact hzsq
  · rintro ⟨k,hk⟩
    have hk0 : rho (k : ℤ) ≠ 0 := by
      intro he
      have h := hinj (he.trans hzero.symm)
      have hkpos : (0 : ℤ) < k := by exact_mod_cast k.pos
      omega
    have hE := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp rho hlp (rho (k : ℤ))).mpr ⟨k,rfl⟩
    rw [← pairedEnergyProduct_factor hp rho hlp hzero hneg,hk] at hE
    exact (mul_eq_zero.mp hE).resolve_left (mul_ne_zero (by norm_num) hk0)

include hneg hinj in
theorem pairedEnergyRoots_injective : Function.Injective (fun k : ℕ+ => (rho (k : ℤ))^2) := by
  intro k n he
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with h | h
  · have hi : (k : ℤ) = (n : ℤ) := hinj h
    exact_mod_cast hi
  · have hi := hinj (h.trans (hneg n).symm)
    have hk : (0 : ℤ) < k := by exact_mod_cast k.pos
    have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
    omega

include hp hp1 hlp hzero hneg hinj in
theorem pairedEnergyProduct_simple_zeros (lambda : ℂ) (hlam : pairedEnergyProduct rho lambda = 0) :
    deriv (pairedEnergyProduct rho) lambda ≠ 0 := by
  obtain ⟨k,hk⟩ := (pairedEnergyProduct_eq_zero_iff hp hp1 rho hlp hzero hneg hinj lambda).mp hlam
  let z := rho (k : ℤ)
  have hE := (entireSingleSpectralProduct_eq_zero_iff_of_lp hp rho hlp z).mpr ⟨k,rfl⟩
  have hsimple := entireSingleSpectralProduct_simple_zeros_of_injective hp hp1 rho hlp hinj z hE
  have hG := analyticOnNhd_pairedEnergyProduct hp rho hlp hzero hneg
  have hcomp : HasDerivAt (fun w : ℂ => pairedEnergyProduct rho (w^2))
      (deriv (pairedEnergyProduct rho) (z^2)*(2*z)) z := by
    simpa using!
      (hG (z^2) (mem_univ _)).differentiableAt.hasDerivAt.comp z ((hasDerivAt_id z).pow 2)
  have hprod : HasDerivAt (fun w : ℂ => (2*w)*pairedEnergyProduct rho (w^2))
      (2*pairedEnergyProduct rho (z^2)+(2*z)*(deriv (pairedEnergyProduct rho) (z^2)*(2*z))) z := by
    simpa using! ((hasDerivAt_id z).const_mul (2 : ℂ)).mul hcomp
  have he : (fun w : ℂ => (2*w)*pairedEnergyProduct rho (w^2)) = entireSingleSpectralProduct rho :=
    funext (pairedEnergyProduct_factor hp rho hlp hzero hneg)
  rw [he] at hprod
  have hder := hprod.deriv
  change z^2 = lambda at hk
  rw [hk,hlam,mul_zero,zero_add] at hder
  intro hbad
  rw [hbad,zero_mul,mul_zero] at hder
  exact hsimple hder

end NLS.ZakharovShabat
