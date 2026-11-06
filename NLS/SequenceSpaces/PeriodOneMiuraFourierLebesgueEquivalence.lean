import NLS.SequenceSpaces.FourierLebesgueHilbertEmbedding
import NLS.SequenceSpaces.PeriodOneMiuraFourierLebesgueAlgebra

/-! # Exact Fourier-Lebesgue regularity of every actual L2 Miura lift

For every finite p>=2 and s>=-1/2, the actual shifted equation has
q in FL^(s,p) exactly when u is in FL^(s+1,p). The strict Hilbert
embedding retains a positive 1/(2p) margin, including at s=-1/2.
-/
noncomputable section
set_option autoImplicit false
open Complex
open scoped ENNReal
namespace NLS

theorem periodOneMiuraProduct_mem_sobolev_of_margin
    (s p : ℝ) (hs : -1/2≤s) (hp : 0<p) (u : Coeff 2)
    (hu : Memℓp (fun n => (Weight.sobolev (s+1/2+1/(2*p)) n : ℂ)*u n) 2) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*(periodOneMiuraProduct u u).val n) 2 := by
  have hδ : 0<1/(2*p) := by positivity
  have ht : 0≤s+1/2+1/(2*p) := by linarith
  have hd : 1/2<1/2+1/(2*p) := by linarith
  have h := periodOneMiuraProduct_mem_sobolev_sub (s+1/2+1/(2*p)) ht
    (1/2+1/(2*p)) hd u u hu hu
  simpa only [show s+1/2+1/(2*p)-(1/2+1/(2*p))=s by ring] using h

theorem periodOneMiura_fourierLebesgue_iff_of_two_lt
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) (ENNReal.ofReal p) ↔
      Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) (ENNReal.ofReal p) := by
  have hppos : 0<p := by linarith
  have hδ : 0<1/(2*p) := by positivity
  have hpe : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  constructor
  · intro hq
    have hqH := WeightedCoeff.memlp_hilbert_of_fourierLebesgue s p hp hq
    have hσ : -1≤s-1/2+1/(2*p) := by linarith
    have huH := periodOneMiura_lift_mem_sobolev_of_image q u c himage
      (s-1/2+1/(2*p)) hσ hqH
    have huT : Memℓp (fun n => (Weight.sobolev (s+1/2+1/(2*p)) n : ℂ)*u n) 2 := by
      simpa only [show s-1/2+1/(2*p)+1=s+1/2+1/(2*p) by ring] using huH
    have hprod := periodOneMiuraProduct_mem_sobolev_of_margin s p hs hppos u huT
    have huS := memlp_sobolev_of_le (by linarith : s≤s+1/2+1/(2*p)) huT
    exact periodOneMiura_lift_mem_of_weighted_image_and_product (ENNReal.ofReal p) q u c himage s
      hq (hprod.of_exponent_ge hpe) (huS.of_exponent_ge hpe)
  · intro hu
    let : Fact (1≤ENNReal.ofReal p) := ⟨by
      exact_mod_cast ENNReal.ofReal_le_ofReal (show (1:ℝ)≤p by linarith)⟩
    have huH := WeightedCoeff.memlp_hilbert_of_fourierLebesgue (s+1) p hp hu
    have huT : Memℓp (fun n => (Weight.sobolev (s+1/2+1/(2*p)) n : ℂ)*u n) 2 := by
      simpa only [show s+1-1/2+1/(2*p)=s+1/2+1/(2*p) by ring] using huH
    have hprod := periodOneMiuraProduct_mem_sobolev_of_margin s p hs hppos u huT
    exact periodOneMiura_image_mem_of_weighted_lift_and_product (ENNReal.ofReal p) q u c himage s
      hu (hprod.of_exponent_ge hpe)

/-- EVERY actual L2 shifted lift has the exact Fourier-Lebesgue
regularity shift, including p=2 and the endpoint s=-1/2. -/
theorem periodOneMiura_fourierLebesgue_iff
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s p : ℝ) (hs : -1/2≤s) (hp : 2≤p) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) (ENNReal.ofReal p) ↔
      Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) (ENNReal.ofReal p) := by
  rcases eq_or_lt_of_le hp with he | he
  · subst p
    have hp2 : ENNReal.ofReal (2 : ℝ)=(2 : ℝ≥0∞) := by norm_num
    rw [hp2]
    exact periodOneMiura_sobolev_iff q u c himage s (by linarith)
  · exact periodOneMiura_fourierLebesgue_iff_of_two_lt q u c himage s p hs he

theorem periodOneMiura_fourierLebesgue_iff_finite_exponent
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (himage : periodOneMiura u=q+periodOneL2Inclusion (lp.single 2 0 c))
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : 2≤p) (hpt : p≠⊤) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*q.val n) p ↔
      Memℓp (fun n => (Weight.sobolev (s+1) n : ℂ)*u n) p := by
  have hpr : 2≤p.toReal := by
    simpa only [ENNReal.toReal_ofNat] using (ENNReal.toReal_le_toReal (by norm_num) hpt).mpr hp
  have h := periodOneMiura_fourierLebesgue_iff q u c himage s p.toReal hs hpr
  simpa only [ENNReal.ofReal_toReal hpt] using h

end NLS
