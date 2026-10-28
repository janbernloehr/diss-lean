import NLS.ZakharovShabat.OffDiagonalSeries
import NLS.ZakharovShabat.SingleResonantPotential

/-! # Exact cubic terms for a two-mode resonant potential

For physical modes 0 and n, only the target index n has a cubic coefficient
in the outer tail. Its full-strip supremum is attained at the left real
boundary. These are exact operator terms, not full spectral-gap asymptotics.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A two-mode background; the resonant leading perturbation is still separate. -/
def twoModeResonantPotential (w : SpectralWeight) (n : ℤ) (s : ℂ) : WeightedCoeffPair w.toWeight p :=
  (WeightedCoeffPair.toMax w.toWeight p).symm
    (weightedMode w.toWeight 0 s + weightedMode w.toWeight (-n) s,
     weightedMode w.toWeight 0 s + weightedMode w.toWeight n s)

/-- The first physical component has modes 0 and -n. -/
theorem twoModeResonantPotential_fst (w : SpectralWeight) (n : ℤ) (hn : 0 < n) (s : ℂ) (k : ℤ) :
    (twoModeResonantPotential (p := p) w n s).fst.val k = if k = 0 ∨ k = -n then s else 0 := by
  change (weightedMode w.toWeight 0 s + weightedMode w.toWeight (-n) s).val k = _
  rw [WeightedCoeff.add_val,weightedMode_apply,weightedMode_apply]
  split_ifs <;> simp_all

/-- The second physical component has modes 0 and n. -/
theorem twoModeResonantPotential_snd (w : SpectralWeight) (n : ℤ) (hn : 0 < n) (s : ℂ) (k : ℤ) :
    (twoModeResonantPotential (p := p) w n s).snd.val k = if k = 0 ∨ k = n then s else 0 := by
  change (weightedMode w.toWeight 0 s + weightedMode w.toWeight n s).val k = _
  rw [WeightedCoeff.add_val,weightedMode_apply,weightedMode_apply]
  split_ifs <;> simp_all

/-- The only cubic background path beyond the cutoff is the target mode. -/
theorem resonantCubic_path (n m l k : ℤ) (hn : 0 < n) (hm : n ≤ |m|)
    (ha : m-l = 0 ∨ m-l = n) (hb : l-k = 0 ∨ l-k = -n)
    (hc : k+m = 0 ∨ k+m = n) : m = n ∧ l = 0 ∧ k = 0 := by
  rcases le_abs.mp hm with hm | hm <;> rcases ha with ha | ha <;>
    rcases hb with hb | hb <;> rcases hc with hc | hc <;> omega

/-- Exact first cubic term of the actual positive parity series on every tail strip. -/
theorem twoModeResonantPotential_cubic_positive (hp : p ≠ ⊤) (w : SpectralWeight)
    (n m : ℤ) (hn : 0 < n) (hm : n ≤ |m|) (s z : ℂ) (hz : z ∈ resonantStrip m) :
    let φ := twoModeResonantPotential (p := p) w n s
    (weightedPotentialInverse hp w φ m z hz
      (weightedPotentialInverse hp w φ m z hz (weightedResonantSource hp w φ m 0))).snd.val m =
      if m = n then s^3/z^2 else 0 := by
  dsimp only
  rw [weightedPotentialInverse_sq_snd_apply]
  simp only [weightedResonantSource_zero_snd,twoModeResonantPotential_fst w n hn,twoModeResonantPotential_snd w n hn]
  have he (l k : ℤ) :
      (if m-l = 0 ∨ m-l = n then s else 0) *
      (if l-k = 0 ∨ l-k = -n then s else 0) *
      complementarySymbol m z (-l) * complementarySymbol m z k *
      (if k+m = 0 ∨ k+m = n then s else 0) =
        if m = n ∧ l = 0 ∧ k = 0 then s^3/z^2 else 0 := by
    by_cases ha : m-l = 0 ∨ m-l = n
    · by_cases hb : l-k = 0 ∨ l-k = -n
      · by_cases hc : k+m = 0 ∨ k+m = n
        · obtain ⟨h1,h2,h3⟩ := resonantCubic_path n m l k hn hm ha hb hc
          subst m l k
          simp [complementarySymbol,ne_of_gt hn,Ne.symm (ne_of_gt hn)]
          ring
        · have hbad : ¬(m=n ∧ l=0 ∧ k=0) := by rintro ⟨rfl,rfl,rfl⟩; simp at hc
          simp [hc,hbad]
      · have hbad : ¬(m=n ∧ l=0 ∧ k=0) := by rintro ⟨rfl,rfl,rfl⟩; simp at hb
        simp [hb,hbad]
    · have hbad : ¬(m=n ∧ l=0 ∧ k=0) := by rintro ⟨rfl,rfl,rfl⟩; simp at ha
      simp [ha,hbad]
  simp only [he]
  by_cases hmn : m=n
  · simp only [hmn]
    rw [tsum_eq_single 0]
    · simp
    · intro l hl
      simp [hl]
  · simp only [hmn]
    rw [tsum_eq_single 0]
    · simp
    · intro l hl
      simp [hl]

/-- The reflected cubic path has the same unique tail index. -/
theorem resonantCubic_path_negative (n m l k : ℤ) (hn : 0 < n) (hm : n ≤ |m|)
    (ha : -m-l = 0 ∨ -m-l = -n) (hb : l-k = 0 ∨ l-k = n)
    (hc : k-m = 0 ∨ k-m = -n) : m = n ∧ l = 0 ∧ k = 0 := by
  rcases le_abs.mp hm with hm | hm <;> rcases ha with ha | ha <;>
    rcases hb with hb | hb <;> rcases hc with hc | hc <;> omega

/-- Exact first cubic term of the actual negative parity series on every tail strip. -/
theorem twoModeResonantPotential_cubic_negative (hp : p ≠ ⊤) (w : SpectralWeight)
    (n m : ℤ) (hn : 0 < n) (hm : n ≤ |m|) (s z : ℂ) (hz : z ∈ resonantStrip m) :
    let φ := twoModeResonantPotential (p := p) w n s
    (weightedPotentialInverse hp w φ m z hz
      (weightedPotentialInverse hp w φ m z hz (weightedResonantSource hp w φ m 1))).fst.val (-m) =
      if m = n then s^3/z^2 else 0 := by
  dsimp only
  rw [weightedPotentialInverse_sq_fst_apply]
  simp only [weightedResonantSource_one_fst,twoModeResonantPotential_fst w n hn,twoModeResonantPotential_snd w n hn]
  have he (l k : ℤ) :
      (if -m-l = 0 ∨ -m-l = -n then s else 0) *
      (if l-k = 0 ∨ l-k = n then s else 0) *
      complementarySymbol m z l * complementarySymbol m z (-k) *
      (if k-m = 0 ∨ k-m = -n then s else 0) =
        if m = n ∧ l = 0 ∧ k = 0 then s^3/z^2 else 0 := by
    by_cases ha : -m-l = 0 ∨ -m-l = -n
    · by_cases hb : l-k = 0 ∨ l-k = n
      · by_cases hc : k-m = 0 ∨ k-m = -n
        · obtain ⟨h1,h2,h3⟩ := resonantCubic_path_negative n m l k hn hm ha hb hc
          subst m l k
          simp [complementarySymbol,ne_of_gt hn,Ne.symm (ne_of_gt hn)]
          ring
        · have hbad : ¬(m=n ∧ l=0 ∧ k=0) := by rintro ⟨rfl,rfl,rfl⟩; simp at hc
          simp [hc,hbad]
      · have hbad : ¬(m=n ∧ l=0 ∧ k=0) := by rintro ⟨rfl,rfl,rfl⟩; simp at hb
        simp [hb,hbad]
    · have hbad : ¬(m=n ∧ l=0 ∧ k=0) := by rintro ⟨rfl,rfl,rfl⟩; simp at ha
      simp [ha,hbad]
  simp only [he]
  by_cases hmn : m=n
  · simp only [hmn]
    rw [tsum_eq_single 0]
    · simp
    · intro l hl
      simp [hl]
  · simp only [hmn]
    rw [tsum_eq_single 0]
    · simp
    · intro l hl
      simp [hl]

/-- This is the full-strip supremum, not a maximum over numerical samples. -/
theorem resonantCubic_strip_isGreatest (n : ℤ) (hn : 0 < n) (s : ℂ) :
    IsGreatest ((fun z : ℂ => ‖s^3/z^2‖) '' resonantStrip n)
      (‖s‖^3/(Real.pi*((n : ℝ)-1/2))^2) := by
  let d : ℝ := Real.pi*((n : ℝ)-1/2)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < d := mul_pos Real.pi_pos (by linarith)
  have hpoint : (d : ℂ) ∈ resonantStrip n := by
    change |d-Real.pi*(n : ℝ)| ≤ Real.pi/2
    have he : d-Real.pi*(n : ℝ) = -(Real.pi/2) := by dsimp [d]; ring
    rw [he,abs_neg,abs_of_pos (by positivity : 0 < Real.pi/2)]
  refine ⟨⟨(d : ℂ),hpoint,?_⟩,?_⟩
  · simp only [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg hd.le]
    rfl
  · rintro _ ⟨z,hz,rfl⟩
    have hlow : d ≤ z.re := by
      change |z.re-Real.pi*(n : ℝ)| ≤ Real.pi/2 at hz
      have hb := (abs_le.mp hz).1
      dsimp [d]
      linarith
    have hnorm : d ≤ ‖z‖ := hlow.trans ((le_abs_self _).trans (Complex.abs_re_le_norm z))
    change ‖s^3/z^2‖ ≤ ‖s‖^3/d^2
    rw [norm_div,norm_pow,norm_pow]
    apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hd)
    exact pow_le_pow_left₀ hd.le hnorm 2

/-- The exact supremum on the whole closed unbounded strip. -/
theorem resonantCubic_strip_sup (n : ℤ) (hn : 0 < n) (s : ℂ) :
    sSup ((fun z : ℂ => ‖s^3/z^2‖) '' resonantStrip n) =
      ‖s‖^3/(Real.pi*((n : ℝ)-1/2))^2 :=
  (resonantCubic_strip_isGreatest n hn s).csSup_eq

/-- The scalar strict comparison holds beyond every proposed cutoff. Actual spectral and infinite-sum limits are still required for a counterexample. -/
theorem resonantCubic_limit_ratio_lt (n : ℤ) (hn : 3 ≤ n) :
    2+2*((n : ℝ)/((n : ℝ)-1/2))^8 < 16 := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ)-1/2 := by linarith
  have hratio : (n : ℝ)/((n : ℝ)-1/2) ≤ 6/5 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hnon : 0 ≤ (n : ℝ)/((n : ℝ)-1/2) := div_nonneg (by linarith) hd.le
  have hpower := pow_le_pow_left₀ hnon hratio 8
  norm_num at hpower
  linarith

end NLS.ZakharovShabat
