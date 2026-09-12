import NLS.Fourier.SobolevIdentification

/-!
# Classical Sobolev reflection across the half period

The reflected derivative has the opposite sign. A matching value at the join
makes the folded function an integral primitive, hence absolutely continuous.
Only classical Sobolev regularity on the original interval is assumed.
-/

noncomputable section
open MeasureTheory Set
namespace NLS.Fourier

/-- Classical `H¹` regularity on the original interval, with no periodic endpoint condition. -/
def HasIntervalH1Regularity (f : ℝ → ℂ) : Prop :=
  AbsolutelyContinuousOnInterval f 0 1 ∧
    MemLp (deriv f) 2 (volume.restrict (Ioc 0 1))

private theorem intervalIntegrable_ite_halves {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 1 2) :
    IntervalIntegrable (fun x => if x ≤ 1 then f x else g x) volume 0 2 := by
  have h01 : IntervalIntegrable (fun x => if x ≤ 1 then f x else g x) volume 0 1 :=
    hf.congr (fun x hx => by
      have hx' : x ≤ 1 := (show x ∈ Ioc (0 : ℝ) 1 from by simpa using hx).2
      simp [hx'])
  have h12 : IntervalIntegrable (fun x => if x ≤ 1 then f x else g x) volume 1 2 :=
    hg.congr (fun x hx => by
      have hx' : 1 < x := (show x ∈ Ioc (1 : ℝ) 2 from by simpa using hx).1
      simp [not_le.mpr hx'])
  exact h01.trans h12

/-- Integrable half-interval data remain integrable after reflection, even with a jump. -/
theorem intervalIntegrable_folded (ε : ℂ) {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) :
    IntervalIntegrable (folded ε f g) volume 0 2 := by
  have hg' : IntervalIntegrable (fun x => g (2 - x)) volume 1 2 := by
    simpa only [sub_zero, show (2 : ℝ) - 1 = 1 by norm_num] using (hg.comp_sub_left 2).symm
  exact intervalIntegrable_ite_halves hf (hg'.const_mul ε)

/-- The folded map preserves physical square integrability for arbitrary `L²` inputs. -/
theorem memLp_folded_of_memLp (ε : ℂ) {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 1))) :
    MemLp (folded ε f g) 2 (volume.restrict (Ioc 0 2)) := by
  have hfi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hf.integrable (by norm_num))
  have hgi : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hg.integrable (by norm_num))
  have hi := intervalIntegrable_folded ε hfi hgi
  have hmeas := ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hi).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hmeas).mpr
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
  have hfs : IntervalIntegrable (fun x => ‖f x‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
  have hgs : IntervalIntegrable (fun x => ‖g x‖ ^ 2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg)
  have hgr : IntervalIntegrable (fun x => ‖ε * g (2 - x)‖ ^ 2) volume 1 2 := by
    have ht : IntervalIntegrable (fun x => ‖g (2 - x)‖ ^ 2) volume 1 2 := by
      simpa only [sub_zero, show (2 : ℝ) - 1 = 1 by norm_num] using (hgs.comp_sub_left 2).symm
    simpa only [norm_mul, mul_pow] using ht.const_mul (‖ε‖ ^ 2)
  convert intervalIntegrable_ite_halves hfs hgr using 1
  funext x
  simp only [folded]
  split_ifs <;> rfl

private theorem integral_folded_left (ε : ℂ) (f g : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..x, folded ε f g t) = ∫ t in (0 : ℝ)..x, f t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ≤ 1 := le_trans ((uIcc_of_le hx.1 ▸ ht).2) hx.2
  simp [folded, ht']

private theorem integral_folded_right (ε : ℂ) (f g : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Icc (1 : ℝ) 2) :
    (∫ t in (1 : ℝ)..x, folded ε f g t) = ε * ∫ t in (2 - x)..1, g t := by
  have he : (∫ t in (1 : ℝ)..x, folded ε f g t) =
      ∫ t in (1 : ℝ)..x, ε * g (2 - t) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : 1 < t := (show t ∈ Ioc (1 : ℝ) x from by simpa [uIoc_of_le hx.1] using ht).1
    simp [folded, not_le.mpr ht']
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left]
  norm_num

/-- The half-coefficient formula only needs integrability on the original interval. -/
theorem periodTwoCoefficient_folded_of_intervalIntegrable (ε : ℂ) {f g : ℝ → ℂ}
    (hf : IntervalIntegrable f volume 0 1) (hg : IntervalIntegrable g volume 0 1) (n : ℤ) :
    periodTwoCoefficient (folded ε f g) n = halfCoefficient f n + ε * halfCoefficient g (-n) := by
  let F := fun x => f x * wave (-n) x
  let G := fun x => g x * wave n x
  have hF : IntervalIntegrable F volume 0 1 := hf.mul_continuousOn (continuous_wave (-n)).continuousOn
  have hG : IntervalIntegrable G volume 0 1 := hg.mul_continuousOn (continuous_wave n).continuousOn
  have he : (fun x => folded ε f g x * wave (-n) x) = folded ε F G := by
    funext x
    dsimp only [folded, F, G]
    split_ifs
    · rfl
    · rw [wave_reflect]
      ring
  have hi := intervalIntegrable_folded ε hF hG
  have hs01 : uIcc (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 2 := uIcc_subset_uIcc (by simp) (by norm_num)
  have hs12 : uIcc (1 : ℝ) 2 ⊆ uIcc (0 : ℝ) 2 := uIcc_subset_uIcc (by norm_num) (by simp)
  unfold periodTwoCoefficient halfCoefficient
  rw [he, ← intervalIntegral.integral_add_adjacent_intervals (hi.mono_set hs01) (hi.mono_set hs12),
    integral_folded_left ε F G (by norm_num), integral_folded_right ε F G (by norm_num)]
  norm_num only [sub_self, neg_neg]
  dsimp only [F, G]
  ring

/-- Matching at the join cancels the boundary term in the integral of the reflected derivative. -/
theorem folded_eq_add_integral_derivative (ε : ℂ) {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (hjoin : f 1 = ε * g 1) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    folded ε f g x = f 0 + ∫ t in (0 : ℝ)..x, folded (-ε) (deriv f) (deriv g) t := by
  have hfi : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (hf.2.integrable (by norm_num))
  have hgi : IntervalIntegrable (deriv g) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      (hg.2.integrable (by norm_num))
  by_cases hx1 : x ≤ 1
  · have hsub : uIcc (0 : ℝ) x ⊆ uIcc (0 : ℝ) 1 :=
      uIcc_subset_uIcc (by simp) (by simpa using (⟨hx.1, hx1⟩ : x ∈ Icc (0 : ℝ) 1))
    rw [integral_folded_left (-ε) _ _ ⟨hx.1, hx1⟩,
      FunctionalAnalysis.integral_deriv_eq_sub_complex (hf.1.mono hsub) (hfi.mono_set hsub)]
    simp [folded, hx1]
  · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
    have hi := intervalIntegrable_folded (-ε) hfi hgi
    have hs01 : uIcc (0 : ℝ) 1 ⊆ uIcc (0 : ℝ) 2 := uIcc_subset_uIcc (by simp) (by norm_num)
    have hs1x : uIcc (1 : ℝ) x ⊆ uIcc (0 : ℝ) 2 :=
      uIcc_subset_uIcc (by norm_num) (by simpa using hx)
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi.mono_set hs01) (hi.mono_set hs1x),
      integral_folded_left (-ε) _ _ (by norm_num), integral_folded_right (-ε) _ _ ⟨hx1', hx.2⟩,
      FunctionalAnalysis.integral_deriv_eq_sub_complex hf.1 hfi]
    have hs : uIcc (2 - x) 1 ⊆ uIcc (0 : ℝ) 1 :=
      uIcc_subset_uIcc (by simp only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), mem_Icc]; constructor <;> linarith [hx.2]) (by simp)
    rw [FunctionalAnalysis.integral_deriv_eq_sub_complex (hg.1.mono hs) (hgi.mono_set hs), hjoin]
    simp only [folded, if_neg hx1]
    ring

/-- A matching join makes the reflected Sobolev function absolutely continuous. -/
theorem absolutelyContinuous_folded (ε : ℂ) {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (hjoin : f 1 = ε * g 1) : AbsolutelyContinuousOnInterval (folded ε f g) 0 2 := by
  have hi : IntervalIntegrable (folded (-ε) (deriv f) (deriv g)) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_folded_of_memLp (-ε) hf.2 hg.2).integrable (by norm_num))
  have ha := FunctionalAnalysis.absolutelyContinuousOnInterval_const_add
    (FunctionalAnalysis.absolutelyContinuousOnInterval_integral hi (c := 0) (by simp)) (f 0)
  apply FunctionalAnalysis.absolutelyContinuousOnInterval_congr ha
  intro x hx
  exact (folded_eq_add_integral_derivative ε hf hg hjoin (by simpa using hx)).symm

/-- The derivative of the fold has the reflected sign almost everywhere. -/
theorem deriv_folded_ae (ε : ℂ) {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (hjoin : f 1 = ε * g 1) :
    deriv (folded ε f g) =ᵐ[volume.restrict (Ioc 0 2)] folded (-ε) (deriv f) (deriv g) := by
  have hi : IntervalIntegrable (folded (-ε) (deriv f) (deriv g)) volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_folded_of_memLp (-ε) hf.2 hg.2).integrable (by norm_num))
  change ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 2),
    deriv (folded ε f g) x = folded (-ε) (deriv f) (deriv g) x
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hi.ae_hasDerivAt_integral,
    (show ∀ᵐ x : ℝ, x ≠ (2 : ℝ) from by simp [ae_iff, measure_singleton])] with x hx hx2
  intro hxi
  have hxi' : x ∈ Ioo (0 : ℝ) 2 := ⟨hxi.1, lt_of_le_of_ne hxi.2 hx2⟩
  have h := (hx (by simpa using (⟨hxi.1.le, hxi.2⟩ : x ∈ Icc (0 : ℝ) 2))
    0 (by simp)).const_add (f 0)
  apply HasDerivAt.deriv
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hxi'.1 hxi'.2] with y hy
  exact folded_eq_add_integral_derivative ε hf hg hjoin ⟨hy.1.le, hy.2.le⟩

/-- The actual derivative of the joined function is square integrable. -/
theorem memLp_deriv_folded (ε : ℂ) {f g : ℝ → ℂ}
    (hf : HasIntervalH1Regularity f) (hg : HasIntervalH1Regularity g)
    (hjoin : f 1 = ε * g 1) :
    MemLp (deriv (folded ε f g)) 2 (volume.restrict (Ioc 0 2)) :=
  (memLp_congr_ae (deriv_folded_ae ε hf hg hjoin)).mpr
    (memLp_folded_of_memLp (-ε) hf.2 hg.2)

end NLS.Fourier
