import Mathlib

open Filter Set
open scoped Topology

namespace RootCollapse

private lemma sine_ratio_pos_lt_one
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (ht : t ∈ Ioc (0 : ℝ) (Real.pi / 2)) :
    0 < Real.sin (a * t) / Real.sin (b * t) ∧
      Real.sin (a * t) / Real.sin (b * t) < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht0 : 0 < t := ht.1
  have htpi : t ≤ Real.pi / 2 := ht.2
  have ha0 : 0 < a * t := mul_pos ha ht0
  have hb0 : 0 < b := lt_trans ha hab
  have hb0t : 0 < b * t := mul_pos hb0 ht0
  have hbt : b * t ≤ Real.pi / 2 := by
    calc
      b * t ≤ 1 * t := mul_le_mul_of_nonneg_right hb ht0.le
      _ = t := one_mul t
      _ ≤ Real.pi / 2 := htpi
  have hat_lt : a * t < b * t := mul_lt_mul_of_pos_right hab ht0
  have hat_mem : a * t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hat_lt.le.trans hbt⟩
  have hbt_mem : b * t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hbt⟩
  have hsin_lt : Real.sin (a * t) < Real.sin (b * t) :=
    Real.strictMonoOn_sin hat_mem hbt_mem hat_lt
  have hhalfpi : Real.pi / 2 < Real.pi := by linarith
  have hsin_a : 0 < Real.sin (a * t) :=
    Real.sin_pos_of_pos_of_lt_pi ha0 (hat_lt.trans (hbt.trans_lt hhalfpi))
  have hsin_b : 0 < Real.sin (b * t) :=
    Real.sin_pos_of_pos_of_lt_pi hb0t (hbt.trans_lt hhalfpi)
  exact ⟨div_pos hsin_a hsin_b, (div_lt_one hsin_b).2 hsin_lt⟩

/-- In the nonoscillatory regime `0 < a < b ≤ 1`, every sequence of positive
roots of `(sin (a t) / sin (b t))^n = tan(t)^2` converges to zero. -/
theorem roots_tend_to_zero
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b ≤ 1)
    (t : ℕ → ℝ)
    (ht : ∀ n, t n ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hroot : ∀ n,
      (Real.sin (a * t n) / Real.sin (b * t n)) ^ n = Real.tan (t n) ^ 2) :
    Tendsto t atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro c hc
    filter_upwards [] with n
    exact lt_trans hc (ht n).1
  · intro ε hε
    let δ : ℝ := min (ε / 2) (Real.pi / 4)
    have hδ0 : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos hε) (by positivity)
    have hδε : δ < ε := by
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
    have hδpi : δ ≤ Real.pi / 2 := by
      exact (min_le_right _ _).trans (by linarith [Real.pi_pos])

    let r : ℝ → ℝ := fun x => Real.sin (a * x) / Real.sin (b * x)
    have hr_cont : ContinuousOn r (Icc δ (Real.pi / 2)) := by
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro x hx
        have hbx0 : 0 < b * x := mul_pos (lt_trans ha hab) (lt_of_lt_of_le hδ0 hx.1)
        have hbxpi : b * x < Real.pi := by
          have : b * x ≤ Real.pi / 2 := by
            calc
              b * x ≤ 1 * x := mul_le_mul_of_nonneg_right hb (le_trans hδ0.le hx.1)
              _ = x := one_mul x
              _ ≤ Real.pi / 2 := hx.2
          linarith [Real.pi_pos]
        exact (Real.sin_pos_of_pos_of_lt_pi hbx0 hbxpi).ne'
    obtain ⟨s, hs, hsmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hδpi) hr_cont
    let M := r s
    have hM : 0 < M ∧ M < 1 := by
      exact sine_ratio_pos_lt_one ha hab hb ⟨lt_of_lt_of_le hδ0 hs.1, hs.2⟩
    have htanδ : 0 < Real.tan δ ^ 2 := by
      have hδhalf : δ < Real.pi / 2 := by
        calc
          δ ≤ Real.pi / 4 := min_le_right _ _
          _ < Real.pi / 2 := by linarith [Real.pi_pos]
      have htan : 0 < Real.tan δ := Real.tan_pos_of_pos_of_lt_pi_div_two
        hδ0 hδhalf
      positivity
    have hpow : Tendsto (fun n : ℕ => M ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hM.1.le hM.2
    have heventually : ∀ᶠ n : ℕ in atTop, M ^ n < Real.tan δ ^ 2 :=
      hpow.eventually (Iio_mem_nhds htanδ)
    filter_upwards [heventually] with n hn
    have htδ : t n < δ := by
      by_contra hnot
      have hδtn : δ ≤ t n := le_of_not_gt hnot
      have htnK : t n ∈ Icc δ (Real.pi / 2) := ⟨hδtn, (ht n).2.le⟩
      have hrle : r (t n) ≤ M := hsmax htnK
      have hrpos : 0 ≤ r (t n) :=
        (sine_ratio_pos_lt_one ha hab hb ⟨(ht n).1, (ht n).2.le⟩).1.le
      have hrpow : r (t n) ^ n ≤ M ^ n := by
        exact pow_le_pow_left₀ hrpos hrle n
      have hδhalf : δ < Real.pi / 2 := by
        calc
          δ ≤ Real.pi / 4 := min_le_right _ _
          _ < Real.pi / 2 := by linarith [Real.pi_pos]
      have htanmono : Real.tan δ ≤ Real.tan (t n) := by
        exact Real.strictMonoOn_tan.monotoneOn
          ⟨by linarith [Real.pi_pos], hδhalf⟩
          ⟨by linarith [Real.pi_pos], (ht n).2⟩ hδtn
      have htansq : Real.tan δ ^ 2 ≤ Real.tan (t n) ^ 2 := by
        nlinarith [Real.tan_pos_of_pos_of_lt_pi_div_two hδ0 hδhalf]
      have hcontra : Real.tan (t n) ^ 2 < Real.tan δ ^ 2 := by
        calc
          Real.tan (t n) ^ 2 = r (t n) ^ n := (hroot n).symm
          _ ≤ M ^ n := hrpow
          _ < Real.tan δ ^ 2 := hn
      linarith
    exact htδ.trans hδε

/-- For arbitrary frequencies, an interior accumulation point of positive roots,
away from a zero of the denominator, lies on the level set `sin (a t) / sin (b t) = 1`.
The explicit positivity hypothesis is automatic for odd exponents because the
right-hand side is positive. -/
theorem accumulation_point_on_level_set
    {a b tStar : ℝ} (t : ℕ → ℝ)
    (ht : Tendsto t atTop (𝓝 tStar))
    (htStar : tStar ∈ Ioo (0 : ℝ) (Real.pi / 2))
    (hdenom : Real.sin (b * tStar) ≠ 0)
    (hrpos : ∀ n, 0 < Real.sin (a * t n) / Real.sin (b * t n))
    (hroot : ∀ n,
      (Real.sin (a * t n) / Real.sin (b * t n)) ^ n = Real.tan (t n) ^ 2) :
    Real.sin (a * tStar) / Real.sin (b * tStar) = 1 := by
  let r : ℝ → ℝ := fun x => Real.sin (a * x) / Real.sin (b * x)
  have hrcont : ContinuousAt r tStar := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hdenom
  have hrlim : Tendsto (fun n => r (t n)) atTop (𝓝 (r tStar)) :=
    hrcont.tendsto.comp ht
  have htanlim : Tendsto (fun n => Real.tan (t n) ^ 2) atTop
      (𝓝 (Real.tan tStar ^ 2)) := by
    have hcos : Real.cos tStar ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [htStar.1, Real.pi_pos], htStar.2⟩).ne'
    exact ((Real.continuousAt_tan.mpr hcos).pow 2).tendsto.comp ht
  have htanStar : 0 < Real.tan tStar ^ 2 := by
    have : 0 < Real.tan tStar :=
      Real.tan_pos_of_pos_of_lt_pi_div_two htStar.1 htStar.2
    positivity
  apply le_antisymm
  · by_contra hnot
    have hone_lt : 1 < r tStar := lt_of_not_ge hnot
    let q : ℝ := (1 + r tStar) / 2
    have hq1 : 1 < q := by dsimp [q]; linarith
    have hqr : q < r tStar := by dsimp [q]; linarith
    have hevent_r : ∀ᶠ n in atTop, q < r (t n) :=
      hrlim.eventually (Ioi_mem_nhds hqr)
    have hpow : Tendsto (fun n : ℕ => q ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hq1
    have hevent_pow' : ∀ᶠ n : ℕ in atTop, Real.tan tStar ^ 2 + 2 ≤ q ^ n :=
      tendsto_atTop.1 hpow (Real.tan tStar ^ 2 + 2)
    have hevent_pow : ∀ᶠ n : ℕ in atTop, Real.tan tStar ^ 2 + 1 < q ^ n :=
      hevent_pow'.mono (fun _ hn => by linarith)
    have hevent_tan : ∀ᶠ n : ℕ in atTop,
        Real.tan (t n) ^ 2 < Real.tan tStar ^ 2 + 1 :=
      htanlim.eventually (Iio_mem_nhds (by linarith))
    obtain ⟨n, hqrn, hp, htan⟩ :=
      (hevent_r.and (hevent_pow.and hevent_tan)).exists
    have hqnonneg : 0 ≤ q := le_trans zero_le_one hq1.le
    have hpowle : q ^ n ≤ r (t n) ^ n :=
      pow_le_pow_left₀ hqnonneg hqrn.le n
    change q ^ n ≤ (Real.sin (a * t n) / Real.sin (b * t n)) ^ n at hpowle
    rw [hroot n] at hpowle
    linarith
  · by_contra hnot
    have hr_lt : r tStar < 1 := lt_of_not_ge hnot
    have hr_nonneg : 0 ≤ r tStar :=
      ge_of_tendsto hrlim (Eventually.of_forall fun n => by
        show 0 ≤ r (t n)
        exact (hrpos n).le)
    let q : ℝ := (r tStar + 1) / 2
    have hq0 : 0 ≤ q := by dsimp [q]; linarith
    have hq1 : q < 1 := by dsimp [q]; linarith
    have hrq : r tStar < q := by dsimp [q]; linarith
    have hevent_r : ∀ᶠ n in atTop, r (t n) < q :=
      hrlim.eventually (Iio_mem_nhds hrq)
    have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have hevent_pow : ∀ᶠ n : ℕ in atTop, q ^ n < Real.tan tStar ^ 2 / 2 :=
      hpow.eventually (Iio_mem_nhds (half_pos htanStar))
    have hevent_tan : ∀ᶠ n : ℕ in atTop,
        Real.tan tStar ^ 2 / 2 < Real.tan (t n) ^ 2 :=
      htanlim.eventually (Ioi_mem_nhds (by linarith))
    obtain ⟨n, hrn, hp, htan⟩ :=
      (hevent_r.and (hevent_pow.and hevent_tan)).exists
    have hrpow : r (t n) ^ n ≤ q ^ n :=
      pow_le_pow_left₀ (by
        show 0 ≤ r (t n)
        exact (hrpos n).le) hrn.le n
    change (Real.sin (a * t n) / Real.sin (b * t n)) ^ n ≤ q ^ n at hrpow
    rw [hroot n] at hrpow
    linarith

end RootCollapse
