import SSPRK.ChainMatrices
import Mathlib.Tactic

/-!
# Third-order SDIRK tableau

The family in V2.10, Theorem 5.2 has `s` stages and realizes the third-order
conditions at its stated radius.
-/

open scoped BigOperators

namespace SSPRK

noncomputable section

/-- The third-order radius from the SDIRK family. -/
def thirdOrderRadius (s : ℕ) : ℝ := (s : ℝ) - 1 + Real.sqrt ((s : ℝ) ^ 2 - 1)

/-- The square-root parameter of the SDIRK family. -/
def sdirkT (s : ℕ) : ℝ := Real.sqrt ((s : ℝ) ^ 2 - 1)

/-- The normalized chain length. -/
def sdirkQ (s : ℕ) : ℝ := ((s : ℝ) - 1) / sdirkT s

/-- The diagonal SDIRK coefficient. -/
def sdirkGamma (s : ℕ) : ℝ := (1 - sdirkQ s) / 2

/-- The strict lower-triangular SDIRK coefficient. -/
def sdirkDelta (s : ℕ) : ℝ := 1 / sdirkT s

/-- The factor in the shifted-chain representation. -/
def sdirkD (s : ℕ) : ℝ := 1 + sdirkQ s

/-- The SDIRK matrix from the third-order family. -/
def sdirkA (s : ℕ) : Matrix (Fin s) (Fin s) ℝ := fun i j ↦
  if j < i then sdirkDelta s else if i = j then sdirkGamma s else 0

/-- The uniform output row of the SDIRK family. -/
def sdirkB (s : ℕ) : Fin s → ℝ := fun _ ↦ 1 / (s : ℝ)

lemma sum_fin_val (s : ℕ) : ∑ i : Fin s, (i : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_add_distrib, ih]
    simp
    ring

lemma sum_fin_val_sq (s : ℕ) :
    ∑ i : Fin s, (i : ℝ) ^ 2 = (s : ℝ) * ((s : ℝ) - 1) * (2 * (s : ℝ) - 1) / 6 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_succ, Nat.cast_add, Nat.cast_one]
    have hterm : ∀ i : Fin s, ((i : ℝ) + 1) ^ 2 = (i : ℝ) ^ 2 + 2 * (i : ℝ) + 1 := by
      intro i
      ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ih, ← Finset.mul_sum, sum_fin_val]
    simp
    ring

lemma sdirkT_sq {s : ℕ} (hs : 2 ≤ s) :
    sdirkT s ^ 2 = ((s : ℝ) - 1) * ((s : ℝ) + 1) := by
  unfold sdirkT
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  rw [Real.sq_sqrt]
  · ring
  · nlinarith

lemma sdirkT_pos {s : ℕ} (hs : 2 ≤ s) : 0 < sdirkT s := by
  unfold sdirkT
  apply Real.sqrt_pos.2
  have hsreal : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  nlinarith

lemma sdirk_delta_mul (s : ℕ) :
    ((s : ℝ) - 1) * sdirkDelta s = sdirkQ s := by
  unfold sdirkDelta sdirkQ
  ring

lemma sdirkD_pos {s : ℕ} (hs : 2 ≤ s) : 0 < sdirkD s := by
  unfold sdirkD sdirkQ
  have ht : 0 < sdirkT s := sdirkT_pos hs
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  positivity

lemma one_le_sdirkD {s : ℕ} (hs : 2 ≤ s) : 1 ≤ sdirkD s := by
  unfold sdirkD sdirkQ
  have ht : 0 < sdirkT s := sdirkT_pos hs
  have hsreal : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
  have hq : 0 ≤ ((s : ℝ) - 1) / sdirkT s := div_nonneg (by linarith) ht.le
  linarith

lemma thirdOrderRadius_pos {s : ℕ} (hs : 2 ≤ s) : 0 < thirdOrderRadius s := by
  unfold thirdOrderRadius
  have hsreal : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
  have ht : 0 < sdirkT s := sdirkT_pos hs
  unfold sdirkT at ht
  linarith

lemma sdirkT_div_lt_one {s : ℕ} (hs : 2 ≤ s) : sdirkT s / (s : ℝ) < 1 := by
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
  have ht_sq := sdirkT_sq hs
  have ht : 0 < sdirkT s := sdirkT_pos hs
  apply (div_lt_one₀ hsreal).2
  nlinarith

lemma thirdOrderRadius_mul_delta {s : ℕ} (hs : 2 ≤ s) :
    thirdOrderRadius s * sdirkDelta s = sdirkD s := by
  unfold thirdOrderRadius sdirkDelta sdirkD sdirkQ
  change (((s : ℝ) - 1) + sdirkT s) * (1 / sdirkT s) = 1 + ((s : ℝ) - 1) / sdirkT s
  have ht : sdirkT s ≠ 0 := ne_of_gt (sdirkT_pos hs)
  field_simp [ht]
  ring

lemma thirdOrderRadius_mul_gamma {s : ℕ} (hs : 2 ≤ s) :
    thirdOrderRadius s * sdirkGamma s = sdirkQ s := by
  unfold thirdOrderRadius sdirkGamma sdirkQ
  change (((s : ℝ) - 1) + sdirkT s) * ((1 - ((s : ℝ) - 1) / sdirkT s) / 2) =
    ((s : ℝ) - 1) / sdirkT s
  have ht : sdirkT s ≠ 0 := ne_of_gt (sdirkT_pos hs)
  have ht_sq := sdirkT_sq hs
  field_simp [ht]
  nlinarith

lemma sdirk_shifted_eq_chainL {s : ℕ} (hs : 2 ≤ s) :
    1 + thirdOrderRadius s • sdirkA s = sdirkD s • chainL s := by
  ext i j
  unfold sdirkA chainL
  by_cases hji : j < i
  · have hij : i ≠ j := ne_of_gt hji
    simp [hji, hji.le, hij, thirdOrderRadius_mul_delta hs]
  · by_cases hij : i = j
    · subst i
      simp [thirdOrderRadius_mul_gamma hs, sdirkD]
    · have hij_lt : i < j := lt_of_le_of_ne (le_of_not_gt hji) hij
      simp [hji, hij, hij_lt]

lemma sdirkA_mulVec_ones (s : ℕ) (i : Fin s) :
    Matrix.mulVec (sdirkA s) (ones s) i = sdirkGamma s + (i : ℝ) * sdirkDelta s := by
  classical
  simp [Matrix.mulVec, dotProduct, sdirkA, ones, Finset.sum_ite]
  have hcard : (Finset.univ.filter fun j : Fin s ↦ j < i).card = i.val := by
    have hset : Finset.univ.filter (fun j : Fin s ↦ j < i) = Finset.Iio i := by
      ext j
      simp
    rw [hset, Fin.card_Iio]
  rw [hcard]
  ring

lemma sdirk_node_mean (s : ℕ) :
    sdirkGamma s + ((s : ℝ) - 1) * sdirkDelta s / 2 = 1 / 2 := by
  unfold sdirkGamma
  linarith [sdirk_delta_mul s]

theorem sdirk_order_one {s : ℕ} (hs : 0 < s) :
    dotProduct (sdirkB s) (ones s) = 1 := by
  have hsreal : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  simp [dotProduct, sdirkB, ones]
  field_simp [hsreal]

theorem sdirk_order_two {s : ℕ} (hs : 0 < s) :
    dotProduct (sdirkB s) (Matrix.mulVec (sdirkA s) (ones s)) = 1 / 2 := by
  have hsreal : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  calc
    dotProduct (sdirkB s) (Matrix.mulVec (sdirkA s) (ones s)) =
        ∑ i : Fin s, (1 / (s : ℝ)) * (sdirkGamma s + (i : ℝ) * sdirkDelta s) := by
          simp only [dotProduct, sdirkB]
          congr with i
          rw [sdirkA_mulVec_ones]
    _ = sdirkGamma s + ((s : ℝ) - 1) * sdirkDelta s / 2 := by
      rw [← Finset.mul_sum]
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, sum_fin_val]
      simp
      field_simp [hsreal]
    _ = 1 / 2 := sdirk_node_mean s

lemma sdirk_node_sq_mean {s : ℕ} (hs : 0 < s) :
    dotProduct (sdirkB s) (fun i ↦ (Matrix.mulVec (sdirkA s) (ones s) i) ^ 2) =
      sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
        sdirkDelta s ^ 2 * ((s : ℝ) - 1) * (2 * (s : ℝ) - 1) / 6 := by
  have hsreal : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  calc
    dotProduct (sdirkB s) (fun i ↦ (Matrix.mulVec (sdirkA s) (ones s) i) ^ 2) =
        ∑ i : Fin s, (1 / (s : ℝ)) * (sdirkGamma s + (i : ℝ) * sdirkDelta s) ^ 2 := by
          simp only [dotProduct, sdirkB]
          congr with i
          rw [sdirkA_mulVec_ones]
    _ = sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
        sdirkDelta s ^ 2 * ((s : ℝ) - 1) * (2 * (s : ℝ) - 1) / 6 := by
          rw [← Finset.mul_sum]
          have hterm : ∀ i : Fin s, (sdirkGamma s + (i : ℝ) * sdirkDelta s) ^ 2 =
              sdirkGamma s ^ 2 + (2 * sdirkGamma s * sdirkDelta s) * (i : ℝ) +
                sdirkDelta s ^ 2 * (i : ℝ) ^ 2 := by
            intro i
            ring
          simp_rw [hterm]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
            ← Finset.mul_sum, ← Finset.mul_sum, sum_fin_val, sum_fin_val_sq]
          simp
          field_simp [hsreal]

lemma sdirk_node_sq_mean_eq_third {s : ℕ} (hs : 2 ≤ s) :
    sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
      sdirkDelta s ^ 2 * ((s : ℝ) - 1) * (2 * (s : ℝ) - 1) / 6 = 1 / 3 := by
  unfold sdirkGamma sdirkDelta sdirkQ
  have ht : sdirkT s ≠ 0 := ne_of_gt (sdirkT_pos hs)
  have ht_sq := sdirkT_sq hs
  field_simp [ht]
  nlinarith

theorem sdirk_order_three_node {s : ℕ} (hs : 2 ≤ s) :
    dotProduct (sdirkB s) (fun i ↦ (Matrix.mulVec (sdirkA s) (ones s) i) ^ 2) = 1 / 3 := by
  rw [sdirk_node_sq_mean (by omega : 0 < s), sdirk_node_sq_mean_eq_third hs]

lemma ones_vecMul_sdirkA (s : ℕ) (j : Fin s) :
    Matrix.vecMul (ones s) (sdirkA s) j =
      sdirkGamma s + ((s : ℝ) - 1 - (j : ℝ)) * sdirkDelta s := by
  classical
  simp [Matrix.vecMul, dotProduct, sdirkA, ones, Finset.sum_ite]
  have hcard : (Finset.univ.filter fun i : Fin s ↦ j < i).card = s - 1 - j.val := by
    have hset : Finset.univ.filter (fun i : Fin s ↦ j < i) = Finset.Ioi j := by
      ext i
      simp
    rw [hset, Fin.card_Ioi]
  rw [hcard]
  have hsub : ((s - 1 - j.val : ℕ) : ℝ) = (s : ℝ) - 1 - (j : ℝ) := by
    have hj : j.val ≤ s - 1 := by omega
    rw [Nat.cast_sub hj, Nat.cast_sub (by omega : 1 ≤ s)]
    norm_num
  rw [hsub]
  ring

lemma sdirk_A_node_mean {s : ℕ} (hs : 0 < s) :
    dotProduct (sdirkB s)
      (Matrix.mulVec (sdirkA s) (Matrix.mulVec (sdirkA s) (ones s))) =
      sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
        sdirkDelta s ^ 2 * ((s : ℝ) - 1) * ((s : ℝ) - 2) / 6 := by
  have hsreal : (s : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs
  calc
    dotProduct (sdirkB s)
        (Matrix.mulVec (sdirkA s) (Matrix.mulVec (sdirkA s) (ones s))) =
        (1 / (s : ℝ)) * dotProduct (ones s)
          (Matrix.mulVec (sdirkA s) (Matrix.mulVec (sdirkA s) (ones s))) := by
            simp only [dotProduct, sdirkB, ones, one_mul]
            rw [← Finset.mul_sum]
    _ = (1 / (s : ℝ)) * dotProduct (Matrix.vecMul (ones s) (sdirkA s))
          (Matrix.mulVec (sdirkA s) (ones s)) := by
            rw [Matrix.dotProduct_mulVec]
    _ = (1 / (s : ℝ)) * ∑ i : Fin s,
          (sdirkGamma s + ((s : ℝ) - 1 - (i : ℝ)) * sdirkDelta s) *
            (sdirkGamma s + (i : ℝ) * sdirkDelta s) := by
              unfold dotProduct
              congr with i
              rw [ones_vecMul_sdirkA, sdirkA_mulVec_ones]
    _ = sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
        sdirkDelta s ^ 2 * ((s : ℝ) - 1) * ((s : ℝ) - 2) / 6 := by
          have hterm : ∀ i : Fin s,
              (sdirkGamma s + ((s : ℝ) - 1 - (i : ℝ)) * sdirkDelta s) *
                (sdirkGamma s + (i : ℝ) * sdirkDelta s) =
                sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
                  sdirkDelta s ^ 2 * ((s : ℝ) - 1) * (i : ℝ) -
                    sdirkDelta s ^ 2 * (i : ℝ) ^ 2 := by
            intro i
            ring
          simp_rw [hterm]
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_const, Finset.sum_const, ← Finset.mul_sum, ← Finset.mul_sum,
            sum_fin_val, sum_fin_val_sq]
          simp
          field_simp [hsreal]
          ring

lemma sdirk_A_node_mean_eq_sixth {s : ℕ} (hs : 2 ≤ s) :
    sdirkGamma s ^ 2 + sdirkGamma s * sdirkDelta s * ((s : ℝ) - 1) +
      sdirkDelta s ^ 2 * ((s : ℝ) - 1) * ((s : ℝ) - 2) / 6 = 1 / 6 := by
  unfold sdirkGamma sdirkDelta sdirkQ
  have ht : sdirkT s ≠ 0 := ne_of_gt (sdirkT_pos hs)
  have ht_sq := sdirkT_sq hs
  field_simp [ht]
  nlinarith

theorem sdirk_order_three_tree {s : ℕ} (hs : 2 ≤ s) :
    dotProduct (sdirkB s)
      (Matrix.mulVec (sdirkA s) (Matrix.mulVec (sdirkA s) (ones s))) = 1 / 6 := by
  rw [sdirk_A_node_mean (by omega : 0 < s), sdirk_A_node_mean_eq_sixth hs]

end

end SSPRK
