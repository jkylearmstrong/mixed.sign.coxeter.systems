/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MixedSignCoxeter.Basic

/-!
# Generalized Howlett Theorem (Theorem 1.1)

Formalization of Section 2.6.1 (Theorem 1.1) of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main definitions
* `howlettU B`: Upper-triangular matrix `U` with `U i j = B i j` for `i < j`,
  `B i i / 2` for `i = j`, and `0` for `i > j`.
* `principalElement S`: The product `s_0 * s_1 * ... * s_{n-1}`.

## Main results
* `howlett_U_mul_principalElement` (Theorem 1.1):
  `howlettU S.B * principalElement S = -(howlettU S.B)ᵀ`.
-/

open Matrix BigOperators

namespace ReflectionSystem

variable {n : ℕ}

/-- The upper-triangular matrix `U` from Theorem 1.1. -/
noncomputable def howlettU (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  of fun i j =>
    if i < j then B i j
    else if i = j then B i i / 2
    else 0

@[simp]
lemma howlettU_apply (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    howlettU B i j = if i < j then B i j else if i = j then B i i / 2 else 0 := rfl

/-- Prefix product `s_0 * s_1 * ... * s_{k-1}` for `k ≤ n`. -/
noncomputable def prefixProd (B : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 =>
    if hk : k < n then
      prefixProd B k * reflectionMatrix B ⟨k, hk⟩
    else
      prefixProd B k

/-- The standard principal element `s_0 * s_1 * ... * s_{n-1}` (Definition 2.53). -/
noncomputable def principalElement (S : ReflectionSystem n) : Matrix (Fin n) (Fin n) ℝ :=
  prefixProd S.B n

/-- Block-diagonal intermediate matrix `M_k` in the inductive proof of Theorem 1.1:
top-left `k × k` block is `-(howlettU B)ᵀ`, bottom-right `(n-k) × (n-k)` block is `howlettU B`. -/
private noncomputable def howlettBlock (B : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  of fun r c =>
    if (r : ℕ) < k ∧ (c : ℕ) < k then -(howlettU B)ᵀ r c
    else if k ≤ (r : ℕ) ∧ k ≤ (c : ℕ) then howlettU B r c
    else 0

private lemma howlettBlock_zero (B : Matrix (Fin n) (Fin n) ℝ) :
    howlettBlock B 0 = howlettU B := by
  ext r c
  simp [howlettBlock]

private lemma howlettBlock_n (B : Matrix (Fin n) (Fin n) ℝ) :
    howlettBlock B n = -(howlettU B)ᵀ := by
  ext r c
  simp [howlettBlock]

private lemma howlettBlock_step (S : ReflectionSystem n) (k : ℕ) (hk : k < n) :
    howlettBlock S.B k * reflectionMatrix S.B ⟨k, hk⟩ = howlettBlock S.B (k + 1) := by
  let idx : Fin n := ⟨k, hk⟩
  have hB : S.B idx idx ≠ 0 := S.B_diag_ne_zero idx
  have hsymm : ∀ a b, S.B a b = S.B b a := fun a b => S.B_symm.apply b a
  ext r c
  simp only [mul_apply, reflectionMatrix_apply]
  have hexpand : ∀ m : Fin n,
      howlettBlock S.B k r m *
        ((if m = c then (1 : ℝ) else 0) - (if m = idx then 2 * S.B idx c / S.B idx idx else 0)) =
      (if m = c then howlettBlock S.B k r m else 0) -
        (if m = idx then howlettBlock S.B k r m * (2 * S.B idx c / S.B idx idx) else 0) := by
    intro m
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hexpand m), Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  simp only [howlettBlock, of_apply, transpose_apply, howlettU_apply]
  have hidx_val : (idx : ℕ) = k := rfl
  rcases lt_trichotomy (r : ℕ) k with hr_lt | hr_eq | hr_gt
  · -- Case 1: r < k
    have h1 : ¬ (k ≤ (r : ℕ)) := not_le_of_gt hr_lt
    have h2 : ¬ ((idx : ℕ) < k) := by omega
    have hr_lt1 : (r : ℕ) < k + 1 := by omega
    have h3 : ¬ (k + 1 ≤ (r : ℕ)) := by omega
    simp only [h1, false_and, ↓reduceIte, h2, and_false, hr_lt1, true_and, h3]
    by_cases hc_lt : (c : ℕ) < k
    · have hc_lt1 : (c : ℕ) < k + 1 := by omega
      simp [hr_lt, hc_lt, hc_lt1]
    · have hc_ge : k ≤ (c : ℕ) := le_of_not_gt hc_lt
      by_cases hc_eq : (c : ℕ) = k
      · have hc_lt1 : (c : ℕ) < k + 1 := by omega
        have hcr_not_lt : ¬ (c < r) := by
          intro h
          have h' : (c : ℕ) < (r : ℕ) := h
          omega
        have hcr_ne : c ≠ r := by omega
        simp [hr_lt, hc_lt, hc_lt1, hcr_not_lt, hcr_ne]
      · have hc_not_lt1 : ¬ ((c : ℕ) < k + 1) := by omega
        simp [hr_lt, hc_lt, hc_not_lt1]
  · -- Case 2: r = k
    have hr_idx : r = idx := Fin.ext hr_eq
    subst hr_idx
    have hnot_lt : ¬ ((idx : ℕ) < k) := by omega
    have hle : k ≤ (idx : ℕ) := by omega
    have hlt1 : (idx : ℕ) < k + 1 := by omega
    have hnot_le1 : ¬ (k + 1 ≤ (idx : ℕ)) := by omega
    simp only [hnot_lt, false_and, ↓reduceIte, hle, true_and, lt_self_iff_false, hlt1, hnot_le1]
    have hhalf : S.B idx idx / 2 * (2 * S.B idx c / S.B idx idx) = S.B idx c := by
      field_simp
    rw [hhalf]
    rcases lt_trichotomy (c : ℕ) k with hc_lt | hc_eq | hc_gt
    · have hc_not_le : ¬ (k ≤ (c : ℕ)) := by omega
      have hc_lt1 : (c : ℕ) < k + 1 := by omega
      have hci : c < idx := hc_lt
      simp [hc_not_le, hc_lt1, hci, hsymm c idx]
    · have hc_idx : c = idx := Fin.ext hc_eq
      subst hc_idx
      simp [hle, hlt1]
      ring
    · have hc_le : k ≤ (c : ℕ) := by omega
      have hc_not_lt1 : ¬ ((c : ℕ) < k + 1) := by omega
      have hic : idx < c := hc_gt
      simp [hc_le, hc_not_lt1, hic]
  · -- Case 3: r > k
    have hr_not_lt : ¬ ((r : ℕ) < k) := by omega
    have hr_le : k ≤ (r : ℕ) := by omega
    have hr_not_lt1 : ¬ ((r : ℕ) < k + 1) := by omega
    have hr_le1 : k + 1 ≤ (r : ℕ) := by omega
    have hidx_not_lt : ¬ (r < idx) := by
      intro h
      exact absurd h (not_lt_of_gt hr_gt)
    have hr_ne_idx : r ≠ idx := by
      intro h
      rw [h] at hr_gt
      exact absurd hr_gt (lt_irrefl _)
    simp only [hr_not_lt, false_and, ↓reduceIte, hr_le, true_and, hidx_not_lt, hr_ne_idx,
      hr_not_lt1, hr_le1]
    rcases lt_trichotomy (c : ℕ) k with hc_lt | hc_eq | hc_gt
    · have hc_not_le : ¬ (k ≤ (c : ℕ)) := by omega
      have hc_not_le1 : ¬ (k + 1 ≤ (c : ℕ)) := by omega
      simp [hc_not_le, hc_not_le1]
    · have hc_not_le1 : ¬ (k + 1 ≤ (c : ℕ)) := by omega
      have hc_idx : c = idx := Fin.ext hc_eq
      subst hc_idx
      simp [hidx_not_lt, hr_ne_idx, hc_not_le1]
    · have hc_le : k ≤ (c : ℕ) := by omega
      have hc_le1 : k + 1 ≤ (c : ℕ) := by omega
      simp [hc_le, hc_le1]

private lemma howlett_prefix_invariant (S : ReflectionSystem n) :
    ∀ k : ℕ, k ≤ n → howlettU S.B * prefixProd S.B k = howlettBlock S.B k
  | 0, _ => by
    simp [prefixProd, howlettBlock_zero]
  | k + 1, hk => by
    have hk_lt : k < n := hk
    have ih := howlett_prefix_invariant S k (le_of_lt hk_lt)
    simp only [prefixProd, hk_lt, ↓reduceDIte]
    rw [← Matrix.mul_assoc, ih, howlettBlock_step S k hk_lt]

/-- **Theorem 1.1** (Generalized Howlett's Theorem):
For any reflection system `(W, S, B)`, `U * (s_0 * s_1 * ... * s_{n-1}) = -Uᵀ`. -/
theorem howlett_U_mul_principalElement (S : ReflectionSystem n) :
    howlettU S.B * principalElement S = -(howlettU S.B)ᵀ := by
  unfold principalElement
  rw [howlett_prefix_invariant S n (le_refl n), howlettBlock_n]

/-- `howlettU S.B` is upper triangular, so its determinant is the product of its
nonzero diagonal entries `∏ i, B i i / 2 ≠ 0`. -/
lemma howlettU_det (S : ReflectionSystem n) :
    (howlettU S.B).det = ∏ i : Fin n, S.B i i / 2 := by
  have htri : (howlettU S.B).BlockTriangular id := by
    intro i j hij
    have h1 : ¬ (i < j) := not_lt_of_gt hij
    have h2 : i ≠ j := ne_of_gt hij
    simp [howlettU_apply, h1, h2]
  rw [Matrix.det_of_isUpperTriangular htri]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [howlettU_apply]

lemma howlettU_det_ne_zero (S : ReflectionSystem n) : (howlettU S.B).det ≠ 0 := by
  rw [howlettU_det]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact div_ne_zero (S.B_diag_ne_zero i) (by norm_num)

/-- **Lemma 2.63**: Up to the nonzero scalar `(det U)⁻¹`, the characteristic polynomial
`det (x I - w)` of the principal element equals `det (x U + Uᵀ)`. -/
theorem principal_charpoly_eq (S : ReflectionSystem n) (x : ℝ) :
    (x • (1 : Matrix (Fin n) (Fin n) ℝ) - principalElement S).det =
      (howlettU S.B).det⁻¹ * (x • howlettU S.B + (howlettU S.B)ᵀ).det := by
  have hmul : howlettU S.B * (x • (1 : Matrix (Fin n) (Fin n) ℝ) - principalElement S) =
      x • howlettU S.B + (howlettU S.B)ᵀ := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, howlett_U_mul_principalElement]
    abel
  have hdet := congr_arg Matrix.det hmul
  rw [Matrix.det_mul] at hdet
  have hU := howlettU_det_ne_zero S
  calc
    (x • (1 : Matrix (Fin n) (Fin n) ℝ) - principalElement S).det
        = (howlettU S.B).det⁻¹ * ((howlettU S.B).det *
            (x • (1 : Matrix (Fin n) (Fin n) ℝ) - principalElement S).det) := by
          field_simp
    _ = (howlettU S.B).det⁻¹ * (x • howlettU S.B + (howlettU S.B)ᵀ).det := by
          rw [hdet]

/-- **Theorem 1.1 (inverse form)**: Since `howlettU S.B` is invertible (`howlettU_det_ne_zero`),
`principalElement S = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ`. -/
theorem howlett_principalElement_eq_neg_inv_mul_transpose (S : ReflectionSystem n) :
    principalElement S = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ := by
  have hU : IsUnit (howlettU S.B).det := (howlettU_det_ne_zero S).isUnit
  have hinv : (howlettU S.B)⁻¹ * howlettU S.B = 1 := Matrix.nonsing_inv_mul _ hU
  calc
    principalElement S = 1 * principalElement S := (Matrix.one_mul _).symm
    _ = ((howlettU S.B)⁻¹ * howlettU S.B) * principalElement S := by rw [hinv]
    _ = (howlettU S.B)⁻¹ * (howlettU S.B * principalElement S) := Matrix.mul_assoc _ _ _
    _ = (howlettU S.B)⁻¹ * (-(howlettU S.B)ᵀ) := by rw [howlett_U_mul_principalElement]
    _ = -(howlettU S.B)⁻¹ * (howlettU S.B)ᵀ := by rw [Matrix.mul_neg, Matrix.neg_mul]

end ReflectionSystem

