/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Reflection Systems

Formalization of Chapter 2 (Sections 2.1–2.3) of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012).

## Main definitions
* `ReflectionSystem n`: A symmetric bilinear form `B : Matrix (Fin n) (Fin n) ℝ`
  with nonzero diagonal entries `B i i ≠ 0` (Definition 2.18).
* `reflectionMatrix B i`: The generating reflection `s_i` through `H_{e_i}` (Remark 2.7).

## Main results
* `reflectionMatrix_mul_self`: `s_i * s_i = 1` (Remark 2.20).
* `reflectionMatrix_preserves_B`: `(s_i)ᵀ * B * s_i = B` (Proposition 2.17).
* `reflectionMatrix_comm_of_orthogonal`: `B i j = 0 → s_i * s_j = s_j * s_i` (Proposition 2.22).
* `reflectionMatrix_neg`: `reflectionMatrix (-B) i = reflectionMatrix B i` (Lemma 2.31).
-/

open Matrix BigOperators

/-- A reflection system `(W, S, B)` on `ℝⁿ` is determined by a symmetric
matrix `B` with nonzero diagonal entries (Definition 2.18, Remark 2.19). -/
structure ReflectionSystem (n : ℕ) where
  B : Matrix (Fin n) (Fin n) ℝ
  B_symm : B.IsSymm
  B_diag_ne_zero : ∀ i : Fin n, B i i ≠ 0

namespace ReflectionSystem

variable {n : ℕ}

/-- The `i`-th generating reflection matrix `s_i` associated to a bilinear form `B`
(Remark 2.7):
`(s_i)_{r, c} = δ_{r, c} - δ_{r, i} * (2 * B i c / B i i)`. -/
noncomputable def reflectionMatrix (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  of fun r c => (if r = c then 1 else 0) - (if r = i then 2 * B i c / B i i else 0)

@[simp]
lemma reflectionMatrix_apply (B : Matrix (Fin n) (Fin n) ℝ) (i r c : Fin n) :
    reflectionMatrix B i r c =
      (if r = c then 1 else 0) - (if r = i then 2 * B i c / B i i else 0) := rfl

lemma reflectionMatrix_apply_self (B : Matrix (Fin n) (Fin n) ℝ) {i : Fin n} (h : B i i ≠ 0) :
    reflectionMatrix B i i i = -1 := by
  simp [h]
  ring

/-- **Lemma 2.31**: Negating the bilinear form `B` yields the exact same generating
reflections, hence `W(B) = W(-B)`. -/
theorem reflectionMatrix_neg (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    reflectionMatrix (-B) i = reflectionMatrix B i := by
  ext r c
  simp [neg_div, div_neg]

/-- **Remark 2.20**: Every generating reflection `s_i` is an involution (`s_i * s_i = 1`). -/
theorem reflectionMatrix_mul_self (S : ReflectionSystem n) (i : Fin n) :
    reflectionMatrix S.B i * reflectionMatrix S.B i = 1 := by
  have hB : S.B i i ≠ 0 := S.B_diag_ne_zero i
  ext r c
  simp only [mul_apply, one_apply, reflectionMatrix_apply]
  have hsum : ∀ k : Fin n,
      ((if r = k then (1 : ℝ) else 0) - (if r = i then 2 * S.B i k / S.B i i else 0)) *
        ((if k = c then (1 : ℝ) else 0) - (if k = i then 2 * S.B i c / S.B i i else 0)) =
      (if k = r then if r = c then (1 : ℝ) else 0 else 0)
        - (if k = r then if r = i then 2 * S.B i c / S.B i i else 0 else 0)
        - (if k = c then if r = i then 2 * S.B i k / S.B i i else 0 else 0)
        + (if k = i then if r = i then (2 * S.B i k / S.B i i) * (2 * S.B i c / S.B i i) else 0 else 0) := by
    intro k
    split_ifs <;> simp_all <;> ring
  simp_rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  simp only [↓reduceIte]
  by_cases hri : r = i <;> simp [hri]
  field_simp
  ring

/-- **Proposition 2.17**: Each generating reflection `s_i` preserves `B`:
`(s_i)ᵀ * B * s_i = B`. -/
theorem reflectionMatrix_preserves_B (S : ReflectionSystem n) (i : Fin n) :
    (reflectionMatrix S.B i)ᵀ * S.B * reflectionMatrix S.B i = S.B := by
  have hB : S.B i i ≠ 0 := S.B_diag_ne_zero i
  have hsymm : ∀ a b, S.B a b = S.B b a := fun a b => S.B_symm.apply b a
  ext r c
  have hleft : ∀ k : Fin n,
      ((reflectionMatrix S.B i)ᵀ * S.B) r k = S.B r k - (2 * S.B i r / S.B i i) * S.B i k := by
    intro k
    simp only [mul_apply, transpose_apply, reflectionMatrix_apply]
    have hterm : ∀ m : Fin n,
        ((if m = r then (1 : ℝ) else 0) - (if m = i then 2 * S.B i r / S.B i i else 0)) * S.B m k =
        (if m = r then S.B m k else 0) - (if m = i then (2 * S.B i r / S.B i i) * S.B m k else 0) := by
      intro m
      split_ifs <;> ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
    simp only [↓reduceIte]
  rw [mul_apply]
  simp_rw [hleft, reflectionMatrix_apply]
  have hterm2 : ∀ k : Fin n,
      (S.B r k - 2 * S.B i r / S.B i i * S.B i k) *
        ((if k = c then (1 : ℝ) else 0) - (if k = i then 2 * S.B i c / S.B i i else 0)) =
      (if k = c then S.B r k - 2 * S.B i r / S.B i i * S.B i k else 0) -
        (if k = i then (S.B r k - 2 * S.B i r / S.B i i * S.B i k) * (2 * S.B i c / S.B i i) else 0) := by
    intro k
    split_ifs <;> ring
  simp_rw [hterm2, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  simp only [↓reduceIte]
  rw [hsymm r i]
  field_simp
  ring

/-- **Proposition 2.22**: If `e_i` and `e_j` are orthogonal relative to `B` (`B i j = 0`),
then `s_i` and `s_j` commute (`s_i * s_j = s_j * s_i`). -/
theorem reflectionMatrix_comm_of_orthogonal (S : ReflectionSystem n) {i j : Fin n}
    (hij : S.B i j = 0) :
    reflectionMatrix S.B i * reflectionMatrix S.B j =
      reflectionMatrix S.B j * reflectionMatrix S.B i := by
  have hji : S.B j i = 0 := by
    rw [← S.B_symm.apply j i]
    exact hij
  ext r c
  simp only [mul_apply, reflectionMatrix_apply]
  have expand : ∀ (a b : Fin n),
      (∑ k : Fin n,
        ((if r = k then (1 : ℝ) else 0) - (if r = a then 2 * S.B a k / S.B a a else 0)) *
        ((if k = c then (1 : ℝ) else 0) - (if k = b then 2 * S.B b c / S.B b b else 0))) =
      (if r = c then (1 : ℝ) else 0)
        - (if r = a then 2 * S.B a c / S.B a a else 0)
        - (if r = b then 2 * S.B b c / S.B b b else 0)
        + (if r = a then (2 * S.B a b / S.B a a) * (2 * S.B b c / S.B b b) else 0) := by
    intro a b
    have ht : ∀ k : Fin n,
        ((if r = k then (1 : ℝ) else 0) - (if r = a then 2 * S.B a k / S.B a a else 0)) *
        ((if k = c then (1 : ℝ) else 0) - (if k = b then 2 * S.B b c / S.B b b else 0)) =
        (if k = r then if r = c then (1 : ℝ) else 0 else 0)
          - (if k = r then if r = b then 2 * S.B b c / S.B b b else 0 else 0)
          - (if k = c then if r = a then 2 * S.B a k / S.B a a else 0 else 0)
          + (if k = b then if r = a then (2 * S.B a k / S.B a a) * (2 * S.B b c / S.B b b) else 0 else 0) := by
      intro k
      split_ifs <;> simp_all <;> ring
    simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
    simp only [↓reduceIte]
    ring
  rw [expand i j, expand j i, hij, hji]
  simp only [zero_mul, zero_div, mul_zero, ite_self]
  ring

/-- **Proposition 2.21 (det of generator)**: Every generating reflection `s_i` has
determinant `-1`. -/
theorem det_reflectionMatrix (S : ReflectionSystem n) (i : Fin n) :
    (reflectionMatrix S.B i).det = -1 := by
  rw [Matrix.det_apply]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ r : Fin n, reflectionMatrix S.B i (σ r) r =
      if σ = 1 then -1 else 0 := by
    intro σ
    by_cases hσ : σ = 1
    · subst hσ
      simp only [Equiv.Perm.sign_one, one_smul, Equiv.Perm.coe_one, id_eq, ↓reduceIte]
      have hprod : ∏ r : Fin n, reflectionMatrix S.B i r r =
          ∏ r : Fin n, (if r = i then (-1 : ℝ) else 1) := by
        refine Finset.prod_congr rfl fun r _ => ?_
        by_cases hr : r = i
        · subst hr
          simpa using reflectionMatrix_apply_self S.B (S.B_diag_ne_zero r)
        · simp [reflectionMatrix_apply, hr]
      rw [hprod]
      simp
    · simp only [hσ, ↓reduceIte]
      have hex : ∃ r : Fin n, σ r ≠ r ∧ σ r ≠ i := by
        by_contra hno
        push Not at hno
        apply hσ
        refine Equiv.ext fun r => ?_
        by_cases hrr : σ r = r
        · exact hrr
        · have hri : σ r = i := hno r hrr
          have hne : r ≠ i := fun h => hrr (h ▸ hri)
          have hσi : σ i ≠ i := fun h => hne (σ.injective (hri.trans h.symm))
          have hii : σ i = i := hno i hσi
          exact absurd hii hσi
      rcases hex with ⟨r, hr1, hr2⟩
      have hzero : reflectionMatrix S.B i (σ r) r = 0 := by
        simp [reflectionMatrix_apply, hr1, hr2]
      have hprod0 : ∏ x : Fin n, reflectionMatrix S.B i (σ x) x = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ r) hzero
      rw [hprod0, smul_zero]
  simp_rw [hterm]
  simp

/-- Word evaluation in `W(S)` as a product of generating reflections. -/
noncomputable def wordProd (S : ReflectionSystem n) (w : List (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  (w.map (reflectionMatrix S.B)).prod

lemma det_wordProd (S : ReflectionSystem n) (w : List (Fin n)) :
    (wordProd S w).det = (-1 : ℝ) ^ w.length := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons, Matrix.det_mul, det_reflectionMatrix,
      List.length_cons]
    have hpow : (-1 : ℝ) ^ (t.length + 1) = -1 * (-1 : ℝ) ^ t.length := by ring
    rw [hpow]
    congr 1

/-- **Proposition 2.21**: If a word `w` in the generators `S` has odd length,
then `wordProd S w` has determinant `-1` and cannot be the identity matrix `1`. -/
theorem odd_word_ne_one (S : ReflectionSystem n) {w : List (Fin n)} (hw : Odd w.length) :
    wordProd S w ≠ 1 := by
  intro h
  have hd := congr_arg Matrix.det h
  rw [det_wordProd, Matrix.det_one, hw.neg_one_pow] at hd
  norm_num at hd

end ReflectionSystem
