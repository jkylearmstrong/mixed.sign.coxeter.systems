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

/-- **Proposition 2.28**: If nodes `i` and `j` are not connected in the reflection
diagram `Γ(B)` (`B i j = 0`), then `s_i` and `s_j` commute. -/
theorem reflectionMatrix_comm_of_not_adjacent (S : ReflectionSystem n) (i j : Fin n)
    (hij : S.B i j = 0) :
    reflectionMatrix S.B i * reflectionMatrix S.B j =
      reflectionMatrix S.B j * reflectionMatrix S.B i :=
  reflectionMatrix_comm_of_orthogonal S hij

/-- Quadratic form `v ↦ vᵀ B v` associated to a symmetric matrix `B`. -/
def quadForm (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, v i * B i j * v j

/-- **Definition 2.47**: `S` is *positive definite* (spherical / finite type) if
`vᵀ B v > 0` for all `v ≠ 0`. -/
def IsPosDef (S : ReflectionSystem n) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 → 0 < quadForm S.B v

/-- **Definition 2.48**: `S` is *positive semidefinite degenerate* (affine type) if
`vᵀ B v ≥ 0` for all `v` and `vᵀ B v = 0` for some `v ≠ 0`. -/
def IsPosSemidefDegenerate (S : ReflectionSystem n) : Prop :=
  (∀ v : Fin n → ℝ, 0 ≤ quadForm S.B v) ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ quadForm S.B v = 0

/-- **Definition 2.49**: `S` is *negative definite* if `vᵀ B v < 0` for all `v ≠ 0`. -/
def IsNegDef (S : ReflectionSystem n) : Prop :=
  ∀ v : Fin n → ℝ, v ≠ 0 → quadForm S.B v < 0

/-- **Definition 2.50–2.51**: `S` is *indefinite* (hyperbolic / mixed signature) if
`B` takes both strictly positive and strictly negative values. -/
def IsIndefinite (S : ReflectionSystem n) : Prop :=
  (∃ u : Fin n → ℝ, 0 < quadForm S.B u) ∧ (∃ v : Fin n → ℝ, quadForm S.B v < 0)

theorem isPosDef_not_isNegDef [NeZero n] (S : ReflectionSystem n) (h : S.IsPosDef) :
    ¬ S.IsNegDef := by
  intro hn
  have hne : (fun _ : Fin n => (1 : ℝ)) ≠ 0 := fun h0 => by
    have := congr_fun h0 0; norm_num at this
  have h1 := h _ hne
  have h2 := hn _ hne
  linarith

theorem isPosDef_not_isIndefinite (S : ReflectionSystem n) (h : S.IsPosDef) :
    ¬ S.IsIndefinite := by
  rintro ⟨_, v, hv⟩
  by_cases hv0 : v = 0
  · subst hv0; simp [quadForm] at hv
  · exact absurd (h v hv0) (not_lt_of_gt hv)

/-- **Example 2.52 (a)**: `A₂(+, +)` is positive definite. -/
theorem example_2_52_A2_pp_posDef :
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 2]
    ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < quadForm B v := by
  intro B v hv
  have hsum : quadForm B v = (v 0 - v 1) ^ 2 + v 0 ^ 2 + v 1 ^ 2 := by
    simp [quadForm, B, Fin.sum_univ_two]
    ring
  rw [hsum]
  by_contra hle
  push Not at hle
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0), sq_nonneg (v 1)]
  apply hv
  ext i; fin_cases i <;> assumption

/-- **Example 2.52 (b)**: `A₂(+, -)` is indefinite (hyperbolic). -/
theorem example_2_52_A2_pm_indefinite :
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, -2]
    (∃ u : Fin 2 → ℝ, 0 < quadForm B u) ∧ (∃ v : Fin 2 → ℝ, quadForm B v < 0) := by
  intro B
  refine ⟨⟨![1, 0], ?_⟩, ⟨![0, 1], ?_⟩⟩
  · simp [quadForm, B, Fin.sum_univ_two]
  · simp [quadForm, B, Fin.sum_univ_two]

/-! ### Reflection Group `W(S)` and Root System `Φ = W Π_+` (Definitions 2.9, 2.12–2.13, 2.27) -/

section Roots

/-- **Definition 2.27**: The set `S(B)` of generating reflections of a reflection system `S`. -/
def generatingReflections (S : ReflectionSystem n) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.range (reflectionMatrix S.B)

/-- **Definition 2.27**: The reflection group `W(B)` as the matrix submonoid generated by
`generatingReflections S`. -/
noncomputable def W_group (S : ReflectionSystem n) : Submonoid (Matrix (Fin n) (Fin n) ℝ) :=
  Submonoid.closure (generatingReflections S)

/-- **Faithfulness of the geometric representation**: Every element `w ∈ W_group S`
preserves the bilinear form `S.B` (`wᵀ * B * w = B`). -/
theorem W_group_preserves_B (S : ReflectionSystem n) {w : Matrix (Fin n) (Fin n) ℝ}
    (hw : w ∈ W_group S) :
    wᵀ * S.B * w = S.B := by
  induction hw using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact reflectionMatrix_preserves_B S i
  | one => simp
  | mul x y _ _ ihx ihy =>
    calc (x * y)ᵀ * S.B * (x * y)
        = yᵀ * (xᵀ * S.B * x) * y := by rw [Matrix.transpose_mul]; simp only [mul_assoc]
      _ = yᵀ * S.B * y := by rw [ihx]
      _ = S.B := ihy

/-- **Definition 2.12**: The set of roots `Φ := W Π_+ = {w e_i | w ∈ W}` of a reflection
system `(W, S, B)`. -/
def roots (S : ReflectionSystem n) : Set (Fin n → ℝ) :=
  { v | ∃ (w : List (Fin n)) (i : Fin n), v = wordProd S w *ᵥ Pi.single i (1 : ℝ) }

/-- **Definition 2.13**: The set of positive roots `Φ_+ ⊆ Φ` (nonzero roots with all
coordinates nonnegative). -/
def positiveRoots (S : ReflectionSystem n) : Set (Fin n → ℝ) :=
  { v ∈ S.roots | (∀ j : Fin n, 0 ≤ v j) ∧ v ≠ 0 }

lemma wordProd_append' (S : ReflectionSystem n) (u w : List (Fin n)) :
    wordProd S (u ++ w) = wordProd S u * wordProd S w := by
  simp [wordProd, List.map_append, List.prod_append]

lemma wordProd_reverse_mul' (S : ReflectionSystem n) (w : List (Fin n)) :
    wordProd S w.reverse * wordProd S w = 1 := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [List.reverse_cons, wordProd_append']
    simp only [wordProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      Matrix.mul_one] at ih ⊢
    calc
      (List.map (reflectionMatrix S.B) t.reverse).prod * reflectionMatrix S.B a *
          (reflectionMatrix S.B a * (List.map (reflectionMatrix S.B) t).prod)
        = (List.map (reflectionMatrix S.B) t.reverse).prod *
            (reflectionMatrix S.B a * reflectionMatrix S.B a) *
            (List.map (reflectionMatrix S.B) t).prod := by simp [Matrix.mul_assoc]
      _ = (List.map (reflectionMatrix S.B) t.reverse).prod *
            (List.map (reflectionMatrix S.B) t).prod := by
          rw [reflectionMatrix_mul_self S a, Matrix.mul_one]
      _ = 1 := ih

lemma wordProd_mem_W_group (S : ReflectionSystem n) (w : List (Fin n)) :
    wordProd S w ∈ W_group S := by
  induction w with
  | nil => simp [wordProd]
  | cons a t ih =>
    simp only [wordProd, List.map_cons, List.prod_cons]
    exact (W_group S).mul_mem (Submonoid.subset_closure ⟨a, rfl⟩) ih

lemma reflectionMatrix_mulVec_single_self (S : ReflectionSystem n) (i : Fin n) :
    reflectionMatrix S.B i *ᵥ Pi.single i (1 : ℝ) = -Pi.single i (1 : ℝ) := by
  ext r
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply, Pi.single_apply]
  have hterm : ∀ j : Fin n,
      reflectionMatrix S.B i r j * (if j = i then (1 : ℝ) else 0) =
        if j = i then reflectionMatrix S.B i r j else 0 := by
    intro j; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  by_cases hri : r = i
  · subst hri
    rw [reflectionMatrix_apply_self S.B (S.B_diag_ne_zero r)]
    simp
  · rw [reflectionMatrix_apply]
    simp [hri]

/-- Every simple basis vector `e_i` is a root. -/
theorem simple_mem_roots (S : ReflectionSystem n) (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ S.roots :=
  ⟨[], i, by rw [show wordProd S [] = 1 from by simp [wordProd], Matrix.one_mulVec]⟩

/-- Every simple basis vector `e_i` is a positive root. -/
theorem simple_mem_positiveRoots (S : ReflectionSystem n) (i : Fin n) :
    Pi.single i (1 : ℝ) ∈ S.positiveRoots := by
  refine ⟨simple_mem_roots S i, fun j => ?_, fun h0 => ?_⟩
  · by_cases h : j = i <;> simp [h]
  · have := congr_fun h0 i
    simp at this

/-- The root system `Φ` is `W`-invariant. -/
theorem roots_mulVec_mem (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots)
    (u : List (Fin n)) :
    wordProd S u *ᵥ v ∈ S.roots := by
  rcases hv with ⟨w, i, rfl⟩
  exact ⟨u ++ w, i, by rw [wordProd_append', Matrix.mulVec_mulVec]⟩

/-- The root system `Φ` is closed under negation: `v ∈ Φ → -v ∈ Φ`. -/
theorem roots_neg_mem (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots) :
    -v ∈ S.roots := by
  rcases hv with ⟨w, i, rfl⟩
  refine ⟨w ++ [i], i, ?_⟩
  rw [wordProd_append', ← Matrix.mulVec_mulVec]
  have hsi : wordProd S [i] = reflectionMatrix S.B i := by simp [wordProd]
  rw [hsi, reflectionMatrix_mulVec_single_self, Matrix.mulVec_neg]

/-- Every root is nonzero. -/
theorem roots_ne_zero (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots) :
    v ≠ 0 := by
  rcases hv with ⟨w, i, rfl⟩
  intro h0
  have h1 : wordProd S w.reverse *ᵥ (wordProd S w *ᵥ Pi.single i (1 : ℝ)) = 0 := by
    rw [h0, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, wordProd_reverse_mul', Matrix.one_mulVec] at h1
  have h2 := congr_fun h1 i
  simp at h2

lemma quadForm_eq_dotProduct (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm B v = dotProduct v (B *ᵥ v) := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma quadForm_mulVec (B M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm B (M *ᵥ v) = quadForm (Mᵀ * B * M) v := by
  rw [quadForm_eq_dotProduct, quadForm_eq_dotProduct]
  calc
    (M *ᵥ v) ⬝ᵥ (B *ᵥ (M *ᵥ v))
      = (v ᵥ* Mᵀ) ⬝ᵥ (B *ᵥ (M *ᵥ v)) := by rw [Matrix.vecMul_transpose]
    _ = v ⬝ᵥ (Mᵀ *ᵥ (B *ᵥ (M *ᵥ v))) := (Matrix.dotProduct_mulVec v Mᵀ _).symm
    _ = v ⬝ᵥ ((Mᵀ * B * M) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- Every root `v = w e_i ∈ Φ` has the same quadratic-form value as `e_i`: `Q(w e_i) = B(e_i, e_i)`. -/
theorem roots_quadForm_eq (S : ReflectionSystem n) {v : Fin n → ℝ} (hv : v ∈ S.roots) :
    ∃ i : Fin n, quadForm S.B v = S.B i i := by
  rcases hv with ⟨w, i, rfl⟩
  refine ⟨i, ?_⟩
  rw [quadForm_mulVec, W_group_preserves_B S (wordProd_mem_W_group S w)]
  rw [quadForm_eq_dotProduct]
  simp only [dotProduct, Matrix.mulVec, Pi.single_apply]
  have h1 : ∀ r : Fin n, (if r = i then (1 : ℝ) else 0) *
      ∑ j : Fin n, S.B r j * (if j = i then (1 : ℝ) else 0) =
      if r = i then S.B r i else 0 := by
    intro r
    split_ifs with hr
    · subst hr
      simp [Finset.sum_ite_eq']
    · simp
  rw [Finset.sum_congr rfl fun r _ => h1 r]
  simp

end Roots

/-! ### Definitions 2.1 & 2.3: Bilinear Form, Orthogonality, and Hyperplanes `H_v` -/

section Orthogonality

/-- **Definition 2.1**: The bilinear form `B(u, v) = uᵀ B v` associated with a matrix
`B : Matrix (Fin n) (Fin n) ℝ`. -/
def bilinForm (B : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) : ℝ :=
  dotProduct u (B *ᵥ v)

theorem bilinForm_smul_left (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (u v : Fin n → ℝ) :
    bilinForm B (c • u) v = c * bilinForm B u v := by
  simp [bilinForm, smul_dotProduct, smul_eq_mul]

theorem bilinForm_smul_right (B : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (u v : Fin n → ℝ) :
    bilinForm B u (c • v) = c * bilinForm B u v := by
  simp [bilinForm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem bilinForm_add_left (B : Matrix (Fin n) (Fin n) ℝ) (u₁ u₂ v : Fin n → ℝ) :
    bilinForm B (u₁ + u₂) v = bilinForm B u₁ v + bilinForm B u₂ v := by
  simp [bilinForm, add_dotProduct]

theorem bilinForm_add_right (B : Matrix (Fin n) (Fin n) ℝ) (u v₁ v₂ : Fin n → ℝ) :
    bilinForm B u (v₁ + v₂) = bilinForm B u v₁ + bilinForm B u v₂ := by
  simp [bilinForm, Matrix.mulVec_add, dotProduct_add]

/-- **Definition 2.3**: Vectors `u` and `v` are orthogonal relative to `B` if `B(v, u) = 0`. -/
def IsOrthogonal (B : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) : Prop :=
  bilinForm B u v = 0

/-- **Definition 2.3**: The orthogonal hyperplane `H_v := { u ∈ ℝⁿ | B(v, u) = 0 }`. -/
def orthHyperplane (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : Set (Fin n → ℝ) :=
  { u | IsOrthogonal B v u }

/-- Each generating reflection `s_i` fixes the orthogonal hyperplane `H_{e_i}` pointwise. -/
theorem reflectionMatrix_fixes_orthHyperplane (S : ReflectionSystem n) (i : Fin n)
    {u : Fin n → ℝ} (hu : u ∈ orthHyperplane S.B (Pi.single i (1 : ℝ))) :
    reflectionMatrix S.B i *ᵥ u = u := by
  have hBiu : ∑ j : Fin n, S.B i j * u j = 0 := by
    have h0 : dotProduct (Pi.single i (1 : ℝ)) (S.B *ᵥ u) = 0 := hu
    simpa [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq'] using h0
  ext r
  simp only [Matrix.mulVec, dotProduct]
  by_cases hri : r = i
  · subst hri
    have hrow : ∀ j : Fin n, reflectionMatrix S.B r r j * u j =
        (if r = j then u j else 0) - (2 / S.B r r) * (S.B r j * u j) := by
      intro j
      rw [reflectionMatrix_apply]
      simp only [↓reduceIte]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun j _ => hrow j, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hBiu, mul_zero, sub_zero]
    simp [Finset.sum_ite_eq]
  · have hrow : ∀ j : Fin n, reflectionMatrix S.B i r j * u j =
        if r = j then u j else 0 := by
      intro j
      rw [reflectionMatrix_apply]
      simp [hri]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp [Finset.sum_ite_eq]

end Orthogonality

/-! ### Remark 2.54: Number of Principal Elements -/

section PrincipalElementsCount

/-- The principal element `w_σ = s_{σ(0)} s_{σ(1)} ⋯ s_{σ(n-1)}` associated with a
permutation `σ : Equiv.Perm (Fin n)` of the generators. -/
noncomputable def principalElementOfPerm (S : ReflectionSystem n) (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  wordProd S ((List.finRange n).map σ)

/-- The set of all principal elements of a reflection system `S`. -/
def principalElements (S : ReflectionSystem n) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.range (principalElementOfPerm S)

/-- **Remark 2.54**: A rank-`n` reflection system has between `1` and `n!` principal elements. -/
theorem card_principalElements_bounds (S : ReflectionSystem n) :
    1 ≤ (principalElements S).ncard ∧ (principalElements S).ncard ≤ n.factorial := by
  have hrange : principalElements S = ↑(Finset.univ.image (principalElementOfPerm S)) := by
    ext M
    simp [principalElements]
  rw [hrange, Set.ncard_coe_finset]
  constructor
  · exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ 1)⟩
  · calc
      (Finset.univ.image (principalElementOfPerm S)).card
        ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card := Finset.card_image_le
      _ = n.factorial := by simp [Fintype.card_perm]

end PrincipalElementsCount

end ReflectionSystem
