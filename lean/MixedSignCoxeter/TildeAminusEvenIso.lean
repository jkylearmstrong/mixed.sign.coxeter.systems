/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic
import MixedSignCoxeter.RemarksAndClassical
import MixedSignCoxeter.FiniteReduction

/-!
# Isomorphism `W(~A_{-n}) ≅ W(D_{n+1})` for Every Even `n ≥ 2`

Formalization of the Remark following Theorem 1.6 of:
Johnathon Kyle Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems* (FSU, 2012):
for every even `n = 2 * k ≥ 2`, the negative affine cycle group `W(~A_{-n})` on
`m = n + 1 = 2 * k + 1` vertices is isomorphic to the Weyl group `W(D_{n+1})`.

## Construction
Let `m = 2 * k + 1` (`k ≥ 1`). Define `altDiag m = diag((-1)^i)` and
`conjT m = altDiag m * (1 + shiftMat m)ᵀ`. Its columns are the `D_m` roots
`r_j = (-1)^j (e_j - e_{j+1})` for `0 ≤ j < m - 1` and `r_{m-1} = e_0 + e_{m-1}`.

## Main results
* `conjT_transpose_mul_self`: `(conjT m)ᵀ * conjT m = -cycleNegForm m`.
* `conjT_det_ne_zero`: `(conjT m).det ≠ 0` (via `remark_3_26_det_neg_odd_cycle`).
* `conjT_mul_reflectionMatrix`: `conjT m * s_c = orthRefl (col c (conjT m)) * conjT m`.
* `theorem_1_6_tildeAminus_iso_D`: `W_tildeAminus (2 * k + 1) ≃* W_D (2 * k + 1)` for all `k ≥ 1`.
-/

open Matrix BigOperators

namespace MixedSignCoxeter

section TildeAminusEvenIso

/-- Orthogonal reflection `I - r rᵀ` across the hyperplane orthogonal to a norm-2 vector `r`. -/
def orthRefl {m : ℕ} (r : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) - r i * r j

@[simp]
lemma orthRefl_apply {m : ℕ} (r : Fin m → ℝ) (i j : Fin m) :
    orthRefl r i j = (if i = j then 1 else 0) - r i * r j := rfl

lemma orthRefl_neg {m : ℕ} (r : Fin m → ℝ) : orthRefl (-r) = orthRefl r := by
  ext i j
  simp [orthRefl]

/-- Alternating sign diagonal matrix `diag((-1)^0, (-1)^1, ..., (-1)^{m-1})`. -/
def altDiag (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.diagonal fun i : Fin m => if i.val % 2 = 0 then (1 : ℝ) else -1

lemma altDiag_mul_self (m : ℕ) : altDiag m * altDiag m = 1 := by
  ext i j
  simp only [altDiag, Matrix.diagonal_mul_diagonal, Matrix.one_apply, Matrix.diagonal_apply]
  split_ifs <;> norm_num

lemma altDiag_transpose (m : ℕ) : (altDiag m)ᵀ = altDiag m := by
  simp [altDiag]

/-- Conjugating matrix `T = altDiag m * (1 + shiftMat m)ᵀ` whose columns are the
`D_m` roots `r_0, ..., r_{m-1}` with Gram matrix `-cycleNegForm m`. -/
def conjT (m : ℕ) : Matrix (Fin m) (Fin m) ℝ :=
  altDiag m * (1 + shiftMat m)ᵀ

lemma conjT_transpose_mul_self (m : ℕ) [NeZero m] (hm : 3 ≤ m) :
    (conjT m)ᵀ * conjT m = -cycleNegForm m := by
  calc
    (conjT m)ᵀ * conjT m
      = (1 + shiftMat m) * (altDiag m)ᵀ * (altDiag m * (1 + shiftMat m)ᵀ) := by
          simp [conjT, Matrix.transpose_mul]
    _ = (1 + shiftMat m) * ((altDiag m * altDiag m) * (1 + shiftMat m)ᵀ) := by
          rw [altDiag_transpose]; simp only [mul_assoc]
    _ = (1 + shiftMat m) * (1 + shiftMat m)ᵀ := by
          rw [altDiag_mul_self, one_mul]
    _ = -cycleNegForm m := (neg_cycleNegForm_eq m hm).symm

lemma conjT_det_ne_zero (m : ℕ) [NeZero m] (hm : 3 ≤ m) (hodd : Odd m) :
    (conjT m).det ≠ 0 := by
  intro h0
  have h4 : (-cycleNegForm m).det = 4 := remark_3_26_det_neg_odd_cycle m hm hodd
  have hmul : ((conjT m)ᵀ * conjT m).det = 0 := by
    rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
  rw [conjT_transpose_mul_self m hm, h4] at hmul
  norm_num at hmul

lemma conjT_mul_inv (m : ℕ) [NeZero m] (hm : 3 ≤ m) (hodd : Odd m) :
    conjT m * (conjT m)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (conjT_det_ne_zero m hm hodd))

lemma conjT_inv_mul (m : ℕ) [NeZero m] (hm : 3 ≤ m) (hodd : Odd m) :
    (conjT m)⁻¹ * conjT m = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (conjT_det_ne_zero m hm hodd))

private lemma cycleNegForm_diag {m : ℕ} [NeZero m] (hm : 2 ≤ m) (c : Fin m) :
    cycleNegForm m c c = -2 := by
  simp only [cycleNegForm, Matrix.of_apply, ↓reduceIte]
  have hne : c ≠ c + 1 := by
    intro h
    have hval := congrArg Fin.val h
    have hc := c.isLt
    have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
    rw [Fin.val_add, h1] at hval
    by_cases hlt : c.val + 1 < m
    · rw [Nat.mod_eq_of_lt hlt] at hval; omega
    · have : c.val + 1 = m := by omega
      rw [this, Nat.mod_self] at hval; omega
  have hc1 : (c = c + 1) = False := eq_false hne
  simp [hc1]

lemma conjT_mul_reflectionMatrix (m : ℕ) [NeZero m] (hm : 3 ≤ m) (c : Fin m) :
    conjT m * ReflectionSystem.reflectionMatrix (cycleNegForm m) c =
      orthRefl (fun i => conjT m i c) * conjT m := by
  have hgram : ∀ c j : Fin m,
      ∑ u : Fin m, conjT m u c * conjT m u j = -cycleNegForm m c j := by
    intro c j
    have h := congrFun (congrFun (conjT_transpose_mul_self m hm) c) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply] using h
  have hdiag : cycleNegForm m c c = -2 := cycleNegForm_diag (by omega) c
  ext i j
  simp only [Matrix.mul_apply, ReflectionSystem.reflectionMatrix_apply, orthRefl_apply]
  have hsplit1 : ∀ k : Fin m,
      conjT m i k * ((if k = j then (1 : ℝ) else 0) -
        (if k = c then 2 * cycleNegForm m c j / cycleNegForm m c c else 0)) =
      (if k = j then conjT m i k else 0) -
        (if k = c then conjT m i k * (2 * cycleNegForm m c j / (-2)) else 0) := by
    intro k
    rw [hdiag]
    split_ifs <;> ring
  have hsplit2 : ∀ u : Fin m,
      ((if i = u then (1 : ℝ) else 0) - conjT m i c * conjT m u c) * conjT m u j =
      (if u = i then conjT m u j else 0) - conjT m i c * (conjT m u c * conjT m u j) := by
    intro u
    by_cases hiu : i = u
    · subst hiu; simp; ring
    · have hui : u ≠ i := fun h => hiu h.symm
      simp [hiu, hui, mul_assoc]
  simp_rw [hsplit1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
  simp_rw [hsplit2, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ← Finset.mul_sum, hgram c j]
  simp only [↓reduceIte]
  ring

/-- Standard simple roots of `D_m` (`m ≥ 3`):
`e_j - e_{j+1}` for `0 ≤ j < m - 1`, and `e_{m-2} + e_{m-1}` for `j = m - 1`. -/
def dSimpleRoot (m : ℕ) (j : Fin m) : Fin m → ℝ :=
  fun i =>
    if j.val + 1 < m then
      (if i = j then 1 else 0) - (if i.val = j.val + 1 then 1 else 0)
    else
      (if i.val = m - 2 then 1 else 0) + (if i.val = m - 1 then 1 else 0)

/-- The Coxeter group `W(~A_{-(m-1)})` as a matrix submonoid of `M_m(ℝ)`. -/
def W_tildeAminus (m : ℕ) [NeZero m] : Submonoid (Matrix (Fin m) (Fin m) ℝ) :=
  Submonoid.closure (Set.range (ReflectionSystem.reflectionMatrix (cycleNegForm m)))

/-- The Weyl group `W(D_m)` as a matrix submonoid of `M_m(ℝ)`. -/
def W_D (m : ℕ) : Submonoid (Matrix (Fin m) (Fin m) ℝ) :=
  Submonoid.closure (Set.range fun j : Fin m => orthRefl (dSimpleRoot m j))

private lemma conjT_apply (m : ℕ) (i c : Fin m) :
    conjT m i c =
      (if i.val % 2 = 0 then (1 : ℝ) else -1) *
        ((if c = i then 1 else 0) + (if i.val = (c.val + 1) % m then 1 else 0)) := by
  simp only [conjT, altDiag, Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.add_apply,
    Matrix.one_apply, shiftMat, Matrix.of_apply]

private lemma orthRefl_conjT_col_lt (m : ℕ) (_hm : 3 ≤ m) (c : Fin m) (hc : c.val + 1 < m) :
    orthRefl (fun i => conjT m i c) = orthRefl (dSimpleRoot m c) := by
  have hcol : (fun i => conjT m i c) =
      (if c.val % 2 = 0 then (1 : ℝ) else -1) • dSimpleRoot m c := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, conjT_apply, dSimpleRoot, hc, ↓reduceIte]
    rw [Nat.mod_eq_of_lt hc]
    by_cases hci : c = i
    · subst hci
      simp
    · by_cases hi1 : i.val = c.val + 1
      · have hne : i ≠ c := fun h => by subst h; omega
        simp only [hci, ↓reduceIte, hi1, zero_add]
        rcases Nat.mod_two_eq_zero_or_one c.val with h0 | h1
        · have hmod1 : (c.val + 1) % 2 ≠ 0 := by omega
          simp [h0, hmod1, hne]
        · have hmod2 : (c.val + 1) % 2 = 0 := by omega
          have hc0 : c.val % 2 ≠ 0 := by omega
          simp [hmod2, hc0, hne]
      · have hne : i ≠ c := fun h => hci h.symm
        simp [hci, hne, hi1]
  rw [hcol]
  by_cases h0 : c.val % 2 = 0
  · simp [h0]
  · simp [h0, orthRefl_neg]

private lemma conjT_col_last (m : ℕ) (hm : 3 ≤ m) (hodd : Odd m)
    (c : Fin m) (hc : ¬ c.val + 1 < m) :
    (fun i => conjT m i c) =
      fun i => (if i.val = 0 then (1 : ℝ) else 0) + (if i.val = m - 1 then 1 else 0) := by
  have hcm : c.val = m - 1 := by have := c.isLt; omega
  have hm_even : (m - 1) % 2 = 0 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  ext i
  simp only [conjT_apply]
  have hmod : (c.val + 1) % m = 0 := by rw [hcm, Nat.sub_add_cancel (by omega), Nat.mod_self]
  rw [hmod]
  have hm0 : m - 1 ≠ 0 := by omega
  have hm0' : 0 ≠ m - 1 := by omega
  by_cases hi0 : i.val = 0
  · have hcne : c ≠ i := by intro h; subst h; omega
    simp [hi0, hcne, hm0']
  · by_cases him : i.val = m - 1
    · have hci : c = i := Fin.ext (by omega)
      simp [hci, him, hm_even, hm0]
    · have hci : c ≠ i := by intro h; apply him; rw [← h, hcm]
      simp [hci, hi0, him]

/-- Permutation matrix `permMat σ` with `permMat σ i j = 1` iff `i = σ j`. -/
private def permMat {m : ℕ} (σ : Equiv.Perm (Fin m)) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => if i = σ j then 1 else 0

private lemma permMat_one {m : ℕ} : permMat (1 : Equiv.Perm (Fin m)) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [permMat, Matrix.one_apply, h]

private lemma permMat_mul {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permMat (σ * τ) = permMat σ * permMat τ := by
  ext i j
  simp only [permMat, Matrix.of_apply, Matrix.mul_apply, Equiv.Perm.mul_apply]
  trans ∑ k : Fin m, (if k = τ j then (if i = σ k then (1 : ℝ) else 0) else 0)
  · simp [Finset.sum_ite_eq', Finset.mem_univ]
    rfl
  · refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

private lemma adjSwap_eq_permMat {m : ℕ} (j : Fin m) (hj : j.val + 1 < m) :
    orthRefl (dSimpleRoot m j) = permMat (Equiv.swap j ⟨j.val + 1, hj⟩) := by
  ext r c
  simp only [orthRefl_apply, dSimpleRoot, hj, ↓reduceIte, permMat, Matrix.of_apply]
  set j1 : Fin m := ⟨j.val + 1, hj⟩
  have hjj1 : j ≠ j1 := by intro h; have := congrArg Fin.val h; simp [j1] at this
  have hval : ∀ x : Fin m, (x.val = j.val + 1 ↔ x = j1) := by
    intro x; simp [j1, Fin.ext_iff]
  simp only [hval]
  by_cases hrc : r = c
  · subst hrc
    by_cases hrj : r = j
    · subst hrj; simp [hjj1, Equiv.swap_apply_left]
    · by_cases hrj1 : r = j1
      · subst hrj1; simp [hjj1.symm, Equiv.swap_apply_right]
      · simp [hrj, hrj1, Equiv.swap_apply_of_ne_of_ne hrj hrj1]
  · by_cases hrj : r = j
    · subst hrj
      by_cases hcj1 : c = j1
      · subst hcj1; simp [hjj1, hjj1.symm, Equiv.swap_apply_right]
      · simp [hrc, hcj1, Equiv.swap_apply_def]
        split_ifs <;> simp_all
    · by_cases hrj1 : r = j1
      · subst hrj1
        by_cases hcj : c = j
        · subst hcj; simp [hjj1, hjj1.symm, Equiv.swap_apply_left]
        · simp [hrc, hcj, Equiv.swap_apply_def]
          split_ifs <;> simp_all
      · have hne : r ≠ Equiv.swap j j1 c := by
          intro h
          rw [Equiv.swap_apply_def] at h
          split_ifs at h <;> simp_all
        simp [hrj, hrj1, hrc, hne]

private lemma swap_zero_mem_closure (m : ℕ) (hm : 3 ≤ m)
    (Tsub : Submonoid (Matrix (Fin m) (Fin m) ℝ))
    (h_adj : ∀ j : Fin m, j.val + 1 < m → orthRefl (dSimpleRoot m j) ∈ Tsub)
    (a : ℕ) (ha : a < m) :
    permMat (Equiv.swap ⟨0, by omega⟩ ⟨a, ha⟩) ∈ Tsub := by
  induction a with
  | zero =>
    have h1 : Equiv.swap (⟨0, by omega⟩ : Fin m) ⟨0, ha⟩ = 1 := Equiv.swap_self _
    rw [h1, permMat_one]
    exact Tsub.one_mem
  | succ a ih =>
    have ha_lt : a < m := by omega
    have hih := ih ha_lt
    let z : Fin m := ⟨0, by omega⟩
    let fa : Fin m := ⟨a, ha_lt⟩
    let fa1 : Fin m := ⟨a + 1, ha⟩
    let adj : Equiv.Perm (Fin m) := Equiv.swap fa fa1
    have hadj_mem : permMat adj ∈ Tsub := by
      have := h_adj fa (by simpa [fa] using ha)
      rwa [adjSwap_eq_permMat fa (by simpa [fa] using ha)] at this
    by_cases ha0 : a = 0
    · subst ha0
      have hzf : Equiv.swap z fa1 = adj := rfl
      rwa [hzf]
    · have hconj : Equiv.swap z fa1 = adj * Equiv.swap z fa * adj := by
        ext x
        simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def, adj]
        split_ifs <;> simp_all [z, fa, fa1, Fin.ext_iff]
      rw [hconj, permMat_mul, permMat_mul]
      exact Tsub.mul_mem (Tsub.mul_mem hadj_mem hih) hadj_mem

private lemma permMat_swap_conj_last (m : ℕ) (hm : 3 ≤ m) :
    let σ : Equiv.Perm (Fin m) := Equiv.swap ⟨0, by omega⟩ ⟨m - 2, by omega⟩
    let r_last : Fin m → ℝ := fun i =>
      (if i.val = 0 then 1 else 0) + (if i.val = m - 1 then 1 else 0)
    permMat σ * orthRefl (dSimpleRoot m ⟨m - 1, by omega⟩) * permMat σ = orthRefl r_last := by
  intro σ r_last
  have hσ_left : ∀ (M : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m),
      (permMat σ * M) i j = M (σ i) j := by
    intro M i j
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply]
    have hσ2 : ∀ k : Fin m, (i = σ k ↔ k = σ i) := fun k => by
      constructor <;> intro h
      · subst h; simp [σ]
      · subst h; simp [σ]
    trans ∑ k : Fin m, (if k = σ i then M k j else 0)
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hσ2 k]
      split_ifs <;> simp
    · simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hσ_right : ∀ (M : Matrix (Fin m) (Fin m) ℝ) (i j : Fin m),
      (M * permMat σ) i j = M i (σ j) := by
    intro M i j
    simp only [Matrix.mul_apply, permMat, Matrix.of_apply]
    have hσ2 : ∀ k : Fin m, (k = σ j ↔ σ k = j) := fun k => by
      constructor <;> intro h
      · subst h; simp [σ]
      · subst h; simp [σ]
    trans ∑ k : Fin m, (if k = σ j then M i k else 0)
    · refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs <;> simp
    · simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hσ_mul : ∀ M : Matrix (Fin m) (Fin m) ℝ,
      (permMat σ * M * permMat σ) = Matrix.of fun i j => M (σ i) (σ j) := by
    intro M
    ext i j
    rw [hσ_right (permMat σ * M) i j, hσ_left M i (σ j)]
    rfl
  rw [hσ_mul]
  ext i j
  simp only [Matrix.of_apply, orthRefl_apply, dSimpleRoot, r_last]
  have hnot : ¬ (m - 1 + 1 < m) := by omega
  simp only [hnot, ↓reduceIte]
  have h0 : σ ⟨0, by omega⟩ = ⟨m - 2, by omega⟩ := Equiv.swap_apply_left _ _
  have hm2 : σ ⟨m - 2, by omega⟩ = ⟨0, by omega⟩ := Equiv.swap_apply_right _ _
  have hm1 : σ ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩ := by
    apply Equiv.swap_apply_of_ne_of_ne <;> simp [Fin.ext_iff] <;> omega
  have h_iff_0 : ∀ x : Fin m, ((σ x).val = m - 2 ↔ x.val = 0) := fun x => by
    constructor <;> intro hx
    · have : σ x = ⟨m - 2, by omega⟩ := Fin.ext hx
      have : x = ⟨0, by omega⟩ := by rw [← hm2, ← this]; simp [σ]
      exact congrArg Fin.val this
    · have : x = ⟨0, by omega⟩ := Fin.ext hx
      rw [this, h0]
  have h_iff_m1 : ∀ x : Fin m, ((σ x).val = m - 1 ↔ x.val = m - 1) := fun x => by
    constructor <;> intro hx
    · have : σ x = ⟨m - 1, by omega⟩ := Fin.ext hx
      have : x = ⟨m - 1, by omega⟩ := by rw [← hm1, ← this]; simp [σ]
      exact congrArg Fin.val this
    · have : x = ⟨m - 1, by omega⟩ := Fin.ext hx
      rw [this, hm1]
  have hij : (σ i = σ j) = (i = j) := propext σ.injective.eq_iff
  simp only [h_iff_0, h_iff_m1, hij]

private lemma permMat_swap_sq {m : ℕ} (a b : Fin m) :
    permMat (Equiv.swap a b) * permMat (Equiv.swap a b) = 1 := by
  rw [← permMat_mul, Equiv.swap_mul_self, permMat_one]

/-- **Theorem 1.6 Remark**: For every even `n = 2 * k ≥ 2` (so `m = n + 1 = 2 * k + 1` is odd),
the negative affine cycle group `W(~A_{-n})` is isomorphic to the Weyl group `W(D_{n+1})`. -/
noncomputable def theorem_1_6_tildeAminus_iso_D (k : ℕ) (hk : 1 ≤ k) :
    W_tildeAminus (2 * k + 1) ≃* W_D (2 * k + 1) := by
  set m := 2 * k + 1
  have hm : 3 ≤ m := by omega
  have hodd : Odd m := ⟨k, by omega⟩
  let T := conjT m
  have hTTinv : T * T⁻¹ = 1 := conjT_mul_inv m hm hodd
  have hTinvT : T⁻¹ * T = 1 := conjT_inv_mul m hm hodd
  let σ : Equiv.Perm (Fin m) := Equiv.swap ⟨0, by omega⟩ ⟨m - 2, by omega⟩
  have hP_in_WD : permMat σ ∈ W_D m :=
    swap_zero_mem_closure m hm (W_D m)
      (fun j _ => Submonoid.subset_closure ⟨j, rfl⟩) (m - 2) (by omega)
  let W_img : Submonoid (Matrix (Fin m) (Fin m) ℝ) :=
    Submonoid.closure (Set.range fun c : Fin m => orthRefl (fun i => T i c))
  have h_adj_in_Wimg : ∀ j : Fin m, j.val + 1 < m → orthRefl (dSimpleRoot m j) ∈ W_img := by
    intro j hj
    rw [← orthRefl_conjT_col_lt m hm j hj]
    exact Submonoid.subset_closure ⟨j, rfl⟩
  have hP_in_Wimg : permMat σ ∈ W_img :=
    swap_zero_mem_closure m hm W_img h_adj_in_Wimg (m - 2) (by omega)
  have hWimg_eq_WD : W_img = W_D m := by
    apply le_antisymm
    · rw [Submonoid.closure_le]
      rintro _ ⟨c, rfl⟩
      by_cases hc : c.val + 1 < m
      · dsimp only
        rw [orthRefl_conjT_col_lt m hm c hc]
        exact Submonoid.subset_closure ⟨c, rfl⟩
      · dsimp only
        rw [conjT_col_last m hm hodd c hc, ← permMat_swap_conj_last m hm]
        exact (W_D m).mul_mem ((W_D m).mul_mem hP_in_WD
          (Submonoid.subset_closure ⟨⟨m - 1, by omega⟩, rfl⟩)) hP_in_WD
    · unfold W_D
      rw [Submonoid.closure_le]
      rintro _ ⟨j, rfl⟩
      by_cases hj : j.val + 1 < m
      · exact h_adj_in_Wimg j hj
      · have hjm : j = ⟨m - 1, by omega⟩ :=
          Fin.ext (by have := j.isLt; change j.val = m - 1; omega)
        rw [hjm]
        have hconj_last :
            orthRefl (dSimpleRoot m ⟨m - 1, by omega⟩) =
              permMat σ * orthRefl (fun i => T i ⟨m - 1, by omega⟩) * permMat σ := by
          have hlast_not : ¬ ((⟨m - 1, by omega⟩ : Fin m).val + 1 < m) :=
            show ¬ (m - 1 + 1 < m) from by omega
          have hcol := conjT_col_last m hm hodd ⟨m - 1, by omega⟩ hlast_not
          have hswap := permMat_swap_conj_last m hm
          dsimp only at hswap
          rw [hcol, ← hswap]
          have hsq : permMat σ * permMat σ = 1 := permMat_swap_sq _ _
          calc orthRefl (dSimpleRoot m ⟨m - 1, by omega⟩)
              = 1 * orthRefl (dSimpleRoot m ⟨m - 1, by omega⟩) * 1 := by simp
            _ = (permMat σ * permMat σ) * orthRefl (dSimpleRoot m ⟨m - 1, by omega⟩) *
                  (permMat σ * permMat σ) := by rw [hsq]
            _ = permMat σ * (permMat σ * orthRefl (dSimpleRoot m ⟨m - 1, by omega⟩) * permMat σ) *
                  permMat σ := by simp only [mul_assoc]
        dsimp only
        rw [hconj_last]
        exact W_img.mul_mem (W_img.mul_mem hP_in_Wimg
          (Submonoid.subset_closure ⟨⟨m - 1, by omega⟩, rfl⟩)) hP_in_Wimg
  have hconj_gen : ∀ c : Fin m,
      T * ReflectionSystem.reflectionMatrix (cycleNegForm m) c * T⁻¹ =
        orthRefl (fun i => T i c) := by
    intro c
    rw [conjT_mul_reflectionMatrix m hm c, mul_assoc, hTTinv, mul_one]
  have hconj_mem : ∀ M ∈ W_tildeAminus m, T * M * T⁻¹ ∈ W_D m := by
    intro M hM
    induction hM using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hconj_gen c, ← hWimg_eq_WD]
      exact Submonoid.subset_closure ⟨c, rfl⟩
    | one =>
      rw [mul_one, hTTinv]
      exact (W_D m).one_mem
    | mul x y _ _ ihx ihy =>
      have hmul : T * (x * y) * T⁻¹ = (T * x * T⁻¹) * (T * y * T⁻¹) := by
        calc T * (x * y) * T⁻¹
            = T * (x * (1 * y)) * T⁻¹ := by rw [one_mul]
          _ = T * (x * ((T⁻¹ * T) * y)) * T⁻¹ := by rw [hTinvT]
          _ = (T * x * T⁻¹) * (T * y * T⁻¹) := by simp only [mul_assoc]
      rw [hmul]
      exact (W_D m).mul_mem ihx ihy
  have hinv_conj_gen : ∀ c : Fin m,
      T⁻¹ * orthRefl (fun i => T i c) * T =
        ReflectionSystem.reflectionMatrix (cycleNegForm m) c := by
    intro c
    rw [← hconj_gen c]
    calc T⁻¹ * (T * ReflectionSystem.reflectionMatrix (cycleNegForm m) c * T⁻¹) * T
        = (T⁻¹ * T) * ReflectionSystem.reflectionMatrix (cycleNegForm m) c * (T⁻¹ * T) := by
            simp only [mul_assoc]
      _ = ReflectionSystem.reflectionMatrix (cycleNegForm m) c := by
            rw [hTinvT, one_mul, mul_one]
  have hinv_conj_mem : ∀ N ∈ W_D m, T⁻¹ * N * T ∈ W_tildeAminus m := by
    intro N hN
    rw [← hWimg_eq_WD] at hN
    induction hN using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hinv_conj_gen c]
      exact Submonoid.subset_closure ⟨c, rfl⟩
    | one =>
      rw [mul_one, hTinvT]
      exact (W_tildeAminus m).one_mem
    | mul x y _ _ ihx ihy =>
      have hmul : T⁻¹ * (x * y) * T = (T⁻¹ * x * T) * (T⁻¹ * y * T) := by
        calc T⁻¹ * (x * y) * T
            = T⁻¹ * (x * (1 * y)) * T := by rw [one_mul]
          _ = T⁻¹ * (x * ((T * T⁻¹) * y)) * T := by rw [hTTinv]
          _ = (T⁻¹ * x * T) * (T⁻¹ * y * T) := by simp only [mul_assoc]
      rw [hmul]
      exact (W_tildeAminus m).mul_mem ihx ihy
  exact
    { toFun := fun ⟨M, hM⟩ => ⟨T * M * T⁻¹, hconj_mem M hM⟩
      invFun := fun ⟨N, hN⟩ => ⟨T⁻¹ * N * T, hinv_conj_mem N hN⟩
      left_inv := fun ⟨M, hM⟩ => by
        ext1
        calc T⁻¹ * (T * M * T⁻¹) * T
            = (T⁻¹ * T) * M * (T⁻¹ * T) := by simp only [mul_assoc]
          _ = M := by rw [hTinvT, one_mul, mul_one]
      right_inv := fun ⟨N, hN⟩ => by
        ext1
        calc T * (T⁻¹ * N * T) * T⁻¹
            = (T * T⁻¹) * N * (T * T⁻¹) := by simp only [mul_assoc]
          _ = N := by rw [hTTinv, one_mul, mul_one]
      map_mul' := fun ⟨x, hx⟩ ⟨y, hy⟩ => by
        ext1
        calc T * (x * y) * T⁻¹
            = T * (x * (1 * y)) * T⁻¹ := by rw [one_mul]
          _ = T * (x * ((T⁻¹ * T) * y)) * T⁻¹ := by rw [hTinvT]
          _ = (T * x * T⁻¹) * (T * y * T⁻¹) := by simp only [mul_assoc] }

end TildeAminusEvenIso

/-! ### Appendix D: The 16 GAP Relators for `W(~A_{-4})` -/

section AppendixD

/-- The five integer generating matrices `s₁, ..., s₅` of `W(~A_{-4})` from Appendix D. -/
def appendixDGen : Fin 5 → Matrix (Fin 5) (Fin 5) ℤ
  | 0 => !![-1, -1, 0, 0, -1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 1 => !![1, 0, 0, 0, 0; -1, -1, -1, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 2 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, -1, -1, -1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]
  | 3 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, -1, -1, -1; 0, 0, 0, 0, 1]
  | 4 => !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; -1, 0, 0, -1, -1]

/-- Word evaluation in `appendixDGen`. -/
def appendixDWord (w : List (Fin 5)) : Matrix (Fin 5) (Fin 5) ℤ :=
  (w.map appendixDGen).prod

/-- The 16 GAP relators from Appendix D (`f₁..f₅ ↦ 0..4`). -/
def appendixDRelators : List (List (Fin 5)) :=
  [ [0, 0], [1, 1], [2, 2], [3, 3], [4, 4],
    [0, 2, 0, 2], [0, 3, 0, 3], [1, 3, 1, 3], [1, 4, 1, 4], [2, 4, 2, 4],
    [0, 1, 0, 1, 0, 1], [1, 2, 1, 2, 1, 2], [2, 3, 2, 3, 2, 3],
    [0, 4, 0, 4, 0, 4], [3, 4, 3, 4, 3, 4],
    [2, 0, 3, 4, 0, 1, 3, 2, 3, 1, 0, 4, 3, 2, 0, 1] ]

/-- **Appendix D**: All 16 GAP relators evaluate to the identity on the `W(~A_{-4})` matrices. -/
theorem appendixD_relators_hold :
    ∀ r ∈ appendixDRelators, appendixDWord r = 1 := by
  decide

/-- The integer generators `appendixDGen` agree with `reflectionMatrix (cycleNegForm 5)` over `ℝ`. -/
theorem appendixDGen_eq_reflectionMatrix (c : Fin 5) :
    (appendixDGen c).map (Int.cast : ℤ → ℝ) =
      ReflectionSystem.reflectionMatrix (cycleNegForm 5) c := by
  fin_cases c <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        (simp [appendixDGen, ReflectionSystem.reflectionMatrix, cycleNegForm]; try norm_num)

end AppendixD

/-! ### Theorem 1.6 (Odd `n`): `W(~A_{-n})` is Infinite for Every Odd `n ≥ 3` -/

section TildeAminusOddInfinite

private def cycleNegSystem (m : ℕ) [NeZero m] (hm : 2 ≤ m) : ReflectionSystem m where
  B := cycleNegForm m
  B_symm := by
    ext i j
    simp only [transpose_apply, cycleNegForm, of_apply]
    by_cases hij : i = j
    · subst hij; simp [eq_comm]
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji, eq_comm]
      ring
  B_diag_ne_zero := by
    intro i
    simp only [cycleNegForm, of_apply, ↓reduceIte]
    have hne1 : i ≠ i + 1 := by
      intro h
      have hval := congrArg Fin.val h
      have hi := i.isLt
      have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, h1] at hval
      by_cases hlt : i.val + 1 < m
      · rw [Nat.mod_eq_of_lt hlt] at hval; omega
      · have : i.val + 1 = m := by omega
        rw [this, Nat.mod_self] at hval; omega
    simp [hne1]

private lemma cycleNegSystem_isConnected (m : ℕ) [NeZero m] (hm : 3 ≤ m) :
    (cycleNegSystem m (by omega)).IsConnected := by
  intro i j
  have hstep : ∀ u : Fin m, (cycleNegSystem m (by omega)).B u (u + 1) ≠ 0 := by
    intro u
    simp only [cycleNegSystem, cycleNegForm, of_apply]
    have hne : u ≠ u + 1 := by
      intro h
      have hval := congrArg Fin.val h
      have hu := u.isLt
      have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, h1] at hval
      by_cases hlt : u.val + 1 < m
      · rw [Nat.mod_eq_of_lt hlt] at hval; omega
      · have : u.val + 1 = m := by omega
        rw [this, Nat.mod_self] at hval; omega
    have hne2 : u ≠ u + 1 + 1 := by
      intro h
      have h20 : (1 : Fin m) + 1 = 0 := by
        have hadd : u + (1 + 1) = u + 0 := by rw [← add_assoc, ← h, add_zero]
        exact add_left_cancel hadd
      have hv := congrArg Fin.val h20
      have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
      rw [Fin.val_add, h1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at hv
      omega
    have hc1 : (u = u + 1) = False := eq_false hne
    have hc2 : (u = u + 1 + 1) = False := eq_false hne2
    simp [hc1, hc2]
  have hreach_zero : ∀ k : ℕ, ∀ hk : k < m,
      Relation.ReflTransGen (fun u v => (cycleNegSystem m (by omega)).B u v ≠ 0)
        ⟨0, by omega⟩ ⟨k, hk⟩ := by
    intro k hk
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
      have hk0 : k < m := by omega
      refine (ih hk0).tail ?_
      have hsucc : (⟨k, hk0⟩ : Fin m) + 1 = ⟨k + 1, hk⟩ := by
        ext
        have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, h1, Fin.val_mk, Fin.val_mk, Nat.mod_eq_of_lt hk]
      rw [← hsucc]
      exact hstep ⟨k, hk0⟩
  have hsymm : ∀ a b : Fin m,
      Relation.ReflTransGen (fun u v => (cycleNegSystem m (by omega)).B u v ≠ 0) a b →
      Relation.ReflTransGen (fun u v => (cycleNegSystem m (by omega)).B u v ≠ 0) b a := by
    intro a b hab
    induction hab with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      have hcb : (cycleNegSystem m (by omega)).B c b ≠ 0 := by
        have hs := congrFun (congrFun (cycleNegSystem m (by omega)).B_symm c) b
        simpa using hs ▸ hbc
      exact Relation.ReflTransGen.head hcb ih
  have hi := hsymm ⟨0, by omega⟩ i (hreach_zero i.val i.isLt)
  have hj := hreach_zero j.val j.isLt
  exact hi.trans hj

/-- **Theorem 1.6 (Odd `n`)**: For every odd `n = 2 * k + 1 ≥ 3` (so `m = n + 1 = 2 * (k + 1)`
is even), the negative affine cycle group `W(~A_{-n})` is infinite. -/
theorem theorem_1_6_tildeAminus_odd_infinite (k : ℕ) (hk : 1 ≤ k) :
    ¬ Finite (W_tildeAminus (2 * k + 2)) := by
  set m := 2 * k + 2
  have hm : 3 ≤ m := by omega
  intro hfin
  have hfin' : Finite (ReflectionSystem.W_group (cycleNegSystem m (by omega))) := hfin
  have hdef := ReflectionSystem.finite_connected_isDefinite (cycleNegSystem m (by omega))
    (by omega) (cycleNegSystem_isConnected m hm) hfin'
  let v : Fin m → ℝ := fun i => (-1 : ℝ) ^ i.val
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h ⟨0, by omega⟩
    simp [v] at h0
  have hquad_zero : ReflectionSystem.quadForm (cycleNegForm m) v = 0 := by
    have hrow : ∀ i : Fin m, ∑ j : Fin m, cycleNegForm m i j * v j = 0 := by
      intro i
      simp only [cycleNegForm, of_apply]
      have hsplit : ∀ j : Fin m,
          (-(if i = j then (2 : ℝ) else 0) - (if j = i + 1 then 1 else 0) -
            (if i = j + 1 then 1 else 0)) * v j =
          (if j = i then -2 * v j else 0) - (if j = i + 1 then v j else 0) -
            (if j = i - 1 then v j else 0) := by
        intro j
        have heq1 : (i = j) ↔ (j = i) := eq_comm
        have heq2 : (i = j + 1) ↔ (j = i - 1) := by
          constructor <;> intro h <;> simp [h]
        simp only [heq1, heq2]
        split_ifs <;> ring
      simp_rw [hsplit, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ]
      simp only [↓reduceIte]
      have hv_succ : v (i + 1) = -v i := by
        simp only [v]
        have hi := i.isLt
        have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
        rw [Fin.val_add, h1]
        by_cases hlt : i.val + 1 < m
        · rw [Nat.mod_eq_of_lt hlt, pow_succ]; ring
        · have him : i.val = m - 1 := by omega
          rw [him, show m - 1 + 1 = m from by omega, Nat.mod_self, pow_zero]
          have hodd : Odd (m - 1) := ⟨k, by omega⟩
          rw [hodd.neg_one_pow]
          norm_num
      have hv_pred : v (i - 1) = -v i := by
        have h := hv_succ
        have hp : (i - 1) + 1 = i := sub_add_cancel i 1
        have h2 : v ((i - 1) + 1) = -v (i - 1) := by
          simp only [v]
          have hlt' : (i - 1).val < m := (i - 1).isLt
          have h1 : (1 : Fin m).val = 1 := by rw [Fin.val_one']; exact Nat.mod_eq_of_lt (by omega)
          rw [Fin.val_add, h1]
          by_cases hlt : (i - 1).val + 1 < m
          · rw [Nat.mod_eq_of_lt hlt, pow_succ]; ring
          · have him : (i - 1).val = m - 1 := by omega
            rw [him, show m - 1 + 1 = m from by omega, Nat.mod_self, pow_zero]
            have hodd : Odd (m - 1) := ⟨k, by omega⟩
            rw [hodd.neg_one_pow]
            norm_num
        rw [hp] at h2
        linarith
      rw [hv_succ, hv_pred]
      ring
    unfold ReflectionSystem.quadForm
    calc ∑ i : Fin m, ∑ j : Fin m, v i * cycleNegForm m i j * v j
        = ∑ i : Fin m, v i * ∑ j : Fin m, cycleNegForm m i j * v j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := by simp [hrow]
  rcases hdef with hpos | hneg
  · have := hpos v hv
    change 0 < ReflectionSystem.quadForm (cycleNegForm m) v at this
    linarith
  · have := hneg v hv
    change ReflectionSystem.quadForm (cycleNegForm m) v < 0 at this
    linarith

end TildeAminusOddInfinite

end MixedSignCoxeter
