
import Mathlib

open Function
open Set
open TopologicalSpace

def arithprog (a b : ℤ) : Set ℤ := { x : ℤ | b ∣ (x - a) }

theorem ap {b d : ℤ} {a c : ℤ} (hb : b ≠ 0) (hd : d ≠ 0)
  (h : ∃ x, x ∈ arithprog a b ∩ arithprog c d) :
  ∃ e f, f ≠ 0 ∧ arithprog a b ∩ arithprog c d = arithprog e f := by
    rcases h with ⟨x0, hx0⟩
    rcases (Set.mem_inter_iff _ _ _).mp hx0 with ⟨hx0a, hx0c⟩
    have hne : lcm b d ≠ 0 := by
      simp [lcm_eq_zero_iff, hb, hd]
    let f : ℤ  := lcm b d
    have hf : f ≠ 0 := by
      exact hne
    let e : ℤ := x0
    have eqcap : arithprog a b ∩ arithprog c d = arithprog e f := by
      ext x
      constructor
      intro hx
      rcases (Set.mem_inter_iff _ _ _).mp hx with ⟨hxab, hxcd⟩
      have hb' : b ∣ (x - x0) := by
        have h := Int.dvd_sub hxab hx0a
        simpa [arithprog] using h
      have hd' : d ∣ (x - x0) := by
        have h := Int.dvd_sub hxcd hx0c
        simpa [arithprog] using h
      simp [arithprog, e, f]
      rw [lcm_dvd_iff]
      exact ⟨hb', hd'⟩
      intro hx
      have hf' : f ∣ (x - x0) := hx
      have hb' : b ∣ (x - x0) :=
      (lcm_dvd_iff.mp hf').1
      have hd' : d ∣ (x - x0) :=
      (lcm_dvd_iff.mp hf').2
      simp [Set.mem_inter_iff]
      constructor
      have h := Int.dvd_add hb' hx0a
      ring_nf at h
      simpa [arithprog]
      have h := Int.dvd_add hd' hx0c
      ring_nf at h
      simpa [arithprog]
    refine ⟨e, f, hf, eqcap⟩


lemma arithprog_shift_subset_compl {a b k : ℤ}
  (hb : b ≠ 0) (hk : k ∈ Set.Icc (1 : ℤ) ((Int.natAbs b : ℤ) - 1)) : arithprog (a + k) b ⊆ (arithprog a b)ᶜ := by
  intro x hx
  by_contra hx'
  have hx0 : x ∈ arithprog a b := by
    simpa using hx'

  set d : ℤ := (Int.natAbs b : ℤ)

  have h1 : d ∣ (x - a) := by
    simpa [arithprog, d] using hx0

  have h2 : d ∣ (x - (a + k)) := by
    simpa [arithprog, d] using hx

  have hkdiv : d ∣ k := by
    have : d ∣ (x - a) - (x - (a + k)) :=
      dvd_sub h1 h2
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

  have hkpos : 0 < k := by
    have : (1 : ℤ) ≤ k := hk.1
    linarith

  have hklt : k < d := by
    have : k ≤ d - 1 := hk.2
    linarith

  have hdpos : 0 < d := by
    have : 0 < Int.natAbs b := (Int.natAbs_pos).mpr hb
    simpa [d] using this

  have : k = 0 := by
    rcases hkdiv with ⟨m, hm⟩
    have : |m| = 0 := by
      have hkabs : |k| < d := by
        have : k < d := hklt
        have hkpos' : 0 ≤ k := le_of_lt hkpos
        simpa [abs_of_nonneg hkpos'] using this
      have : d * |m| < d := by
        simpa [hm, abs_mul, abs_of_nonneg (le_of_lt hdpos)] using hkabs
      have : |m| = 0 := by
        have : |m| < 1 := by
          have : d * |m| < d * 1 := by
            simpa using this
          have hdpos' : 0 < d := hdpos
          exact (mul_lt_mul_left hdpos').mp this
        simpa using (Int.abs_lt_one_iff.mp this)
      exact this
    have hm0 : m = 0 := by
      simpa using abs_eq_zero.mp this
    simpa [hm, hm0]

  exact lt_irrefl (0 : ℤ) (by simpa [this] using hkpos)

lemma exists_prime_dvd_int
  (x : ℤ) (hx1 : x ≠ 1) (hx2 : x ≠ -1) : ∃ p : ℕ, Nat.Prime p ∧ (p : ℤ) ∣ x := by
  have hnatAbs_ne_one : Int.natAbs x ≠ 1 := by
    intro h
    have hx : x = 1 ∨ x = -1 := by
      simpa [Int.natAbs_eq_iff] using h
    cases hx with
    | inl h1 => exact hx1 h1
    | inr h2 => exact hx2 h2

  rcases Nat.exists_prime_and_dvd hnatAbs_ne_one with ⟨p, hp, hpdvd⟩

  refine ⟨p, hp, ?_⟩

  have : (p : ℤ) ∣ Int.natAbs x := by
    exact_mod_cast hpdvd
  exact (Int.dvd_natAbs).mp this


theorem Z_minus_pm_one_eq_union_prime_arithprog :
  {x : ℤ | x ≠ 1 ∧ x ≠ -1} = ⋃ p : ℕ, ⋃ (_ : Nat.Prime p), arithprog 0 (p : ℤ) := by
  ext x
  constructor
  ·
    intro hx
    rcases hx with ⟨hx1, hx2⟩
    rcases exists_prime_dvd_int x hx1 hx2 with ⟨p, hp, hpdvd⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨p, Set.mem_iUnion.mpr ?_⟩
    refine ⟨hp, ?_⟩
    dsimp [arithprog]
    simpa using hpdvd

  ·
    intro hx
    rcases Set.mem_iUnion.mp hx with ⟨p, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hp, hx⟩
    dsimp [arithprog] at hx
    constructor
    · intro h
      have : (p : ℤ) ∣ 1 := by simpa [h] using hx
      have hp' : p = 1 := by
        exact Nat.eq_one_of_dvd_one (by exact_mod_cast this)
      exact hp.ne_one hp'
    · intro h
      have : (p : ℤ) ∣ 1 := by simpa [h] using hx
      have hp' : p = 1 := by
        exact Nat.eq_one_of_dvd_one (by exact_mod_cast this)
      exact hp.ne_one hp'

lemma arithprog_infinite {a b : ℤ} (hb : b ≠ 0) :
  Set.Infinite (arithprog a b) := by
  classical
  have h_inj : Function.Injective (fun n : ℤ => a + n*b) := by
    intro m n h
    have h' : m * b = n * b := by
      exact add_left_cancel h


    have hmul : b * (m - n) = 0 := by
      have hsub : m * b - n * b = 0 := sub_eq_zero.mpr h'
      have hsub' : (m - n) * b = 0 := by
        simpa [sub_mul] using hsub
      simpa [mul_comm, mul_left_comm, mul_assoc] using hsub'

    have hmn : m - n = 0 := by
      rcases mul_eq_zero.mp hmul with hb0 | hmn
      · exact (hb hb0).elim
      · exact hmn
    linarith

  have h_range_inf :
      Set.Infinite (Set.range (fun n : ℤ => a + n*b)) :=
    Set.infinite_range_of_injective h_inj

  have h_subset : Set.range (fun n : ℤ => a + n*b) ⊆ arithprog a b := by
      intro x hx
      rcases hx with ⟨n, rfl⟩
      dsimp [arithprog]
      refine ⟨n, ?_⟩
      ring

  exact h_range_inf.mono h_subset

lemma arithprog_inter_contains
  {a₁ b₁ a₂ b₂ x : ℤ} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hx₁ : x ∈ arithprog a₁ b₁) (hx₂ : x ∈ arithprog a₂ b₂) :
  ∃ b : ℤ, b ≠ 0 ∧
    arithprog x b ⊆ arithprog a₁ b₁ ∩ arithprog a₂ b₂ := by
  refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
  intro y hy
  constructor
  ·
    dsimp [arithprog] at *
    have h₁ : b₁ ∣ (y - x) := by
      have : b₁ ∣ b₁ * b₂ := ⟨b₂, rfl⟩
      exact dvd_trans this hy
    have h₂ : b₁ ∣ (x - a₁) := hx₁
    have : b₁ ∣ (y - a₁) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using dvd_add h₁ h₂
    exact this
  ·
    dsimp [arithprog] at *
    have h₁ : b₂ ∣ (y - x) := by
      have : b₂ ∣ b₁ * b₂ := ⟨b₁, by ring⟩
      exact dvd_trans this hy
    have h₂ : b₂ ∣ (x - a₂) := hx₂
    have : b₂ ∣ (y - a₂) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using dvd_add h₁ h₂
    exact this


def arithprog_basis : Set (Set ℤ) :=
  { s | ∃ a b, b ≠ 0 ∧ s = arithprog a b }


instance : TopologicalSpace ℤ := TopologicalSpace.generateFrom arithprog_basis


lemma arithprog_isOpen_basic {a b : ℤ} (hb : b ≠ 0) : IsOpen (arithprog a b) := by
  apply TopologicalSpace.GenerateOpen.basic
  use a, b, hb




theorem is_basis_arithprog : IsTopologicalBasis arithprog_basis := by
  refine IsTopologicalBasis.mk ?_ ?_ ?_

  · intro t₁ ht₁ t₂ ht₂ x hx
    rcases ht₁ with ⟨a₁, b₁, hb₁, rfl⟩
    rcases ht₂ with ⟨a₂, b₂, hb₂, rfl⟩
    rcases arithprog_inter_contains hb₁ hb₂ hx.1 hx.2 with ⟨b, hb, hsub⟩
    use arithprog x b
    constructor
    ·
      refine ⟨x, b, hb, rfl⟩
    ·
      exact ⟨by simp [arithprog], hsub⟩


  · ext x
    simp
    use arithprog x 1
    constructor
    ·

      refine ⟨x, 1, one_ne_zero, rfl⟩
    ·
      simp [arithprog]

  ·
    rfl


theorem isOpen_iff_furstenberg {U : Set ℤ} :
  IsOpen U ↔ ∀ x ∈ U, ∃ a b : ℤ, b ≠ 0 ∧ x ∈ arithprog a b ∧ arithprog a b ⊆ U := by
  rw [is_basis_arithprog.isOpen_iff]
  constructor
  · -- 左 → 右
    intro h x hx
    rcases h x hx with ⟨S, ⟨a, b, hb, rfl⟩, hxS, hSU⟩
    exact ⟨a, b, hb, hxS, hSU⟩
  · -- 右 → 左
    intro h x hx
    rcases h x hx with ⟨a, b, hb, hxa, hsub⟩
    exact ⟨arithprog a b, ⟨a, b, hb, rfl⟩, hxa, hsub⟩

lemma arithprog_isOpen_new {a b : ℤ} (hb : b ≠ 0) : IsOpen (arithprog a b) := by
  apply TopologicalSpace.GenerateOpen.basic
  use a, b, hb


theorem Furstenberg_open_infinite
  {U : Set ℤ} (hopen : IsOpen U) (hne : U.Nonempty) :
  Set.Infinite U :=
by
  rcases hne with ⟨x, hx⟩

  rw [is_basis_arithprog.isOpen_iff] at hopen


  rcases hopen x hx with ⟨S, ⟨a, b, hb, rfl⟩, hxS, hsub⟩

  exact (arithprog_infinite hb).mono hsub

lemma arithprog_compl_subset {a b : ℤ} (hb : b ≠ 0) :
  (arithprog a b)ᶜ ⊆  ⋃ k ∈ Set.Icc (1 : ℤ) ((Int.natAbs b : ℤ) - 1), arithprog (a + k) b := by
    intro x hx
    have hxnot : ¬ ((Int.natAbs b : ℤ) ∣ (x - a)) := by
      simpa [arithprog] using hx
    let k : ℤ := (x - a) % (Int.natAbs b)
    have hk0 : k ≠ 0 := by
      intro hk
      have this : (Int.natAbs b : ℤ) ∣ (x - a) := by
        exact Int.dvd_of_emod_eq_zero (by simpa [k] using hk)
      exact hxnot this

    have hk_nonneg : 0 ≤ k := by
      have hbabs_ne0 : (Int.natAbs b : ℤ) ≠ 0 := by
        have : (Int.natAbs b : ℕ) ≠ 0 := Nat.ne_of_gt (Int.natAbs_pos.mpr hb)
        exact_mod_cast this
      simpa [k] using Int.emod_nonneg (x - a) hbabs_ne0

    have hk_lt : k < Int.natAbs b := by
      have hbposZ : (0 : ℤ) < (Int.natAbs b : ℤ) := by
        exact_mod_cast (Int.natAbs_pos.mpr hb)
      simpa [k] using Int.emod_lt_of_pos (x - a) hbposZ

    have hk_pos : 1 ≤ k := by
      have : 0 < k := by
        exact lt_of_le_of_ne hk_nonneg (Ne.symm hk0)
      exact Int.add_one_le_iff.mpr this
    have hk_le : k ≤ Int.natAbs b - 1 := by
      exact Int.le_sub_one_of_lt hk_lt
    have hk_mem : k ∈ (Set.Icc (1 : ℤ) ((Int.natAbs b : ℤ) - 1)) := by
      simpa [Set.mem_Icc] using And.intro hk_pos hk_le
    refine Set.mem_iUnion.mpr ?_
    refine ⟨k, ?_⟩
    refine Set.mem_iUnion.mpr ?_
    refine ⟨hk_mem, ?_⟩

    have hm : (Int.natAbs b : ℤ) ∣ x - (a + k) := by
      let m : ℤ := (Int.natAbs b : ℤ)
      change m ∣ x - (a + k)
      refine ⟨(x - a) / m, ?_⟩
      have hxak : x - (a + k) = (x - a) - k := by
        ring_nf
      have hsub : (x - a) - (x - a) % m = (x - a) / m * m := by
        have h := Int.ediv_add_emod (x - a) m
        have h' := congrArg (fun t => t - (x - a) % m) h
        have h'' : (x - a) / m * m = (x - a) - (x - a) % m := by
          simpa [mul_comm, mul_left_comm, mul_assoc,sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using h'
        rw [h'']
      calc
        x - (a + k) = (x - a) - k := hxak
        _ = (x - a) - (x - a) % m := by simp [k, m]
        _ = (x - a) / m * m := hsub
        _ = m * ((x - a) / m) := by simp [mul_comm]

    have hbabs : b ∣ (Int.natAbs b : ℤ) := by
      simpa using (Int.dvd_natAbs_self b)

    have : b ∣ x - (a + k) := dvd_trans hbabs hm
    simpa [arithprog] using this


lemma arithprog_compl_mem_subset
  {a b : ℤ} (hb : b ≠ 0) :
  ∀ x ∈ (arithprog a b)ᶜ,
    ∃ k ∈ Set.Icc (1 : ℤ) ((Int.natAbs b : ℤ) - 1),
      x ∈ arithprog (a + k) b :=
by
  intro x hx
  have hx' := arithprog_compl_subset (a := a) (b := b) hb hx
  rcases Set.mem_iUnion.mp hx' with ⟨k, hk⟩
  rcases Set.mem_iUnion.mp hk with ⟨hkIcc, hxk⟩
  exact ⟨k, hkIcc, hxk⟩

lemma arithprog_compl_isOpen {a b : ℤ} (hb : b ≠ 0) : IsOpen ((arithprog a b)ᶜ) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x hx
  rcases arithprog_compl_mem_subset (a := a) (b := b) hb x hx
    with ⟨k, hk, hxk⟩
  refine ⟨arithprog (a + k) b,
    arithprog_shift_subset_compl (a := a) (b := b) (k := k) hb hk,
    arithprog_isOpen_new (a := a + k) (b := b) hb,
    hxk⟩


theorem infinite_primes_furstenberg :Set.Infinite {p : ℕ | Nat.Prime p} := by
  by_contra h
  have hfin : Set.Finite {p : ℕ | Nat.Prime p} := by
    simpa [Set.Infinite] using h
  classical
  have hPfin : Set.Finite {p : ℕ | Nat.Prime p} := hfin
  let P : Finset ℕ := hPfin.toFinset
  have hP : ∀ p : ℕ, p ∈ P ↔ Nat.Prime p := by
    intro p; simpa [P] using (hPfin.mem_toFinset)

  have hPm : ({1, -1} : Set ℤ) = ⋂ q ∈ P, (arithprog 0 (q : ℤ))ᶜ := by
    classical
    ext x
    constructor
    ·
      intro hx
      rcases hx with rfl | rfl
      ·
        simp [arithprog]
        intro q hq hdiv
        have hq' : Nat.Prime q := by
          have : q ∈ {p : ℕ | Nat.Prime p} := by
            simpa [P] using hq
          simpa using this
        have : q = 1 := Nat.eq_one_of_dvd_one (by exact_mod_cast hdiv)
        exact hq'.ne_one this
      ·
        simp [arithprog]
        intro q hq hdiv
        have hq' : Nat.Prime q := by
          have : q ∈ {p : ℕ | Nat.Prime p} := by
            simpa [P] using hq
          simpa using this
        have : q = 1 := Nat.eq_one_of_dvd_one (by exact_mod_cast hdiv)
        exact hq'.ne_one this

    ·
      intro hx
      by_contra h
      have hx' : x ≠ 1 ∧ x ≠ -1 := by
        simpa [not_or] using h
      rcases exists_prime_dvd_int x hx'.1 hx'.2 with ⟨p, hp, hpdvd⟩
      have : x ∈ arithprog 0 (p : ℤ) := by
        simpa [arithprog] using hpdvd
      have hxall : ∀ q ∈ P, x ∈ (arithprog 0 (q : ℤ))ᶜ := by
        simpa using hx
      have hpP : p ∈ P := by
        simpa [P] using hp
      exact hxall p hpP this

  have hPm_open : IsOpen ({1, -1} : Set ℤ) := by
    classical
    have hfin' :
        (∀ q ∈ P, Nat.Prime q) →
          IsOpen (⋂ q ∈ P, (arithprog 0 (q : ℤ))ᶜ) := by
      refine Finset.induction_on P ?h0 ?hstep
      ·
        intro _
        simpa
      · intro p P hp_notmem hPopen hPrime
        have hp' : Nat.Prime p := hPrime p (Finset.mem_insert_self p P)
        have hPrimeP : ∀ q ∈ P, Nat.Prime q := by
          intro q hq
          exact hPrime q (Finset.mem_insert_of_mem hq)
        have hop : IsOpen ((arithprog 0 (p : ℤ))ᶜ) :=
          arithprog_compl_isOpen (a := 0) (b := (p : ℤ))
            (by exact_mod_cast hp'.ne_zero)
        have hPopen' : IsOpen (⋂ q ∈ P, (arithprog 0 (q : ℤ))ᶜ) :=
          hPopen hPrimeP
        simpa [Finset.set_biInter_insert] using hop.inter hPopen'

    have hfin : IsOpen (⋂ q ∈ P, (arithprog 0 (q : ℤ))ᶜ) :=
      hfin' (by
        intro q hq
        exact (hP q).1 hq)

    simpa [hPm] using hfin

  have h_inf : Set.Infinite ({1, -1} : Set ℤ) :=
    Furstenberg_open_infinite (U := ({1, -1} : Set ℤ)) hPm_open (by
      refine ⟨(1 : ℤ), ?_⟩
      simp)

  have h_fin : Set.Finite ({1, -1} : Set ℤ) := by
    classical
    refine Set.Finite.ofFinset ({1, -1} : Finset ℤ) ?_
    intro x
    simp

  exact h_fin.not_infinite h_inf
