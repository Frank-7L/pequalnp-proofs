import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1119_aux

variable {α : Type*} [Fintype α] [DecidableEq α]

def miss (H : Finset (Finset α)) (X : Finset α) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ X

noncomputable def maxSets (H : Finset (Finset α)) : Finset (Finset α) := by
  classical
  exact Finset.univ.filter (fun X => miss H X ∧ ∀ i ∉ X, ¬ miss H (insert i X))

lemma miss_subset {H : Finset (Finset α)} {X Y : Finset α}
    (h : miss H Y) (hXY : X ⊆ Y) : miss H X := by
  intro e he heX
  exact h e he (heX.trans hXY)

lemma maxSets_largest {H : Finset (Finset α)} {A X : Finset α}
    (hA : A ∈ maxSets H) (hAX : A ⊆ X) (hX : miss H X) : X = A := by
  classical
  have ha := (Finset.mem_filter.mp hA).2
  apply Finset.Subset.antisymm _ hAX
  intro i hi
  by_contra hiA
  exact ha.2 i hiA (miss_subset hX (Finset.insert_subset hi hAX))

lemma extend_max {H : Finset (Finset α)} {X : Finset α} (hX : miss H X) :
    ∃ A ∈ maxSets H, X ⊆ A := by
  classical
  let S := (Finset.univ : Finset (Finset α)).filter (fun A => X ⊆ A ∧ miss H A)
  have hS : S.Nonempty := ⟨X, by simp [S, hX]⟩
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image S Finset.card hS
  have hAX := (Finset.mem_filter.mp hA).2
  refine ⟨A, Finset.mem_filter.mpr ⟨Finset.mem_univ A, hAX.2, ?_⟩, hAX.1⟩
  intro i hi hm
  have hiS : insert i A ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hAX.1.trans (Finset.subset_insert i A), hm⟩
  have hle := hmax (insert i A) hiS
  rw [Finset.card_insert_of_notMem hi] at hle
  omega

noncomputable def determines (family : Finset (Finset (Finset α)))
    (ord : Bool) (Q : Finset (Finset α)) : Prop := by
  classical
  exact ∀ C : Finset (Finset α) → Finset α → Bool,
    (∀ H ∈ family, ∀ X Y, X ⊆ Y → C H X = true → C H Y = true) →
    (ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X,
      C H X = true → C J X = true) →
    (∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X)) →
    ∀ H ∈ family, ∀ X, C H X = !decide (miss H X)

lemma determines_of_bank {E : Finset (Finset α)}
    {family : Finset (Finset (Finset α))} {ord : Bool} {Q : Finset (Finset α)}
    (hsub : ∀ H ∈ family, H ⊆ E)
    (hbank : E ∪ family.biUnion maxSets ⊆ Q) : determines family ord Q := by
  classical
  intro C hmono _ htest H hH X
  by_cases hm : miss H X
  · obtain ⟨A, hA, hXA⟩ := extend_max hm
    have hAQ : A ∈ Q := hbank (Finset.mem_union_right E (Finset.mem_biUnion.mpr ⟨H, hH, hA⟩))
    have hma : miss H A := (Finset.mem_filter.mp hA).2.1
    have hfalse : C H A = false := by simpa [hma] using htest H hH A hAQ
    cases hx : C H X with
    | false => simpa [hm] using hx
    | true => have ht := hmono H hH X A hXA hx; simp [hfalse] at ht
  · obtain ⟨e, he, heX⟩ : ∃ e ∈ H, e ⊆ X := by
      by_contra hn
      exact hm (fun e he heX => hn ⟨e, he, heX⟩)
    have heQ : e ∈ Q := hbank (Finset.mem_union_left _ (hsub H hH he))
    have hme : ¬miss H e := fun hh => hh e he (Finset.Subset.refl e)
    have htrue : C H e = true := by simpa [hme] using htest H hH e heQ
    simpa [hm] using hmono H hH e X heX htrue

lemma true_subset_edge_eq {E H : Finset (Finset α)} {e X : Finset α}
    (hcard : ∀ f ∈ E, f.card = 2) (hsub : H ⊆ E) (he : e ∈ E)
    (htrue : ¬miss H X) (hXe : X ⊆ e) : X = e := by
  classical
  obtain ⟨f, hf, hfX⟩ : ∃ f ∈ H, f ⊆ X := by
    by_contra hn
    exact htrue (fun f hf hfX => hn ⟨f, hf, hfX⟩)
  have hfe : f = e := Finset.eq_of_subset_of_card_le (hfX.trans hXe) (by
    rw [hcard e he, hcard f (hsub hf)])
  exact Finset.Subset.antisymm hXe (hfe ▸ hfX)

lemma edges_needed {E : Finset (Finset α)}
    {family : Finset (Finset (Finset α))} {ord : Bool} {Q : Finset (Finset α)}
    (hE : E ∈ family) (hsub : ∀ H ∈ family, H ⊆ E)
    (hcard : ∀ e ∈ E, e.card = 2) (hd : determines family ord Q) : E ⊆ Q := by
  classical
  intro e he
  by_contra heQ
  let C : Finset (Finset α) → Finset α → Bool :=
    fun H X => decide (¬miss H X ∧ X ≠ e)
  have hmono : ∀ H ∈ family, ∀ X Y, X ⊆ Y → C H X = true → C H Y = true := by
    intro H hH X Y hXY hc
    have hx : ¬miss H X ∧ X ≠ e := by simpa [C] using hc
    have hy : ¬miss H Y := fun hm => hx.1 (miss_subset hm hXY)
    have hYe : Y ≠ e := by
      intro hh
      exact hx.2 (true_subset_edge_eq hcard (hsub H hH) he hx.1 (hh ▸ hXY))
    simpa [C] using And.intro hy hYe
  have hord : ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X,
      C H X = true → C J X = true := by
    intro _ H _ J _ hHJ X hc
    have hx : ¬miss H X ∧ X ≠ e := by simpa [C] using hc
    have hj : ¬miss J X := by
      intro hm
      exact hx.1 (fun f hf => hm f (hHJ hf))
    simpa [C] using And.intro hj hx.2
  have ht : ∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X) := by
    intro H _ X hX
    have hXe : X ≠ e := by intro hh; subst X; exact heQ hX
    simp [C, hXe]
  have bad := hd C hmono hord ht E hE e
  have hme : ¬miss E e := fun hh => hh e he (Finset.Subset.refl e)
  simp [C, hme] at bad

lemma maxSets_needed {family : Finset (Finset (Finset α))} {ord : Bool}
    {Q : Finset (Finset α)} (hd : determines family ord Q) :
    family.biUnion maxSets ⊆ Q := by
  classical
  intro A hA
  obtain ⟨H0, hH0, hA⟩ := Finset.mem_biUnion.mp hA
  by_contra hAQ
  let C : Finset (Finset α) → Finset α → Bool :=
    fun H X => decide (¬miss H X ∨ (H0 ⊆ H ∧ A ⊆ X))
  have hmono : ∀ H ∈ family, ∀ X Y, X ⊆ Y → C H X = true → C H Y = true := by
    intro H _ X Y hXY hc
    have hx : ¬miss H X ∨ (H0 ⊆ H ∧ A ⊆ X) := by simpa [C] using hc
    have hy : ¬miss H Y ∨ (H0 ⊆ H ∧ A ⊆ Y) := by
      rcases hx with hx | hx
      · exact Or.inl (fun hm => hx (miss_subset hm hXY))
      · exact Or.inr ⟨hx.1, hx.2.trans hXY⟩
    simpa [C] using hy
  have hord : ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X,
      C H X = true → C J X = true := by
    intro _ H _ J _ hHJ X hc
    have hx : ¬miss H X ∨ (H0 ⊆ H ∧ A ⊆ X) := by simpa [C] using hc
    have hj : ¬miss J X ∨ (H0 ⊆ J ∧ A ⊆ X) := by
      rcases hx with hx | hx
      · exact Or.inl (fun hm => hx (fun e he => hm e (hHJ he)))
      · exact Or.inr ⟨hx.1.trans hHJ, hx.2⟩
    simpa [C] using hj
  have ht : ∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X) := by
    intro H _ X hX
    by_cases hm : miss H X
    · have hextra : ¬(H0 ⊆ H ∧ A ⊆ X) := by
        rintro ⟨h0H, hAX⟩
        have hm0 : miss H0 X := fun e he => hm e (h0H he)
        have hXA := maxSets_largest hA hAX hm0
        exact hAQ (hXA ▸ hX)
      simp [C, hm]
      exact fun h0 ha => hextra ⟨h0, ha⟩
    · simp [C, hm]
  have bad := hd C hmono hord ht H0 hH0 A
  have hmA : miss H0 A := (Finset.mem_filter.mp hA).2.1
  simp [C, hmA] at bad

theorem determines_iff_bank (E : Finset (Finset α))
    (family : Finset (Finset (Finset α))) (ord : Bool) (Q : Finset (Finset α))
    (hE : E ∈ family) (hsub : ∀ H ∈ family, H ⊆ E)
    (hcard : ∀ e ∈ E, e.card = 2) :
    determines family ord Q ↔ E ∪ family.biUnion maxSets ⊆ Q := by
  constructor
  · intro hd
    exact Finset.union_subset (edges_needed hE hsub hcard hd) (maxSets_needed hd)
  · exact determines_of_bank hsub

def deleteVertex (E : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  E.filter (fun e => v ∉ e)

private lemma max_mem {H : Finset (Finset α)} {A : Finset α}
    (h : A ∈ maxSets H) :
    miss H A ∧ ∀ i ∉ A, ¬ miss H (insert i A) := by
  classical
  exact (Finset.mem_filter.mp h).2

private lemma mem_max {H : Finset (Finset α)} {A : Finset α}
    (hmiss : miss H A) (hmax : ∀ i ∉ A, ¬ miss H (insert i A)) :
    A ∈ maxSets H := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmiss, hmax⟩

private lemma miss_delete_iff (E : Finset (Finset α)) (v : α) (X : Finset α) :
    miss (deleteVertex E v) X ↔ miss E (X.erase v) := by
  constructor
  · intro h e he hesub
    by_cases hv : v ∈ e
    · have hnv : v ∈ X.erase v := hesub hv
      simpa using hnv
    · exact h e (Finset.mem_filter.mpr ⟨he, hv⟩)
        (Finset.Subset.trans hesub (Finset.erase_subset v X))
  · intro h e he hesub
    have hev : e ∈ E ∧ v ∉ e := Finset.mem_filter.mp he
    apply h e hev.1
    intro i hi
    exact Finset.mem_erase.mpr ⟨fun hvi => hev.2 (hvi ▸ hi), hesub hi⟩

private lemma deleted_max_has_vertex (E : Finset (Finset α)) (v : α)
    {A : Finset α} (hA : A ∈ maxSets (deleteVertex E v)) : v ∈ A := by
  by_contra hv
  have hm := (max_mem hA).2 v hv
  apply hm
  rw [miss_delete_iff]
  simpa using (miss_delete_iff E v A).mp (max_mem hA).1

private lemma erase_insert_comm {A : Finset α} {i v : α} (hiv : i ≠ v) :
    (insert i A).erase v = insert i (A.erase v) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [hiv]
  · simp [Finset.mem_erase, Finset.mem_insert, hji]

private lemma insert_max_deleted (E : Finset (Finset α)) (v : α)
    {B : Finset α} (hB : B ∈ maxSets E) (hv : v ∉ B) :
    insert v B ∈ maxSets (deleteVertex E v) := by
  apply mem_max
  · rw [miss_delete_iff]
    simpa [hv] using (max_mem hB).1
  · intro i hi hm
    have hiv : i ≠ v := by
      intro h
      subst i
      exact hi (Finset.mem_insert_self _ _)
    have hnot : i ∉ B := by
      intro hib
      exact hi (Finset.mem_insert_of_mem hib)
    have hfail := (max_mem hB).2 i hnot
    apply hfail
    have h := (miss_delete_iff E v (insert i (insert v B))).mp hm
    rw [erase_insert_comm hiv] at h
    simpa [hv] using h

private lemma max_deleted_cases (E : Finset (Finset α)) (v : α)
    {A : Finset α} (hA : A ∈ maxSets (deleteVertex E v)) :
    A ∈ maxSets E ∨
      ∃ B ∈ maxSets E, v ∉ B ∧ A = insert v B := by
  classical
  have hvA := deleted_max_has_vertex E v hA
  by_cases hEA : miss E A
  · left
    apply mem_max hEA
    intro i hi hm
    exact (max_mem hA).2 i hi (fun e he => hm e (Finset.mem_filter.mp he).1)
  · right
    refine ⟨A.erase v, ?_, by simp, ?_⟩
    · apply mem_max
      · exact (miss_delete_iff E v A).mp (max_mem hA).1
      · intro i hi hm
        by_cases hiv : i = v
        · subst i
          exact hEA (by simpa [Finset.insert_erase hvA] using hm)
        · have hiA : i ∉ A := by
            intro hia
            exact hi (Finset.mem_erase.mpr ⟨hiv, hia⟩)
          have hdel : miss (deleteVertex E v) (insert i A) := by
            rw [miss_delete_iff]
            rw [erase_insert_comm hiv]
            exact hm
          exact (max_mem hA).2 i hiA hdel
    · exact (Finset.insert_erase hvA).symm

theorem vertex_bank_identity (E : Finset (Finset α)) (D : Finset α) :
    E ∪ (insert E (D.image (deleteVertex E))).biUnion maxSets =
      E ∪ maxSets E ∪
        D.biUnion (fun v => ((maxSets E).filter (fun B => v ∉ B)).image (insert v)) := by
  classical
  ext A
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro (hAE | ⟨H, hH, hAH⟩)
    · exact Or.inl (Or.inl hAE)
    · rcases hH with rfl | ⟨v, hvD, rfl⟩
      · exact Or.inl (Or.inr hAH)
      · rcases max_deleted_cases E v hAH with hbase | ⟨B, hB, hvB, rfl⟩
        · exact Or.inl (Or.inr hbase)
        · exact Or.inr ⟨v, hvD, B, ⟨hB, hvB⟩, rfl⟩
  · rintro ((hAE | hbase) | ⟨v, hvD, B, ⟨hB, hvB⟩, rfl⟩)
    · exact Or.inl hAE
    · exact Or.inr ⟨E, Or.inl rfl, hbase⟩
    · exact Or.inr ⟨deleteVertex E v, Or.inr ⟨v, hvD, rfl⟩,
        insert_max_deleted E v hB hvB⟩

end PEqualNP.Outside.L_lib_1119_aux

theorem PEqualNP.Outside.L_lib_1119 : (
∀ (n : Nat) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
  let sets := (Finset.univ : Finset (Finset (Fin n)))
  let miss := fun (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) => ∀ e ∈ H, ¬e ⊆ X
  let maximal := fun (H : Finset (Finset (Fin n))) (A : Finset (Fin n)) =>
    sets.filter (fun X => X ⊆ A ∧ miss H X ∧ ∀ i ∈ A \ X, ¬miss H (insert i X))
  let base := maximal E Finset.univ
  ∀ D : Finset (Fin n),
  let family := insert E (D.image (fun v => E.filter (fun e => v ∉ e)))
  let bank := E ∪ base ∪ D.biUnion (fun v => (base.filter (fun X => v ∉ X)).image (insert v))
  let determines := fun (ord : Bool) (Q : Finset (Finset (Fin n))) =>
    ∀ C : Finset (Finset (Fin n)) → Finset (Fin n) → Bool,
      (∀ H ∈ family, ∀ X Y : Finset (Fin n), X ⊆ Y → C H X = true → C H Y = true) →
      (ord = true → ∀ H ∈ family, ∀ J ∈ family, H ⊆ J → ∀ X, C H X = true → C J X = true) →
      (∀ H ∈ family, ∀ X ∈ Q, C H X = !decide (miss H X)) →
      ∀ H ∈ family, ∀ X, C H X = !decide (miss H X)
  ∀ ord Q, determines ord Q ↔ bank ⊆ Q
) := by
  classical
  intro n E hcard
  dsimp only
  intro D
  intro ord Q
  let family : Finset (Finset (Finset (Fin n))) :=
    insert E (D.image (fun v => E.filter (fun e => v ∉ e)))
  let base := PEqualNP.Outside.L_lib_1119_aux.maxSets E
  let rawbase : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Finset (Fin n))).filter (fun X =>
      X ⊆ (Finset.univ : Finset (Fin n)) ∧
      (∀ e ∈ E, ¬ e ⊆ X) ∧
      ∀ i ∈ (Finset.univ : Finset (Fin n)) \ X, ¬ (∀ e ∈ E, ¬ e ⊆ insert i X))
  let bank : Finset (Finset (Fin n)) :=
    E ∪ base ∪ D.biUnion (fun v => (base.filter (fun X => v ∉ X)).image (insert v))
  have hE : E ∈ family := by simp [family]
  have hsub : ∀ H ∈ family, H ⊆ E := by
    intro H hH
    simp only [family, Finset.mem_insert, Finset.mem_image] at hH
    rcases hH with rfl | ⟨v, _, rfl⟩
    · exact Finset.Subset.refl _
    · exact Finset.filter_subset _ _
  have hbase : rawbase = base := by
    ext X
    simp [rawbase, base, PEqualNP.Outside.L_lib_1119_aux.maxSets,
      PEqualNP.Outside.L_lib_1119_aux.miss]
  dsimp only [rawbase] at hbase
  rw [hbase]
  change _ ↔ bank ⊆ Q
  have hb : bank = E ∪ family.biUnion PEqualNP.Outside.L_lib_1119_aux.maxSets := by
    exact (PEqualNP.Outside.L_lib_1119_aux.vertex_bank_identity E D).symm
  rw [hb]
  have hdec (H : Finset (Finset (Fin n))) (X : Finset (Fin n)) :
      (!decide (∀ e ∈ H, ¬e ⊆ X)) =
        (!decide (PEqualNP.Outside.L_lib_1119_aux.miss H X)) := by
    congr 1
    exact Bool.decide_congr Iff.rfl
  apply Iff.trans ?_ (PEqualNP.Outside.L_lib_1119_aux.determines_iff_bank E family ord Q hE hsub hcard)
  unfold PEqualNP.Outside.L_lib_1119_aux.determines
  constructor
  · intro hd C hm ho ht H hH X
    rw [← hdec H X]
    apply hd C hm ho ?_ H hH X
    intro J hJ Y hY
    rw [hdec J Y]
    exact ht J hJ Y hY
  · intro hd C hm ho ht H hH X
    rw [hdec H X]
    apply hd C hm ho ?_ H hH X
    intro J hJ Y hY
    rw [← hdec J Y]
    exact ht J hJ Y hY
