import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5473.Sh

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_5473.Sh

namespace PEqualNP.Outside.L_meta_5473.LRAT

noncomputable section anon
def neg (l : Nat) : Nat :=
  match Nat.beq (Nat.mod l (nat_lit 2)) (nat_lit 0) with
  | true => Nat.add l (nat_lit 1)
  | false => Nat.sub l (nat_lit 1)

def bit (T l : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight T l) (nat_lit 1)) (nat_lit 1)

def setBit (T u : Nat) : Nat := Nat.lor T (Nat.shiftLeft (nat_lit 1) u)

theorem bit_eq_testBit (T l : Nat) : bit T l = T.testBit l := by
  have h : Nat.land (Nat.shiftRight T l) 1 = (T >>> l) % 2 := Nat.and_one_is_mod _
  unfold bit
  rw [h, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow, Bool.eq_iff_iff,
    decide_eq_true_eq]
  exact ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl _⟩

theorem bit_setBit (T u l : Nat) : bit (setBit T u) l = (bit T l || decide (u = l)) := by
  have h : setBit T u = T ||| (1 <<< u) := rfl
  rw [h, bit_eq_testBit, bit_eq_testBit, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]

def litVal (a : Nat → Bool) (l : Nat) : Bool := a (l / 2) == (l % 2 == 0)

def ClauseSat (a : Nat → Bool) (c : List Nat) : Prop := ∃ l ∈ c, litVal a l = true

def FormulaSat (F : List (List Nat)) : Prop := ∃ a : Nat → Bool, ∀ c ∈ F, ClauseSat a c

theorem litVal_neg (a : Nat → Bool) (l : Nat) : litVal a (neg l) = !litVal a l := by
  have hn : neg l = if l % 2 = 0 then l + 1 else l - 1 := by
    unfold neg
    cases hb : Nat.beq (Nat.mod l 2) 0 with
    | false =>
      have h1 : ¬ (l % 2 = 0) := Nat.ne_of_beq_eq_false hb
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]; rfl
    | true =>
      have h1 : l % 2 = 0 := Nat.eq_of_beq_eq_true hb
      rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
  rw [hn]
  unfold litVal
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) / 2 = l / 2 := by omega
    have h2 : (l + 1) % 2 = 1 := by omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true h), h1, h2, h]
    cases a (l / 2) <;> rfl
  · have h1 : (l - 1) / 2 = l / 2 := by omega
    have h2 : (l - 1) % 2 = 0 := by omega
    have h3 : l % 2 = 1 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h), h1, h2, h3]
    cases a (l / 2) <;> rfl

inductive Trie where
  | nil : Trie
  | node (v : Option Nat) (l r : Trie) : Trie

namespace Trie

def get (t : Trie) : Nat → Option Nat :=
  Trie.rec (motive := fun _ => Nat → Option Nat) (fun _ => none)
    (fun v _ _ ihl ihr k =>
      Bool.rec
        (Bool.rec (ihr (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1))) (ihl (Nat.div k (nat_lit 2)))
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        v (Nat.beq k (nat_lit 0))) t

def root (t : Trie) : Option Nat := Trie.rec (motive := fun _ => Option Nat) none (fun v _ _ _ _ => v) t
def left (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ l _ _ _ => l) t
def right (t : Trie) : Trie := Trie.rec (motive := fun _ => Trie) .nil (fun _ _ r _ _ => r) t

def set (fuel : Nat) : Trie → Nat → Option Nat → Trie :=
  Nat.rec (motive := fun _ => Trie → Nat → Option Nat → Trie) (fun t _ _ => t)
    (fun _ ih t k o =>
      Bool.rec
        (Bool.rec (.node t.root t.left (ih t.right (Nat.sub (Nat.div k (nat_lit 2)) (nat_lit 1)) o))
          (.node t.root (ih t.left (Nat.div k (nat_lit 2)) o) t.right)
          (Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 1)))
        (.node o t.left t.right) (Nat.beq k (nat_lit 0))) fuel

def All (P : Nat → Prop) : Trie → Prop
  | .nil => True
  | .node v l r => (∀ c, v = some c → P c) ∧ All P l ∧ All P r

theorem All.get {P : Nat → Prop} :
    ∀ {t : Trie} {k : Nat} {c : Nat}, All P t → t.get k = some c → P c
  | .nil, _, _, _, h => by simp [Trie.get] at h
  | .node v l r, k, c, ⟨hv, hl, hr⟩, h => by
    change Bool.rec (Bool.rec (r.get _) (l.get _) _) v _ = some c at h
    cases h0 : Nat.beq k 0
    · rw [h0] at h
      cases h1 : Nat.beq (Nat.mod k 2) 1
      · rw [h1] at h; exact All.get hr h
      · rw [h1] at h; exact All.get hl h
    · rw [h0] at h; exact hv c h

theorem All.root {P : Nat → Prop} {t : Trie} (h : All P t) :
    ∀ c, t.root = some c → P c := by
  cases t with
  | nil => intro c hc; cases hc
  | node v l r => exact h.1

theorem All.left {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.left := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.1

theorem All.right {P : Nat → Prop} {t : Trie} (h : All P t) : All P t.right := by
  cases t with
  | nil => trivial
  | node v l r => exact h.2.2

theorem All.set {P : Nat → Prop} :
    ∀ (fuel : Nat) {t : Trie} (k : Nat) {o : Option Nat},
      All P t → (∀ c, o = some c → P c) → All P (Trie.set fuel t k o)
  | 0, _, _, _, ht, _ => ht
  | fuel + 1, t, k, o, ht, ho => by
    change All P (Bool.rec (Bool.rec (.node t.root t.left (Trie.set fuel t.right _ o))
      (.node t.root (Trie.set fuel t.left _ o) t.right) _) (.node o t.left t.right) _)
    cases h0 : Nat.beq k 0
    · cases h1 : Nat.beq (Nat.mod k 2) 1
      · exact ⟨ht.root, ht.left, All.set fuel _ ht.right ho⟩
      · exact ⟨ht.root, All.set fuel _ ht.left ho, ht.right⟩
    · exact ⟨ho, ht.left, ht.right⟩

end Trie

theorem bit_land (x y l : Nat) : bit (Nat.land x y) l = (bit x l && bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_and x y l

theorem bit_xor (x y l : Nat) : bit (Nat.xor x y) l = (bit x l ^^ bit y l) := by
  rw [bit_eq_testBit, bit_eq_testBit, bit_eq_testBit]
  exact Nat.testBit_xor x y l

theorem bit_zero (l : Nat) : bit 0 l = false := by
  rw [bit_eq_testBit]; exact Nat.zero_testBit l

theorem bit_pow (u l : Nat) : bit (Nat.shiftLeft 1 u) l = decide (u = l) := by
  have h : Nat.shiftLeft 1 u = 1 <<< u := rfl
  rw [bit_eq_testBit, h, Nat.one_shiftLeft, Nat.testBit_two_pow]

def mask : List Nat → Nat
  | [] => 0
  | l :: ls => setBit (mask ls) l

theorem bit_mask : ∀ (c : List Nat) (l : Nat), bit (mask c) l = true ↔ l ∈ c
  | [], l => by simp [mask, bit_zero]
  | x :: xs, l => by
    rw [mask, bit_setBit, Bool.or_eq_true, bit_mask xs l, decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim Or.inr (fun h => Or.inl h.symm),
      fun h => h.elim (fun h => Or.inr h.symm) Or.inl⟩

abbrev Cont := Trie → Nat → Bool → Nat → Nat → Nat → Bool

def stepRead (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec
    (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x (nat_lit 0)))
    (k db (Nat.succ x) false C F P)
    (Nat.beq id (nat_lit 0))

def stepUnit (k : Cont) (db : Trie) (id C F P x : Nat) : Bool :=
  Bool.rec false (k db id true C (setBit F (neg x)) 0) (Nat.beq P (Nat.shiftLeft (nat_lit 1) x))

def stepClause (k : Cont) (db : Trie) (id C F D : Nat) : Bool :=
  Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
    (Bool.rec (k (db.set 64 (Nat.sub id (nat_lit 1)) (some C)) 0 false 0 0 0) true
      (Nat.beq C (nat_lit 0)))
    (Nat.beq (Nat.xor D (Nat.land D F)) (nat_lit 0))

def stepHint (k : Cont) (db : Trie) (id C F x : Nat) : Bool :=
  Option.rec false (stepClause k db id C F) (db.get x)

def tokenStep (k : Cont) (x : Nat) : Cont := fun db id mode C F P =>
  Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P (nat_lit 0)))
    mode

def stop : Cont := fun _ _ _ _ _ _ => false

def runS (e : Cont) (toks : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e (fun x _ k => tokenStep k x) toks

def runWord (W M fuel w : Nat) (k : Cont) : Cont :=
  Nat.rec (motive := fun _ => Nat → Cont) (fun _ => k)
    (fun _ ih w =>
      Bool.rec (tokenStep (ih (Nat.shiftRight w W)) (Nat.land w M)) k (Nat.beq w (nat_lit 1)))
    fuel w

def fuelW : Nat := 1024

def runW (e : Cont) (W : Nat) (words : List Nat) : Cont :=
  List.rec (motive := fun _ => Cont) e
    (fun w _ k => runWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) fuelW w k) words

def entryIn (db : Trie) (e : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun q lits _ =>
      Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q (nat_lit 1)))) e

def verify (B : List (List Nat)) : Cont := fun db _ _ _ _ _ =>
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.rec false ih (entryIn db e)) B

def loadF : List (List Nat) → List Nat → Trie → Trie
  | [], _, t => t
  | _ :: _, [], t => t
  | c :: cs, q :: qs, t =>
    loadF cs qs (Bool.rec (t.set 64 (Nat.sub q 1) (some (mask c))) t (Nat.beq q 0))

def loadB : List (List Nat) → Trie → Trie
  | [], t => t
  | [] :: es, t => loadB es t
  | (q :: lits) :: es, t => loadB es (t.set 64 (Nat.sub q 1) (some (mask lits)))

def check (F : List (List Nat)) (fk : List Nat) (toks : List Nat) : Bool :=
  runS stop toks (loadF F fk .nil) 0 false 0 0 0

def checkW (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadF F fk .nil) 0 false 0 0 0

def checkFirst (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) : Bool :=
  runW (verify B) W words (loadF F fk .nil) 0 false 0 0 0

def checkSeg (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat)) : Bool :=
  runW (verify B') W words (loadB B .nil) 0 false 0 0 0

def checkLast (B : List (List Nat)) (W : Nat) (words : List Nat) : Bool :=
  runW stop W words (loadB B .nil) 0 false 0 0 0

section Soundness

variable (a : Nat → Bool)

def MaskSat (m : Nat) : Prop := ∃ l, bit m l = true ∧ litVal a l = true

def BitsFalse (F : Nat) : Prop := ∀ l, bit F l = true → litVal a l = false

def EntriesSat (B : List (List Nat)) : Prop := ∀ e ∈ B, ClauseSat a e.tail

def HintInv (C F P : Nat) : Prop :=
  (∀ x, bit C x = true → litVal a x = false) →
    BitsFalse a F ∧ (P = 0 ∨ ∃ w, bit P w = true ∧ litVal a w = true)

theorem witness_U {F D : Nat} (hF : BitsFalse a F) (hD : MaskSat a D) :
    ∃ w, bit (Nat.xor D (Nat.land D F)) w = true ∧ litVal a w = true := by
  obtain ⟨w, hwD, hwv⟩ := hD
  have hwF : bit F w = false := by
    cases hb : bit F w
    · rfl
    · rw [hF w hb] at hwv; exact absurd hwv (by simp)
  exact ⟨w, by rw [bit_xor, bit_land, hwD, hwF]; rfl, hwv⟩

def Good (Q : Prop) (k : Cont) : Prop :=
  ∀ db id mode C F P, db.All (MaskSat a) → (mode = true → HintInv a C F P) →
    k db id mode C F P = true → Q

theorem stop_good (Q : Prop) : Good a Q stop := by
  intro _ _ _ _ _ _ _ _ h
  exact absurd h (by simp [stop])

theorem tokenStep_good {Q : Prop} {k : Cont} (hk : Good a Q k) (x : Nat) :
    Good a Q (tokenStep k x) := by
  intro db id mode C F P hdb hinv h
  change Bool.rec (stepRead k db id C F P x)
    (Bool.rec (stepUnit k db id C F P x) (stepHint k db id C F x) (Nat.beq P 0)) mode = true at h
  cases mode with
  | false =>
    change Bool.rec
      (Bool.rec (k db id false (setBit C x) F P) (k db id true C C 0) (Nat.beq x 0))
      (k db (Nat.succ x) false C F P) (Nat.beq id 0) = true at h
    cases hi : Nat.beq id 0
    · rw [hi] at h
      cases hx : Nat.beq x 0
      · rw [hx] at h
        exact hk db id false _ F P hdb (by simp) h
      · rw [hx] at h
        exact hk db id true C C 0 hdb (fun _ hC => ⟨hC, Or.inl rfl⟩) h
    · rw [hi] at h
      exact hk db _ false C F P hdb (by simp) h
  | true =>
    have hinv := hinv rfl
    cases hP : Nat.beq P 0
    · 
      rw [hP] at h
      change Bool.rec false (k db id true C (setBit F (neg x)) 0)
        (Nat.beq P (Nat.shiftLeft 1 x)) = true at h
      cases hu : Nat.beq P (Nat.shiftLeft 1 x)
      · rw [hu] at h; exact absurd h (by simp)
      · rw [hu] at h
        refine hk db id true C _ 0 hdb (fun _ hC => ⟨?_, Or.inl rfl⟩) h
        obtain ⟨hF, hPw⟩ := hinv hC
        rcases hPw with hP0 | ⟨w, hw, hwv⟩
        · rw [hP0] at hP; exact absurd hP (by simp)
        · rw [Nat.eq_of_beq_eq_true hu, bit_pow, decide_eq_true_eq] at hw
          subst hw
          intro l hl
          rw [bit_setBit, Bool.or_eq_true, decide_eq_true_eq] at hl
          rcases hl with hl | rfl
          · exact hF l hl
          · rw [litVal_neg, hwv]; rfl
    · 
      rw [hP] at h
      change Option.rec false (stepClause k db id C F) (db.get x) = true at h
      cases hg : db.get x with
      | none => rw [hg] at h; exact absurd h (by simp)
      | some D =>
        rw [hg] at h
        have hD : MaskSat a D := Trie.All.get hdb hg
        change Bool.rec (k db id true C F (Nat.xor D (Nat.land D F)))
          (Bool.rec (k (db.set 64 (Nat.sub id 1) (some C)) 0 false 0 0 0) true
            (Nat.beq C 0))
          (Nat.beq (Nat.xor D (Nat.land D F)) 0) = true at h
        cases hU : Nat.beq (Nat.xor D (Nat.land D F)) 0
        · rw [hU] at h
          refine hk db id true C F _ hdb (fun _ hC => ⟨(hinv hC).1, Or.inr ?_⟩) h
          exact witness_U a (hinv hC).1 hD
        · rw [hU] at h
          
          have hCsat : MaskSat a C := by
            apply Classical.byContradiction
            intro hn
            have hC : ∀ y, bit C y = true → litVal a y = false := by
              intro y hy
              cases hv : litVal a y
              · rfl
              · exact absurd ⟨y, hy, hv⟩ hn
            obtain ⟨w, hw, _⟩ := witness_U a (hinv hC).1 hD
            rw [Nat.eq_of_beq_eq_true hU, bit_zero] at hw
            exact absurd hw (by simp)
          cases hC0 : Nat.beq C 0
          · rw [hC0] at h
            exact hk _ _ false 0 0 0
              (Trie.All.set 64 _ hdb (fun c hc => by cases hc; exact hCsat)) (by simp) h
          · obtain ⟨w, hw, _⟩ := hCsat
            rw [Nat.eq_of_beq_eq_true hC0, bit_zero] at hw
            exact absurd hw (by simp)

theorem runS_good {Q : Prop} {e : Cont} (he : Good a Q e) :
    ∀ toks : List Nat, Good a Q (runS e toks)
  | [] => he
  | x :: xs => tokenStep_good a (runS_good he xs) x

theorem runWord_good {Q : Prop} (W M : Nat) {k : Cont} (hk : Good a Q k) :
    ∀ fuel w, Good a Q (runWord W M fuel w k)
  | 0, _ => hk
  | fuel + 1, w => by
    change Good a Q (Bool.rec (tokenStep (runWord W M fuel (Nat.shiftRight w W) k)
      (Nat.land w M)) k (Nat.beq w 1))
    cases Nat.beq w 1
    · exact tokenStep_good a (runWord_good W M hk fuel _) _
    · exact hk

theorem runW_good {Q : Prop} {e : Cont} (he : Good a Q e) (W : Nat) :
    ∀ words : List Nat, Good a Q (runW e W words)
  | [] => he
  | w :: ws => by
    have h := runWord_good a W (Nat.sub (Nat.shiftLeft 1 W) 1) (runW_good he W ws) fuelW w
    exact h

theorem clauseSat_of_maskSat {c : List Nat} (h : MaskSat a (mask c)) : ClauseSat a c := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mp hl, hv⟩

theorem maskSat_of_clauseSat {c : List Nat} (h : ClauseSat a c) : MaskSat a (mask c) := by
  obtain ⟨l, hl, hv⟩ := h
  exact ⟨l, (bit_mask c l).mpr hl, hv⟩

theorem verify_good (B : List (List Nat)) : Good a (EntriesSat a B) (verify B) := by
  intro db _ _ _ _ _ hdb _ h
  induction B with
  | nil => intro e he; simp at he
  | cons e es ih =>
    change Bool.rec false (List.rec (motive := fun _ => Bool) true
      (fun e _ ih => Bool.rec false ih (entryIn db e)) es) (entryIn db e) = true at h
    cases he : entryIn db e
    · rw [he] at h; exact absurd h (by simp)
    · rw [he] at h
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · cases e' with
        | nil => simp [entryIn] at he
        | cons q lits =>
          change Option.rec false (fun D => Nat.beq D (mask lits)) (db.get (Nat.sub q 1)) = true
            at he
          cases hg : db.get (Nat.sub q 1) with
          | none => rw [hg] at he; exact absurd he (by simp)
          | some D =>
            rw [hg] at he
            have hD := Trie.All.get hdb hg
            rw [Nat.eq_of_beq_eq_true he] at hD
            exact clauseSat_of_maskSat a hD
      · exact ih h e' he'

theorem loadF_all : ∀ (F : List (List Nat)) (fk : List Nat) {t : Trie}, t.All (MaskSat a) →
    (∀ c ∈ F, ClauseSat a c) → (loadF F fk t).All (MaskSat a)
  | [], _, _, ht, _ => ht
  | _ :: _, [], _, ht, _ => ht
  | c :: cs, q :: qs, t, ht, hF => by
    unfold loadF
    apply loadF_all cs qs _ (fun c' hc' => hF c' (List.mem_cons_of_mem _ hc'))
    cases Nat.beq q 0
    · exact Trie.All.set 64 _ ht (fun c' hc' => by
        cases hc'; exact maskSat_of_clauseSat a (hF c List.mem_cons_self))
    · exact ht

theorem loadB_all : ∀ (B : List (List Nat)) {t : Trie}, t.All (MaskSat a) →
    EntriesSat a B → (loadB B t).All (MaskSat a)
  | [], _, ht, _ => ht
  | [] :: es, _, ht, hB => loadB_all es ht (fun e he => hB e (List.mem_cons_of_mem _ he))
  | (q :: lits) :: es, t, ht, hB => by
    unfold loadB
    apply loadB_all es _ (fun e he => hB e (List.mem_cons_of_mem _ he))
    exact Trie.All.set 64 _ ht (fun c' hc' => by
      cases hc'; exact maskSat_of_clauseSat a (hB _ List.mem_cons_self))

end Soundness

theorem check_sound (F : List (List Nat)) (fk toks : List Nat) (h : check F fk toks = true) :
    ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runS_good a (stop_good a False) toks _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkW_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (h : checkW F fk W words = true) : ¬ FormulaSat F := by
  rintro ⟨a, ha⟩
  exact runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkFirst_sound (F : List (List Nat)) (fk : List Nat) (W : Nat) (words : List Nat)
    (B : List (List Nat)) (h : checkFirst F fk W words B = true) :
    ∀ a, (∀ c ∈ F, ClauseSat a c) → EntriesSat a B := fun a ha =>
  runW_good a (verify_good a B) W words _ _ false 0 0 0
    (loadF_all a F fk (t := .nil) trivial ha) (by simp) h

theorem checkSeg_sound (B : List (List Nat)) (W : Nat) (words : List Nat) (B' : List (List Nat))
    (h : checkSeg B W words B' = true) : ∀ a, EntriesSat a B → EntriesSat a B' := fun a hB =>
  runW_good a (verify_good a B') W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

theorem checkLast_sound (B : List (List Nat)) (W : Nat) (words : List Nat)
    (h : checkLast B W words = true) : ∀ a, EntriesSat a B → False := fun a hB =>
  runW_good a (stop_good a False) W words _ _ false 0 0 0
    (loadB_all a B (t := .nil) trivial hB) (by simp) h

def unpackWord (W M fuel w : Nat) (rest : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => rest)
    (fun _ ih w => Bool.rec (Nat.land w M :: ih (Nat.shiftRight w W)) rest (Nat.beq w (nat_lit 1)))
    fuel w

def unpack (W : Nat) (words : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun w _ ih => unpackWord W (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)) 1024 w ih)
    words

def decodeF (toks : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) []
    (fun x _ acc =>
      Bool.rec (List.rec (motive := fun _ => List (List Nat)) [[x]] (fun c cs _ => (x :: c) :: cs) acc)
        ([] :: acc) (Nat.beq x (nat_lit 0)))
    toks

end anon
end PEqualNP.Outside.L_meta_5473.LRAT

namespace PEqualNP.Outside.L_meta_5473.LRAT.Link

open PEqualNP.Outside.L_meta_5473.LRAT

structure Model where
  op : ℕ → ℕ
  s1 : ℕ → ℕ
  s2 : ℕ → ℕ
  so : ℕ
  w : ℕ → ℕ → Bool

def Model.sv (n : ℕ) (M : Model) (j k r : ℕ) : Bool :=
  if k < n then r.testBit k else if k < n + j then M.w (k - n) r else false

def gfun (t : ℕ) (a b : Bool) : Bool :=
  if t = 0 then a && b else if t = 1 then a || b else true

structure Valid (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (M : Model) : Prop where
  op_lt : ∀ j < s, M.op j < 3
  s1_le : ∀ j < s, M.s1 j ≤ n + j
  s2_le : ∀ j < s, M.s2 j ≤ n + j
  so_le : M.so ≤ n + s
  w_eq : ∀ j < s, ∀ r, R r →
    M.w j r = gfun (M.op j) (M.sv n j (M.s1 j) r) (M.sv n j (M.s2 j) r)
  out_eq : ∀ r, R r → M.sv n s M.so r = g r

def Model.pad (n : ℕ) (M : Model) (j : ℕ) : Prop :=
  M.op j = 2 ∧ M.s1 j = n + j ∧ M.s2 j = n + j

instance (n : ℕ) (M : Model) (j : ℕ) : Decidable (M.pad n j) := by
  unfold Model.pad; infer_instance

structure NF (n s : ℕ) (M : Model) : Prop where
  pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j
  padOp : ∀ j < s, M.op j = 2 → M.pad n j
  noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j
  noPadRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i
  ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j
  used : ∀ j, j + 1 < s → ¬ M.pad n j → ∃ i, j < i ∧ i < s ∧ (M.s1 i = n + j ∨ M.s2 i = n + j)
  out : 0 < s → M.so = n + s - 1 ∨ M.pad n (s - 1)

section formula
variable (n s : ℕ)

def wd : ℕ := 2 ^ n + n + s + 1

def ix (kd j a : ℕ) : ℕ := (kd * (s + 1) + j) * wd n s + a

def P (v : ℕ) : ℕ := 2 * v + 2

def Q (v : ℕ) : ℕ := 2 * v + 3

def L (v : ℕ) (b : Bool) : ℕ := if b then P v else Q v

def pairs (m : ℕ) : List (ℕ × ℕ) :=
  (List.range m).flatMap fun b => (List.range b).map fun a => (a, b)

def fOp : List (List ℕ) :=
  (List.range s).map fun j => [P (ix n s 0 j 0), P (ix n s 0 j 1), P (ix n s 0 j 2)]

def fSrcAlo : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).map fun j =>
    (List.range (n + j + 1)).map fun k => P (ix n s e j k)

def srcEq (e j k r : ℕ) : List (List ℕ) :=
  if k < n then [[Q (ix n s e j k), L (ix n s (e + 3) j r) (r.testBit k)]]
  else if k < n + j then
    [[Q (ix n s e j k), Q (ix n s (e + 3) j r), P (ix n s 3 (k - n) r)],
     [Q (ix n s e j k), P (ix n s (e + 3) j r), Q (ix n s 3 (k - n) r)]]
  else [[Q (ix n s e j k), Q (ix n s (e + 3) j r)]]

def fSrcEq (rows : List ℕ) : List (List ℕ) :=
  [1, 2].flatMap fun e => (List.range s).flatMap fun j => rows.flatMap fun r =>
    (List.range (n + j + 1)).flatMap fun k => srcEq n s e j k r

def gateCl (j r : ℕ) : List (List ℕ) :=
  [[Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 4 j r)],
   [Q (ix n s 0 j 0), Q (ix n s 3 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 0), P (ix n s 3 j r), Q (ix n s 4 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 4 j r)],
   [Q (ix n s 0 j 1), P (ix n s 3 j r), Q (ix n s 5 j r)],
   [Q (ix n s 0 j 1), Q (ix n s 3 j r), P (ix n s 4 j r), P (ix n s 5 j r)],
   [Q (ix n s 0 j 2), P (ix n s 3 j r)]]

def fGate (rows : List ℕ) : List (List ℕ) :=
  (List.range s).flatMap fun j => rows.flatMap fun r => gateCl n s j r

def fOutAlo : List (List ℕ) := [(List.range (n + s + 1)).map fun k => P (ix n s 6 0 k)]

def outEq (g : ℕ → Bool) (k r : ℕ) : List (List ℕ) :=
  if k < n then (if r.testBit k = g r then [] else [[Q (ix n s 6 0 k)]])
  else if k < n + s then [[Q (ix n s 6 0 k), L (ix n s 3 (k - n) r) (g r)]]
  else if g r = true then [[Q (ix n s 6 0 k)]] else []

def fOutEq (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  rows.flatMap fun r => (List.range (n + s + 1)).flatMap fun k => outEq n s g k r

def fOut : List (List ℕ) :=
  if s = 0 then [] else [[P (ix n s 6 0 (n + s - 1)), P (ix n s 7 (s - 1) 0)]]

def fPad : List (List ℕ) :=
  (List.range s).flatMap fun j =>
    [[Q (ix n s 7 j 0), P (ix n s 0 j 2)], [Q (ix n s 7 j 0), P (ix n s 1 j (n + j))],
     [Q (ix n s 7 j 0), P (ix n s 2 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 0 j 2)],
     [P (ix n s 7 j 0), Q (ix n s 1 j (n + j))], [P (ix n s 7 j 0), Q (ix n s 2 j (n + j))]]

def fPre : List (List ℕ) :=
  (List.range (s - 1)).map fun j => [Q (ix n s 7 (j + 1) 0), P (ix n s 7 j 0)]

def fPadRd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range j).flatMap fun i =>
    [[Q (ix n s 7 i 0), Q (ix n s 1 j (n + i))], [Q (ix n s 7 i 0), Q (ix n s 2 j (n + i))]]

def fOrd : List (List ℕ) :=
  (List.range s).flatMap fun j => (List.range (n + j + 1)).flatMap fun k =>
    (List.range (k + 1)).map fun l => [Q (ix n s 1 j k), Q (ix n s 2 j l), P (ix n s 7 j 0)]

def fUsed : List (List ℕ) :=
  (List.range (s - 1)).map fun j =>
    ((List.range (s - 1 - j)).map fun t => P (ix n s 1 (j + 1 + t) (n + j))) ++
    ((List.range (s - 1 - j)).map fun t => P (ix n s 2 (j + 1 + t) (n + j))) ++
      [P (ix n s 7 j 0)]

def enc (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) :=
  fOp n s ++ fSrcAlo n s ++ fSrcEq n s rows ++ fGate n s rows ++ fOutAlo n s ++
    fOutEq n s g rows ++ fOut n s ++ fPad n s ++ fPre n s ++ fPadRd n s ++ fOrd n s ++
    fUsed n s

end formula

def rowFun (n : ℕ) (f : (Fin n → Bool) → Bool) (r : ℕ) : Bool := f fun i => r.testBit i

def meaning (n : ℕ) (M : Model) (kd j a : ℕ) : Bool :=
  if kd = 0 then M.op j == a else if kd = 1 then M.s1 j == a else if kd = 2 then M.s2 j == a
  else if kd = 3 then M.w j a else if kd = 4 then M.sv n j (M.s1 j) a
  else if kd = 5 then M.sv n j (M.s2 j) a else if kd = 6 then M.so == a
  else if kd = 7 then decide (M.pad n j) else false

def val (n s : ℕ) (M : Model) (x : ℕ) : Bool :=
  meaning n M ((x - 1) / wd n s / (s + 1)) ((x - 1) / wd n s % (s + 1)) ((x - 1) % wd n s)

theorem val_ix (n s : ℕ) (M : Model) {kd j a : ℕ} (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s kd j a + 1) = meaning n M kd j a := by
  have hw : 0 < wd n s := Nat.succ_pos _
  unfold val ix
  rw [Nat.add_sub_cancel]
  have h1 : ((kd * (s + 1) + j) * wd n s + a) / wd n s = kd * (s + 1) + j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h2 : ((kd * (s + 1) + j) * wd n s + a) % wd n s = a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  have h3 : (kd * (s + 1) + j) / (s + 1) = kd := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega),
      Nat.zero_add]
  have h4 : (kd * (s + 1) + j) % (s + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2, h3, h4]

theorem litVal_P (a : ℕ → Bool) (v : ℕ) : litVal a (P v) = a (v + 1) := by
  unfold litVal P
  rw [show (2 * v + 2) / 2 = v + 1 by omega, show (2 * v + 2) % 2 = 0 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_Q (a : ℕ → Bool) (v : ℕ) : litVal a (Q v) = !a (v + 1) := by
  unfold litVal Q
  rw [show (2 * v + 3) / 2 = v + 1 by omega, show (2 * v + 3) % 2 = 1 by omega]
  cases a (v + 1) <;> rfl

theorem litVal_L (a : ℕ → Bool) (v : ℕ) (b : Bool) : litVal a (L v b) = (a (v + 1) == b) := by
  cases b <;> simp [L, litVal_P, litVal_Q]

theorem cs_cons (a : ℕ → Bool) (l : ℕ) (c : List ℕ) :
    ClauseSat a (l :: c) ↔ litVal a l = true ∨ ClauseSat a c := by
  simp [ClauseSat]

theorem cs_nil (a : ℕ → Bool) : ClauseSat a [] ↔ False := by simp [ClauseSat]

theorem cs_of_mem {a : ℕ → Bool} {c : List ℕ} {l : ℕ} (h : l ∈ c) (hl : litVal a l = true) :
    ClauseSat a c := ⟨l, h, hl⟩

section vlemmas
variable {n s : ℕ} (M : Model) {j a : ℕ}

theorem wd_lt1 (h : a ≤ n + s + 1) : a < wd n s := by
  have := Nat.one_le_two_pow (n := n); unfold wd; omega
theorem wd_lt2 (h : a < 2 ^ n) : a < wd n s := by unfold wd; omega

theorem v_op (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 0 j a + 1) = (M.op j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s1 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 1 j a + 1) = (M.s1 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_s2 (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 2 j a + 1) = (M.s2 j == a) := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_w (hj : j ≤ s) (ha : a < wd n s) : val n s M (ix n s 3 j a + 1) = M.w j a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u1 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 4 j a + 1) = M.sv n j (M.s1 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_u2 (hj : j ≤ s) (ha : a < wd n s) :
    val n s M (ix n s 5 j a + 1) = M.sv n j (M.s2 j) a := by
  rw [val_ix n s M hj ha]; simp [meaning]
theorem v_so (ha : a < wd n s) : val n s M (ix n s 6 0 a + 1) = (M.so == a) := by
  rw [val_ix n s M (Nat.zero_le _) ha]; simp [meaning]
theorem v_pad (hj : j ≤ s) : val n s M (ix n s 7 j 0 + 1) = decide (M.pad n j) := by
  rw [val_ix n s M hj (wd_lt1 (by omega))]; simp [meaning]

end vlemmas

def Model.src (M : Model) (e j : ℕ) : ℕ := if e = 1 then M.s1 j else M.s2 j

theorem v_src {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s e j a + 1) = (M.src e j == a) := by
  rcases he with rfl | rfl
  · exact v_s1 M hj ha
  · exact v_s2 M hj ha

theorem v_u {n s : ℕ} (M : Model) {e j a : ℕ} (he : e = 1 ∨ e = 2) (hj : j ≤ s)
    (ha : a < wd n s) : val n s M (ix n s (e + 3) j a + 1) = M.sv n j (M.src e j) a := by
  rcases he with rfl | rfl
  · exact v_u1 M hj ha
  · exact v_u2 M hj ha

section sound
variable {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
  (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
include hv

theorem src_le {e j : ℕ} (he : e = 1 ∨ e = 2) (hj : j < s) : M.src e j ≤ n + j := by
  rcases he with rfl | rfl
  · simpa [Model.src] using hv.s1_le j hj
  · simpa [Model.src] using hv.s2_le j hj

theorem s_fOp : ∀ c ∈ fOp n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOp, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have := hv.op_lt j hj
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_op, beq_iff_eq, or_false]
  omega

theorem s_fSrcAlo : ∀ c ∈ fSrcAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcAlo, List.mem_flatMap, List.mem_map, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  obtain ⟨e, he, j, hj, rfl⟩ := hc
  have hle := src_le hv he hj
  apply cs_of_mem (List.mem_map.2 ⟨M.src e j, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_src M he (by omega) (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fSrcEq : ∀ c ∈ fSrcEq n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fSrcEq, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨e, he, j, hj, r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  unfold srcEq at hc
  split_ifs at hc with h1 h2
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_src M he, v_u M he,
      or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1]
    · left; simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
    · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_src M he, v_u M he, v_w,
        or_false]
      by_cases hs : M.src e j = k
      · rw [hs]
        have : M.sv n j k r = M.w (k - n) r := by simp [Model.sv, h1, h2]
        rw [this]
        cases M.w (k - n) r <;> simp
      · simp [hs]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_src M he, v_u M he, or_false]
    by_cases hs : M.src e j = k
    · right; rw [hs]; simp [Model.sv, h1, h2]
    · left; simp [hs]

omit hv in
theorem gate_fact (t : ℕ) (ht : t < 3) (x a b : Bool) (hw : x = gfun t a b) :
    ((!(t == 0) || !x || a) = true) ∧ ((!(t == 0) || !x || b) = true) ∧
    ((!(t == 0) || x || !a || !b) = true) ∧ ((!(t == 1) || x || !a) = true) ∧
    ((!(t == 1) || x || !b) = true) ∧ ((!(t == 1) || !x || a || b) = true) ∧
    ((!(t == 2) || x) = true) := by
  interval_cases t <;> cases x <;> cases a <;> cases b <;> simp_all [gfun]

include hrows in
theorem s_fGate : ∀ c ∈ fGate n s rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fGate, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨j, hj, r, hr, hc⟩ := hc
  have hr' := hrows r hr
  have G := gate_fact _ (hv.op_lt j hj) _ _ _ (hv.w_eq j hj r hr)
  simp only [gateCl, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨G1, G2, G3, G4, G5, G6, G7⟩ := G
  simp only [Bool.or_eq_true, or_assoc] at G1 G2 G3 G4 G5 G6 G7
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_w, v_u1, v_u2,
      or_false, or_assoc] <;> assumption

theorem s_fOutAlo : ∀ c ∈ fOutAlo n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutAlo, List.mem_cons, List.not_mem_nil, or_false] at hc
  subst hc
  have := hv.so_le
  apply cs_of_mem (List.mem_map.2 ⟨M.so, List.mem_range.2 (by omega), rfl⟩)
  rw [litVal_P, v_so M (wd_lt1 (by omega))]
  simp

include hrows in
theorem s_fOutEq : ∀ c ∈ fOutEq n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOutEq, List.mem_flatMap, List.mem_range] at hc
  obtain ⟨r, hr, k, hk, hc⟩ := hc
  have hr' := hrows r hr
  have ho := hv.out_eq r hr
  unfold outEq at hc
  by_cases h1 : k < n
  · rw [if_pos h1] at hc
    by_cases h2 : r.testBit k = g r
    · rw [if_pos h2] at hc; simp at hc
    · rw [if_neg h2] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_pos h1] at ho
        exact absurd ho h2
      · simp [e]
  · rw [if_neg h1] at hc
    by_cases h3 : k < n + s
    · rw [if_pos h3] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc
      simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_L, v_so, v_w, or_false]
      by_cases e : M.so = k
      · rw [e] at ho
        simp only [Model.sv, if_neg h1, if_pos h3] at ho
        right; rw [ho]; simp
      · simp [e]
    · rw [if_neg h3] at hc
      by_cases h4 : g r = true
      · rw [if_pos h4] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst hc
        simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_so, or_false]
        by_cases e : M.so = k
        · rw [e] at ho
          simp only [Model.sv, if_neg h1, if_neg h3] at ho
          rw [h4] at ho
          exact absurd ho Bool.false_ne_true
        · simp [e]
      · rw [if_neg h4] at hc; simp at hc

include hn

theorem s_fOut : ∀ c ∈ fOut n s, ClauseSat (val n s M) c := by
  intro c hc
  unfold fOut at hc
  split_ifs at hc with hs
  · simp at hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_P, v_so, v_pad, or_false, beq_iff_eq,
      decide_eq_true_eq]
    exact hn.out (by omega)

theorem s_fPad : ∀ c ∈ fPad n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPad, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, hc⟩ := hc
  have h1 := hn.padOp j hj
  have h2 := hn.noF j hj
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_op, v_s1, v_s2, v_pad,
      or_false, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
      beq_eq_false_iff_ne, ne_eq]
    unfold Model.pad at *
    tauto

theorem s_fPre : ∀ c ∈ fPre n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPre, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_pad, or_false,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : M.pad n (j + 1)
  · exact Or.inr (hn.pre j (by omega) h)
  · exact Or.inl h

theorem s_fPadRd : ∀ c ∈ fPadRd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fPadRd, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  obtain ⟨j, hj, i, hi, hc⟩ := hc
  have h1 := hn.noPadRd j hj i hi
  rcases hc with rfl | rfl <;>
  · simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, v_s1, v_s2, v_pad, or_false,
      Bool.not_eq_true', decide_eq_false_iff_not, beq_eq_false_iff_ne, ne_eq]
    tauto

theorem s_fOrd : ∀ c ∈ fOrd n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fOrd, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, k, hk, l, hl, rfl⟩ := hc
  simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [cs_cons, cs_nil, litVal_Q, litVal_P, v_s1, v_s2, v_pad, or_false,
    Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq, decide_eq_true_eq]
  by_cases hp : M.pad n j
  · exact Or.inr (Or.inr hp)
  · have := hn.ord j hj hp
    omega

theorem s_fUsed : ∀ c ∈ fUsed n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fUsed, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  by_cases hp : M.pad n j
  · apply cs_of_mem (l := P (ix n s 7 j 0)) (by simp)
    rw [litVal_P, v_pad M (by omega)]
    simpa using hp
  · obtain ⟨i, hji, hi, h | h⟩ := hn.used j (by omega) hp
    · apply cs_of_mem (l := P (ix n s 1 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s1 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h
    · apply cs_of_mem (l := P (ix n s 2 (j + 1 + (i - j - 1)) (n + j)))
      · apply List.mem_append_left; apply List.mem_append_right
        exact List.mem_map.2 ⟨i - j - 1, List.mem_range.2 (by omega), rfl⟩
      · rw [litVal_P, v_s2 M (by omega) (wd_lt1 (by omega)),
          show j + 1 + (i - j - 1) = i by omega]
        simpa using h

include hrows in

theorem enc_sat : ∀ c ∈ enc n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  simp only [enc, List.append_assoc, List.mem_append] at hc
  rcases hc with h | h | h | h | h | h | h | h | h | h | h | h
  · exact s_fOp hv c h
  · exact s_fSrcAlo hv c h
  · exact s_fSrcEq hrows hv c h
  · exact s_fGate hrows hv c h
  · exact s_fOutAlo hv c h
  · exact s_fOutEq hrows hv c h
  · exact s_fOut hv hn c h
  · exact s_fPad hv hn c h
  · exact s_fPre hv hn c h
  · exact s_fPadRd hv hn c h
  · exact s_fOrd hv hn c h
  · exact s_fUsed hv hn c h

end sound

section circuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5473.Sh

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def nm (n j a : ℕ) : ℕ := if a < n + j then a else n + j

def code (n : ℕ) (g : Gate) (j : ℕ) : ℕ × ℕ × ℕ :=
  match g.op, g.inputs with
  | .and, [] => (2, n + j, n + j)
  | .and, [a] => (0, nm n j a, nm n j a)
  | .and, a :: b :: _ => (0, nm n j a, nm n j b)
  | .or, [] => (1, n + j, n + j)
  | .or, [a] => (1, nm n j a, nm n j a)
  | .or, a :: b :: _ => (1, nm n j a, nm n j b)
  | _, _ => (2, n + j, n + j)

def gateAt (C : Circuit) (j : ℕ) : Gate := C.gates.getD j ⟨.and, []⟩

def ofCirc (n s : ℕ) (C : Circuit) : Model where
  op j := (code n (gateAt C j) j).1
  s1 j := (code n (gateAt C j) j).2.1
  s2 j := (code n (gateAt C j) j).2.2
  so := if C.output < n + C.gates.length then C.output else n + s
  w j r := if j < C.gates.length then (C.wires (xr n r)).getD (n + j) false else true

theorem xr_length (n r : ℕ) : (xr n r).length = n := by simp [xr]

theorem xr_getD (n r a : ℕ) (ha : a < n) : (xr n r).getD a false = r.testBit a := by
  simp [xr, List.getD_eq_getElem?_getD, ha]

theorem code_le (n : ℕ) (g : Gate) (j : ℕ) :
    (code n g j).1 < 3 ∧ (code n g j).2.1 ≤ n + j ∧ (code n g j).2.2 ≤ n + j := by
  have h : ∀ a, nm n j a ≤ n + j := fun a => by unfold nm; split_ifs <;> omega
  rcases g with ⟨op, ins⟩
  cases op <;> rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp [code, h]

theorem code_eval (n : ℕ) (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (j : ℕ) (S : ℕ → Bool) (hS : S (n + j) = false) :
    g.op.eval (g.inputs.map fun i => S (nm n j i)) =
      gfun (code n g j).1 (S (code n g j).2.1) (S (code n g j).2.2) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  dsimp only at hlen
  rcases hop with rfl | rfl <;>
    rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp_all [code, GateOp.eval, gfun]

theorem wire_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
        (wiresFrom (C.gates.take j) x).getD i false) ∧
    ∀ i, (wiresFrom (C.gates.take j) x).getD i false =
      if i < x.length + j then (C.wires x).getD i false else false := by
  have hsplit : C.gates = C.gates.take j ++ (gateAt C j :: C.gates.drop (j + 1)) := by
    rw [gateAt, List.getD_eq_getElem _ _ hj, List.cons_getElem_drop_succ, List.take_append_drop]
  set V := wiresFrom (C.gates.take j) x with hV
  have hVl : V.length = x.length + j := by
    rw [hV, length_wiresFrom, List.length_take]; omega
  set e := (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => V.getD i false)
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1)) (V ++ [e]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]; rfl
  have hpre : ∀ i < x.length + j + 1, (C.wires x).getD i false = (V ++ [e]).getD i false := by
    intro i hi
    rw [hw, getD_wiresFrom _ _ _ (by simp [hVl]; omega)]
  refine ⟨?_, ?_⟩
  · rw [hpre _ (by omega), ← hVl, getD_snoc_eq]
  · intro i
    split_ifs with hi
    · rw [hpre i (by omega), List.getD_append _ _ _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  where
    getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by simp

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  rw [wires_eq, length_wiresFrom]

theorem ofCirc_sv (n s : ℕ) (C : Circuit) (j r k : ℕ) (hj : k < n + C.gates.length)
    (hk : k < n + j) : (ofCirc n s C).sv n j k r = (C.wires (xr n r)).getD k false := by
  unfold Model.sv
  by_cases h6 : k < n
  · rw [if_pos h6, wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6),
      xr_getD n r k h6]
  · rw [if_neg h6, if_pos hk]
    simp only [ofCirc, show k - n < C.gates.length by omega, if_true]
    congr 1
    omega

theorem valid_ofCirc (n s : ℕ) (g : ℕ → Bool) (R : ℕ → Prop) (C : Circuit) (hC : Monotone2 C)
    (hsz : C.gates.length ≤ s) (hev : ∀ r, R r → C.eval (xr n r) = g r) :
    Valid n s g R (ofCirc n s C) where
  op_lt j _ := (code_le n _ j).1
  s1_le j _ := (code_le n _ j).2.1
  s2_le j _ := (code_le n _ j).2.2
  so_le := by simp only [ofCirc]; split_ifs <;> omega
  w_eq j hj r _ := by
    by_cases hjl : j < C.gates.length
    · have hmem : gateAt C j ∈ C.gates := by
        rw [gateAt, List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
      have hg := hC (gateAt C j) hmem
      obtain ⟨h1, h2⟩ := wire_gate C (xr n r) j hjl
      rw [xr_length] at h1 h2
      have hS : ∀ i, (wiresFrom (C.gates.take j) (xr n r)).getD i false =
          (ofCirc n s C).sv n j (nm n j i) r := by
        intro i
        rw [h2 i]
        unfold nm
        split_ifs with hi
        · rw [ofCirc_sv n s C j r i (by omega) hi]
        · simp [Model.sv]
      simp only [hS] at h1
      have hw : (ofCirc n s C).w j r = if j < C.gates.length then
          (C.wires (xr n r)).getD (n + j) false else true := rfl
      rw [hw, if_pos hjl, h1, code_eval n _ hg.1 hg.2 j (fun k => (ofCirc n s C).sv n j k r)
        (by simp [Model.sv])]
      rfl
    · have hga : gateAt C j = ⟨.and, []⟩ := by
        rw [gateAt, List.getD_eq_default _ _ (by omega)]
      simp [ofCirc, hjl, hga, code, gfun]
  out_eq r hr := by
    rw [← hev r hr, Circuit.eval]
    have hso : (ofCirc n s C).so =
        if C.output < n + C.gates.length then C.output else n + s := rfl
    rw [hso]
    split_ifs with ho
    · by_cases h6 : C.output < n
      · simp only [Model.sv, if_pos h6]
        rw [wires_eq, getD_wiresFrom _ _ _ (by rw [xr_length]; exact h6), xr_getD n r _ h6]
      · rw [ofCirc_sv n s C s r _ ho (by omega)]
    · rw [List.getD_eq_default _ _ (by rw [wires_length, xr_length]; omega)]
      simp [Model.sv]

end circuit

def phi (n d k : ℕ) : ℕ := if k < n then k else if k < n + d then k + 1 else k

def rd (n d t j k : ℕ) : ℕ :=
  if k = n + d then (if t = 0 then n + j else if t = 1 then n else phi n d (t - 2)) else phi n d k

def tval (n : ℕ) (M : Model) (d t r : ℕ) : Bool :=
  if t = 0 then false else if t = 1 then true else M.sv n d (t - 2) r

def mv (n s : ℕ) (M : Model) (d t : ℕ) : Model where
  op j := if j = 0 then 2 else if j ≤ d then M.op (j - 1) else M.op j
  s1 j := if j = 0 then n else if j ≤ d then phi n d (M.s1 (j - 1)) else rd n d t j (M.s1 j)
  s2 j := if j = 0 then n else if j ≤ d then phi n d (M.s2 (j - 1)) else rd n d t j (M.s2 j)
  so := rd n d t s M.so
  w j r := if j = 0 then true else if j ≤ d then M.w (j - 1) r else M.w j r

def Model.Read (n s : ℕ) (M : Model) (d : ℕ) : Prop :=
  (∃ j, d < j ∧ j < s ∧ (M.s1 j = n + d ∨ M.s2 j = n + d)) ∨ M.so = n + d

def TgtOk (n d t : ℕ) : Prop := t = 0 ∨ t = 1 ∨ (2 ≤ t ∧ t - 2 < n + d)

section move
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}

theorem sv_shift (hd : d < s) {i k r : ℕ} (hi : i < d) (hk : k ≤ n + i) :
    (mv n s M d t).sv n (i + 1) (phi n d k) r = M.sv n i k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + (i + 1) by omega), if_pos h7, mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_pos (show k < n + d by omega), if_neg (show ¬ k + 1 < n by omega),
        if_neg (show ¬ k + 1 < n + (i + 1) by omega), if_neg h7]

theorem sv_later {j k r : ℕ} (hj : d < j) (hkd : k ≠ n + d) :
    (mv n s M d t).sv n j (phi n d k) r = M.sv n j k r := by
  unfold Model.sv phi
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + d
    · simp only [if_neg h6, if_pos h7, if_neg (show ¬ k + 1 < n by omega),
        if_pos (show k + 1 < n + j by omega), if_pos (show k < n + j by omega), mv,
        if_neg (show ¬ k + 1 - n = 0 by omega), if_pos (show k + 1 - n ≤ d by omega)]
      congr 1 <;> omega
    · simp only [if_neg h6, if_neg h7]
      by_cases h8 : k < n + j
      · simp only [if_pos h8, mv, if_neg (show ¬ k - n = 0 by omega),
          if_neg (show ¬ k - n ≤ d by omega)]
      · simp only [if_neg h8]

theorem sv_rd (ht : TgtOk n d t) {j k r : ℕ} (hj : d < j)
    (htr : k = n + d → M.w d r = tval n M d t r) :
    (mv n s M d t).sv n j (rd n d t j k) r = M.sv n j k r := by
  unfold rd
  by_cases hkd : k = n + d
  · rw [if_pos hkd]
    have hw := htr hkd
    have hold : M.sv n j k r = M.w d r := by
      unfold Model.sv
      simp only [if_neg (show ¬ k < n by omega), if_pos (show k < n + j by omega)]
      congr 1; omega
    rw [hold, hw]
    unfold tval
    rcases ht with rfl | rfl | ⟨h2, hc⟩
    · simp [Model.sv]
    · simp [Model.sv, mv, show 0 < j by omega]
    · simp only [if_neg (show ¬ t = 0 by omega), if_neg (show ¬ t = 1 by omega)]
      rw [sv_later hj (by omega)]
      unfold Model.sv
      by_cases h6 : t - 2 < n
      · simp [h6]
      · simp only [if_neg h6, if_pos (show t - 2 < n + j by omega), if_pos hc]
  · rw [if_neg hkd]
    exact sv_later hj hkd

theorem valid_mv (hv : Valid n s g R M) (hd : d < s) (ht : TgtOk n d t)
    (htr : M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) :
    Valid n s g R (mv n s M d t) where
  op_lt j hj := by
    simp only [mv]; split_ifs
    · omega
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hj
  s1_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s1_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s1_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  s2_le j hj := by
    simp only [mv]; split_ifs with h0 h1
    · omega
    · have := hv.s2_le (j - 1) (by omega); unfold phi; split_ifs <;> omega
    · have := hv.s2_le j hj
      unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  so_le := by
    have := hv.so_le
    simp only [mv]; unfold rd phi; rcases ht with rfl | rfl | ⟨_, _⟩ <;> split_ifs <;> omega
  w_eq j hj r hr := by
    by_cases h0 : j = 0
    · subst h0; simp [mv, gfun]
    · by_cases h1 : j ≤ d
      · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        have e1 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s1_le i (by omega))
        have e2 := sv_shift (M := M) (t := t) hd (i := i) (r := r) (by omega)
          (hv.s2_le i (by omega))
        simp only [mv, if_neg h0, if_pos h1, Nat.add_sub_cancel] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq i (by omega) r hr
      · have e1 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s1 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inl h⟩) r hr)
        have e2 := sv_rd (s := s) (M := M) ht (j := j) (k := M.s2 j) (r := r) (by omega)
          (fun h => htr (Or.inl ⟨j, by omega, hj, Or.inr h⟩) r hr)
        simp only [mv, if_neg h0, if_neg h1] at e1 e2 ⊢
        rw [e1, e2]
        exact hv.w_eq j hj r hr
  out_eq r hr := by
    have e := sv_rd (s := s) (M := M) ht (j := s) (k := M.so) (r := r) hd
      (fun h => htr (Or.inr h) r hr)
    simp only [mv] at e ⊢
    rw [e]
    exact hv.out_eq r hr

theorem pad_mv0 : (mv n s M d t).pad n 0 := by simp [Model.pad, mv]

theorem pad_mv_shift (hv : Valid n s g R M) {i : ℕ} (hi : i < d) (hd : d < s) :
    (mv n s M d t).pad n (i + 1) ↔ M.pad n i := by
  have h1 := hv.s1_le i (by omega)
  have h2 := hv.s2_le i (by omega)
  simp only [Model.pad, mv, if_neg (show ¬ i + 1 = 0 by omega), if_pos (show i + 1 ≤ d by omega),
    Nat.add_sub_cancel]
  unfold phi
  constructor
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs at b c <;> omega
  · rintro ⟨a, b, c⟩; refine ⟨a, ?_, ?_⟩ <;> split_ifs <;> omega

theorem pad_mv_later {j : ℕ} (hj : d < j) (h : M.pad n j) : (mv n s M d t).pad n j := by
  obtain ⟨a, b, c⟩ := h
  simp only [Model.pad, mv, if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j ≤ d by omega)]
  refine ⟨a, ?_, ?_⟩ <;> unfold rd phi <;> split_ifs <;> omega

end move

def ind (n : ℕ) (M : Model) (j : ℕ) : ℕ := if M.pad n j then 0 else 1

def muf (s : ℕ) (a : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range s, (s - j) * a j

def ssum (s : ℕ) (M : Model) : ℕ := ∑ j ∈ Finset.range s, M.s1 j

def meas (n s : ℕ) (M : Model) : ℕ := (s * (n + s) + 1) * muf s (ind n M) + ssum s M

theorem muf_lt (s : ℕ) (a b : ℕ → ℕ) (d : ℕ) (hd : d < s) (hb0 : b 0 = 0)
    (hsh : ∀ i < d, b (i + 1) = a i) (hle : ∀ j, d < j → j < s → b j ≤ a j)
    (hpos : 0 < a d ∨ ∃ i < d, 0 < a i) : muf s b < muf s a := by
  have base : ∑ j ∈ Finset.range (d + 1), (s - j) * b j <
      ∑ j ∈ Finset.range (d + 1), (s - j) * a j := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ, hb0, Nat.mul_zero, Nat.add_zero]
    have e1 : ∑ i ∈ Finset.range d, (s - (i + 1)) * b (i + 1) =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i :=
      Finset.sum_congr rfl fun i hi => by rw [hsh i (Finset.mem_range.1 hi)]
    have e2 : ∑ i ∈ Finset.range d, (s - i) * a i =
        ∑ i ∈ Finset.range d, (s - (i + 1)) * a i + ∑ i ∈ Finset.range d, a i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show s - i = (s - (i + 1)) + 1 by omega, Nat.add_mul, Nat.one_mul]
    rw [e1, e2]
    have : 0 < ∑ i ∈ Finset.range d, a i + (s - d) * a d := by
      rcases hpos with h | ⟨i, hi, h⟩
      · have : 0 < (s - d) * a d := Nat.mul_pos (by omega) h
        omega
      · have := Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hi)
        omega
    omega
  have step : ∀ m, d + 1 ≤ m → m ≤ s → ∑ j ∈ Finset.range m, (s - j) * b j <
      ∑ j ∈ Finset.range m, (s - j) * a j := by
    intro m hm hms
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases h : m + 1 = d + 1
      · rw [h]; exact base
      · rw [Finset.sum_range_succ, Finset.sum_range_succ]
        have := ih (by omega) (by omega)
        have : (s - m) * b m ≤ (s - m) * a m :=
          Nat.mul_le_mul_left _ (hle m (by omega) (by omega))
        omega
  exact step s (by omega) le_rfl

theorem ssum_le {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) :
    ssum s M ≤ s * (n + s) := by
  calc ssum s M ≤ ∑ j ∈ Finset.range s, (n + s) :=
        Finset.sum_le_sum fun j hj => by
          have := hv.s1_le j (Finset.mem_range.1 hj); have := Finset.mem_range.1 hj; omega
    _ = s * (n + s) := by simp

theorem meas_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas n s (mv n s M d t) < meas n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := ssum_le hv'
  unfold meas
  have : (s * (n + s) + 1) * muf s (ind n (mv n s M d t)) + (s * (n + s) + 1) ≤
      (s * (n + s) + 1) * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  omega

def sw (M : Model) (j : ℕ) : Model :=
  { M with s1 := fun i => if i = j then M.s2 j else M.s1 i,
           s2 := fun i => if i = j then M.s1 j else M.s2 i }

theorem valid_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (j : ℕ) : Valid n s g R (sw M j) where
  op_lt := hv.op_lt
  s1_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s2_le i hi
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [sw]; split_ifs with h
    · subst h; exact hv.s1_le i hi
    · exact hv.s2_le i hi
  so_le := hv.so_le
  w_eq i hi r hr := by
    have := hv.w_eq i hi r hr
    have hsv : ∀ k, (sw M j).sv n i k r = M.sv n i k r := fun k => rfl
    simp only [hsv]
    simp only [sw]
    split_ifs with h1
    · subst h1
      rw [this]; unfold gfun
      split_ifs <;> simp [Bool.and_comm, Bool.or_comm]
    · exact this
  out_eq r hr := hv.out_eq r hr

theorem pad_sw {n : ℕ} {M : Model} {j : ℕ} (i : ℕ) : (sw M j).pad n i ↔ M.pad n i := by
  simp only [Model.pad, sw]
  split_ifs with h
  · subst h; constructor <;> rintro ⟨a, b, c⟩ <;> exact ⟨a, c, b⟩
  · rfl

theorem meas_sw {n s : ℕ} {M : Model} {j : ℕ} (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas n s (sw M j) < meas n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas
  rw [hind]
  have : ssum s (sw M j) < ssum s M := by
    apply Finset.sum_lt_sum
    · intro i _
      simp only [sw]; split_ifs with h
      · subst h; omega
      · exact le_rfl
    · exact ⟨j, Finset.mem_range.2 hj, by simp [sw, hlt]⟩
  omega

section triv
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M) {j : ℕ}
  (hj : j < s)
include hv hj

theorem copy_tgt {k : ℕ} (hk : k ≤ n + j) (hw : ∀ r, R r → M.w j r = M.sv n j k r) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  by_cases hk' : k < n + j
  · refine ⟨k + 2, Or.inr (Or.inr ⟨by omega, by omega⟩), fun r hr => ?_⟩
    rw [hw r hr]; simp [tval]
  · refine ⟨0, Or.inl rfl, fun r hr => ?_⟩
    rw [hw r hr]; simp [tval, Model.sv, show ¬ k < n by omega, hk']

omit hv hj in
theorem const_tgt (c : Bool) (hw : ∀ r, R r → M.w j r = c) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  cases c
  · exact ⟨0, Or.inl rfl, fun r hr => by rw [hw r hr]; simp [tval]⟩
  · exact ⟨1, Or.inr (Or.inl rfl), fun r hr => by rw [hw r hr]; simp [tval]⟩

theorem op2_triv (h2 : M.op j = 2) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r :=
  const_tgt true fun r hr => by rw [hv.w_eq j hj r hr, h2]; simp [gfun]

theorem false_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = false) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = false)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · refine const_tgt false fun r hr => ?_
    rw [hw r hr, h0]
    rcases h with h | h <;> simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · rcases h with h | h
      · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
      · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h1]; simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem true_src
    (h : (∀ r, R r → M.sv n j (M.s1 j) r = true) ∨ (∀ r, R r → M.sv n j (M.s2 j) r = true)) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have hop := hv.op_lt j hj
  have hw := hv.w_eq j hj
  by_cases h0 : M.op j = 0
  · rcases h with h | h
    · exact copy_tgt hv hj (hv.s2_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
    · exact copy_tgt hv hj (hv.s1_le j hj) fun r hr => by rw [hw r hr, h0]; simp [gfun, h r hr]
  · by_cases h1 : M.op j = 1
    · refine const_tgt true fun r hr => ?_
      rw [hw r hr, h1]
      rcases h with h | h <;> simp [gfun, h r hr]
    · exact op2_triv hv hj (by omega)

theorem same_src (he : M.s1 j = M.s2 j) :
    ∃ t, TgtOk n j t ∧ ∀ r, R r → M.w j r = tval n M j t r := by
  have := hv.op_lt j hj
  by_cases h2 : M.op j = 2
  · exact op2_triv hv hj h2
  refine copy_tgt hv hj (hv.s1_le j hj) fun r hr => ?_
  rw [hv.w_eq j hj r hr, ← he]
  unfold gfun
  split_ifs <;> first | omega | cases M.sv n j (M.s1 j) r <;> rfl

end triv

theorem pad_w {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    {i : ℕ} (hi : i < s) (hp : M.pad n i) {r : ℕ} (hr : R r) : M.w i r = true := by
  rw [hv.w_eq i hi r hr, hp.1]
  simp [gfun]

theorem exists_nf {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas n s M' < meas n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas_sw hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine ⟨M, hv, {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }⟩
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by have := hall (s - 1 - j) (by omega); rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf⟩ := exists_nf ⟨_, hv⟩
  exact ⟨val n s M, enc_sat hrows hM hnf⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link n s f rows hrows C hC (by omega) hev)

theorem sat_of_check (a : ℕ → Bool) (F : List (List ℕ))
    (h : F.all (fun c => c.any fun l => litVal a l) = true) : FormulaSat F := by
  refine ⟨a, fun c hc => ?_⟩
  have := List.all_eq_true.1 h c hc
  obtain ⟨l, hl, hv⟩ := List.any_eq_true.1 this
  exact ⟨l, hl, hv⟩

end PEqualNP.Outside.L_meta_5473.LRAT.Link

namespace PEqualNP.Outside.L_meta_5473.LRAT.Link

open PEqualNP.Outside.L_meta_5473.LRAT

def lexWord (B : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => lexWord B a m * B + a m

theorem lexWord_lt {B : ℕ} {a : ℕ → ℕ} : ∀ m, (∀ i < m, a i < B) → lexWord B a m < B ^ m
  | 0, _ => by simp [lexWord]
  | m + 1, h => by
    have ih := lexWord_lt m (fun i hi => h i (by omega))
    have hm := h m (by omega)
    have h2 : (lexWord B a m + 1) * B ≤ B ^ m * B := Nat.mul_le_mul_right _ ih
    rw [Nat.add_mul, Nat.one_mul] at h2
    simp only [lexWord, pow_succ]
    omega

theorem lexWord_congr {B : ℕ} {a b : ℕ → ℕ} :
    ∀ m, (∀ i < m, a i = b i) → lexWord B a m = lexWord B b m
  | 0, _ => rfl
  | m + 1, h => by
    simp only [lexWord, lexWord_congr m (fun i hi => h i (by omega)), h m (by omega)]

theorem lexWord_lt_of {B : ℕ} {a b : ℕ → ℕ} {j : ℕ} (hab : ∀ i < j, a i = b i) (hj : b j < a j) :
    ∀ m, j < m → (∀ i < m, b i < B) → lexWord B b m < lexWord B a m
  | 0, h, _ => by omega
  | m + 1, hjm, hb => by
    by_cases h : m = j
    · subst h
      simp only [lexWord, lexWord_congr m hab]
      omega
    · have ih := lexWord_lt_of hab hj m (by omega) (fun i hi => hb i (by omega))
      have hm := hb m (by omega)
      have h2 : (lexWord B b m + 1) * B ≤ lexWord B a m * B := Nat.mul_le_mul_right _ ih
      rw [Nat.add_mul, Nat.one_mul] at h2
      simp only [lexWord]
      omega

def lexKey (n s : ℕ) (M : Model) (j : ℕ) : ℕ := M.s1 j * (3 * (n + s + 1)) + M.s2 j * 3 + M.op j

def lexB (n s : ℕ) : ℕ := 3 * (n + s + 1) * (n + s + 1)

theorem lex3 (K x1 y1 z1 x2 y2 z2 : ℕ) (hy : y1 * 3 + z1 < K) (hz : z1 < 3)
    (h : x1 < x2 ∨ (x1 = x2 ∧ (y1 < y2 ∨ (y1 = y2 ∧ z1 < z2)))) :
    x1 * K + y1 * 3 + z1 < x2 * K + y2 * 3 + z2 := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · have : (x1 + 1) * K ≤ x2 * K := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · omega
  · omega

section keys
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model}

theorem lexKey_lt (hv : Valid n s g R M) {j : ℕ} (hj : j < s) : lexKey n s M j < lexB n s := by
  have h1 := hv.s1_le j hj
  have h2 := hv.s2_le j hj
  have h3 := hv.op_lt j hj
  have : M.s1 j * (3 * (n + s + 1)) ≤ (n + s) * (3 * (n + s + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have e : (n + s) * (3 * (n + s + 1)) + 3 * (n + s + 1) = 3 * (n + s + 1) * (n + s + 1) := by
    ring
  unfold lexKey lexB
  omega

def meas2 (n s : ℕ) (M : Model) : ℕ :=
  lexB n s ^ s * muf s (ind n M) + lexWord (lexB n s) (lexKey n s M) s

theorem lexWord_lt_pow (hv : Valid n s g R M) :
    lexWord (lexB n s) (lexKey n s M) s < lexB n s ^ s :=
  lexWord_lt s fun _ hi => lexKey_lt hv hi

end keys

theorem meas2_mv {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {d t : ℕ}
    (hv : Valid n s g R M) (hv' : Valid n s g R (mv n s M d t)) (hd : d < s)
    (hpos : ¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) : meas2 n s (mv n s M d t) < meas2 n s M := by
  have hlt : muf s (ind n (mv n s M d t)) < muf s (ind n M) := by
    apply muf_lt s (ind n M) (ind n (mv n s M d t)) d hd
    · simp [ind, pad_mv0]
    · intro i hi; simp only [ind, pad_mv_shift hv hi hd]
    · intro j hj _
      unfold ind
      by_cases h1 : (mv n s M d t).pad n j
      · simp [h1]
      · have h2 : ¬ M.pad n j := fun h => h1 (pad_mv_later hj h)
        simp [h1, h2]
    · rcases hpos with h | ⟨i, hi, h⟩
      · left; simp [ind, h]
      · right; exact ⟨i, hi, by simp [ind, h]⟩
  have b1 := lexWord_lt_pow hv'
  have : lexB n s ^ s * muf s (ind n (mv n s M d t)) + lexB n s ^ s ≤
      lexB n s ^ s * muf s (ind n M) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
  unfold meas2
  omega

theorem meas2_sw {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}
    (hv : Valid n s g R M) (hj : j < s) (hlt : M.s2 j < M.s1 j) :
    meas2 n s (sw M j) < meas2 n s M := by
  have hind : ind n (sw M j) = ind n M := by funext i; simp [ind, pad_sw]
  unfold meas2
  rw [hind]
  have hk : lexKey n s (sw M j) j < lexKey n s M j := by
    have h1 := hv.s1_le j hj
    have : (M.s2 j + 1) * (3 * (n + s + 1)) ≤ M.s1 j * (3 * (n + s + 1)) :=
      Nat.mul_le_mul_right _ hlt
    rw [Nat.add_mul, Nat.one_mul] at this
    simp only [lexKey, sw, if_pos rfl, ↓reduceIte]
    omega
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (sw M j)) (j := j)
    (fun i hi => by simp [lexKey, sw, show i ≠ j by omega]) hk s hj
    (fun i hi => lexKey_lt (valid_sw hv j) hi)
  omega

def tsw (n j k : ℕ) : ℕ := if k = n + j then n + j + 1 else if k = n + j + 1 then n + j else k

def xsw (n : ℕ) (M : Model) (j : ℕ) : Model where
  op i := if i = j then M.op (j + 1) else if i = j + 1 then M.op j else M.op i
  s1 i := if i = j then M.s1 (j + 1) else if i = j + 1 then M.s1 j
    else if j + 1 < i then tsw n j (M.s1 i) else M.s1 i
  s2 i := if i = j then M.s2 (j + 1) else if i = j + 1 then M.s2 j
    else if j + 1 < i then tsw n j (M.s2 i) else M.s2 i
  so := tsw n j M.so
  w i r := if i = j then M.w (j + 1) r else if i = j + 1 then M.w j r else M.w i r

section xsw
variable {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} {j : ℕ}

theorem sv_xsw_low {i i' k r : ℕ} (hk : k < n + j) (hi : j ≤ i) (hi' : j ≤ i') :
    (xsw n M j).sv n i k r = M.sv n i' k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · simp only [if_neg h6, if_pos (show k < n + i by omega), if_pos (show k < n + i' by omega),
      xsw, if_neg (show k - n ≠ j by omega), if_neg (show k - n ≠ j + 1 by omega)]

theorem sv_xsw_early {i k r : ℕ} (hi : i < j) : (xsw n M j).sv n i k r = M.sv n i k r := by
  unfold Model.sv
  by_cases h6 : k < n
  · simp [h6]
  · by_cases h7 : k < n + i
    · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
        if_neg (show k - n ≠ j + 1 by omega)]
    · simp only [if_neg h6, if_neg h7]

theorem sv_xsw_late {i k r : ℕ} (hi : j + 1 < i) :
    (xsw n M j).sv n i (tsw n j k) r = M.sv n i k r := by
  unfold tsw
  by_cases h1 : k = n + j
  · subst h1
    simp only [if_pos rfl, ↓reduceIte]
    unfold Model.sv
    simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
      if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
      show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega,
      if_neg (show j + 1 ≠ j by omega), if_pos rfl, ↓reduceIte]
  · by_cases h2 : k = n + j + 1
    · subst h2
      simp only [if_neg h1, if_pos rfl, ↓reduceIte]
      unfold Model.sv
      simp only [if_neg (show ¬ n + j + 1 < n by omega), if_pos (show n + j + 1 < n + i by omega),
        if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + i by omega), xsw,
        show n + j + 1 - n = j + 1 by omega, show n + j - n = j by omega, if_pos rfl, ↓reduceIte]
    · simp only [if_neg h1, if_neg h2]
      unfold Model.sv
      by_cases h6 : k < n
      · simp [h6]
      · by_cases h7 : k < n + i
        · simp only [if_neg h6, if_pos h7, xsw, if_neg (show k - n ≠ j by omega),
            if_neg (show k - n ≠ j + 1 by omega)]
        · simp only [if_neg h6, if_neg h7]

theorem tsw_le {i k : ℕ} (hi : j + 1 ≤ i) (hk : k ≤ n + i) : tsw n j k ≤ n + i := by
  unfold tsw; split_ifs <;> omega

theorem tsw_eq_iff {i k : ℕ} (hi : j + 1 < i) : tsw n j k = n + i ↔ k = n + i := by
  unfold tsw; split_ifs <;> omega

variable (hv : Valid n s g R M) (hj : j + 1 < s) (h1 : M.s1 j < n + j) (h2 : M.s2 j < n + j)
  (h3 : M.s1 (j + 1) < n + j) (h4 : M.s2 (j + 1) < n + j)
include hv hj h1 h2 h3 h4

theorem valid_xsw : Valid n s g R (xsw n M j) where
  op_lt i hi := by
    simp only [xsw]; split_ifs
    · exact hv.op_lt _ hj
    · exact hv.op_lt _ (by omega)
    · exact hv.op_lt _ hi
  s1_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s1_le i hi)
    · exact hv.s1_le i hi
  s2_le i hi := by
    simp only [xsw]; split_ifs with a b c
    · omega
    · omega
    · exact tsw_le (by omega) (hv.s2_le i hi)
    · exact hv.s2_le i hi
  so_le := tsw_le (by omega) hv.so_le
  w_eq i hi r hr := by
    by_cases a : i = j
    · subst a
      have e1 : (xsw n M i).s1 i = M.s1 (i + 1) := by simp [xsw]
      have e2 : (xsw n M i).s2 i = M.s2 (i + 1) := by simp [xsw]
      have e3 : (xsw n M i).op i = M.op (i + 1) := by simp [xsw]
      have e4 : (xsw n M i).w i r = M.w (i + 1) r := by simp [xsw]
      rw [e1, e2, e3, e4, sv_xsw_low h3 le_rfl (Nat.le_succ i),
        sv_xsw_low h4 le_rfl (Nat.le_succ i)]
      exact hv.w_eq (i + 1) hj r hr
    · by_cases b : i = j + 1
      · subst b
        have e1 : (xsw n M j).s1 (j + 1) = M.s1 j := by simp [xsw]
        have e2 : (xsw n M j).s2 (j + 1) = M.s2 j := by simp [xsw]
        have e3 : (xsw n M j).op (j + 1) = M.op j := by simp [xsw]
        have e4 : (xsw n M j).w (j + 1) r = M.w j r := by simp [xsw]
        rw [e1, e2, e3, e4, sv_xsw_low h1 (Nat.le_succ j) le_rfl,
          sv_xsw_low h2 (Nat.le_succ j) le_rfl]
        exact hv.w_eq j (by omega) r hr
      · by_cases c : j + 1 < i
        · have e1 : (xsw n M j).s1 i = tsw n j (M.s1 i) := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = tsw n j (M.s2 i) := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_late c, sv_xsw_late c]
          exact hv.w_eq i hi r hr
        · have e1 : (xsw n M j).s1 i = M.s1 i := by simp [xsw, a, b, c]
          have e2 : (xsw n M j).s2 i = M.s2 i := by simp [xsw, a, b, c]
          have e3 : (xsw n M j).op i = M.op i := by simp [xsw, a, b]
          have e4 : (xsw n M j).w i r = M.w i r := by simp [xsw, a, b]
          rw [e1, e2, e3, e4, sv_xsw_early (by omega), sv_xsw_early (by omega)]
          exact hv.w_eq i hi r hr
  out_eq r hr := by
    have e : (xsw n M j).so = tsw n j M.so := rfl
    rw [e, sv_xsw_late hj]
    exact hv.out_eq r hr

omit hv hj in
theorem ind_xsw : ind n (xsw n M j) = ind n M := by
  funext i
  unfold ind
  have hp : (xsw n M j).pad n i ↔ M.pad n i := by
    by_cases a : i = j
    · subst a
      simp only [Model.pad, xsw, if_pos rfl, ↓reduceIte]
      omega
    · by_cases b : i = j + 1
      · subst b
        simp only [Model.pad, xsw, if_neg a, if_pos rfl, ↓reduceIte]
        omega
      · by_cases c : j + 1 < i
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_pos c, tsw_eq_iff c]
        · simp only [Model.pad, xsw, if_neg a, if_neg b, if_neg c]
  by_cases h : M.pad n i
  · simp [h, hp.2 h]
  · have h' : ¬ (xsw n M j).pad n i := fun h' => h (hp.1 h')
    simp [h, h']

theorem meas2_xsw (hlt : lexKey n s M (j + 1) < lexKey n s M j) :
    meas2 n s (xsw n M j) < meas2 n s M := by
  unfold meas2
  rw [ind_xsw h1 h2 h3 h4]
  have hk : lexKey n s (xsw n M j) j = lexKey n s M (j + 1) := by simp [lexKey, xsw]
  have := lexWord_lt_of (B := lexB n s) (a := lexKey n s M) (b := lexKey n s (xsw n M j))
    (j := j)
    (fun i hi => by
      simp [lexKey, xsw, show i ≠ j by omega, show i ≠ j + 1 by omega,
        show ¬ j + 1 < i by omega])
    (by rw [hk]; exact hlt) s (by omega)
    (fun i hi => lexKey_lt (valid_xsw hv hj h1 h2 h3 h4) hi)
  omega

end xsw

def LexNF (n s : ℕ) (M : Model) : Prop :=
  ∀ j, j + 1 < s → ¬ M.pad n j → M.s1 (j + 1) ≠ n + j → M.s2 (j + 1) ≠ n + j →
    M.s1 j < M.s1 (j + 1) ∨ (M.s1 j = M.s1 (j + 1) ∧ (M.s2 j < M.s2 (j + 1) ∨
      (M.s2 j = M.s2 (j + 1) ∧ M.op j = 0 ∧ M.op (j + 1) = 1)))

theorem nf_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : NF n s M := by
  classical
  have hmv : ∀ d t, d < s → TgtOk n d t →
      (M.Read n s d → ∀ r, R r → M.w d r = tval n M d t r) →
      (¬ M.pad n d ∨ ∃ i < d, ¬ M.pad n i) → False := by
    intro d t hd ht htr hpos
    have hv' := valid_mv hv hd ht htr
    exact hmin _ hv' (meas2_mv hv hv' hd hpos)
  have htriv : ∀ d < s, ¬ M.pad n d →
      (∃ t, TgtOk n d t ∧ ∀ r, R r → M.w d r = tval n M d t r) → False := by
    intro d hd hnp ⟨t, ht, hw⟩
    exact hmv d t hd ht (fun _ => hw) (Or.inl hnp)
  have padOp : ∀ j < s, M.op j = 2 → M.pad n j := by
    intro j hj h2
    by_contra hnp
    exact htriv j hj hnp (op2_triv hv hj h2)
  have noF : ∀ j < s, ¬ M.pad n j → M.s1 j ≠ n + j ∧ M.s2 j ≠ n + j := by
    intro j hj hnp
    by_contra hc
    have hF : M.s1 j = n + j ∨ M.s2 j = n + j := by tauto
    refine htriv j hj hnp (false_src hv hj ?_)
    rcases hF with h | h
    · exact Or.inl fun r _ => by rw [h]; simp [Model.sv]
    · exact Or.inr fun r _ => by rw [h]; simp [Model.sv]
  have padRd : ∀ j < s, ∀ i < j, M.pad n i → M.s1 j ≠ n + i ∧ M.s2 j ≠ n + i := by
    intro j hj i hi hpi
    by_contra hc
    have hT : M.s1 j = n + i ∨ M.s2 j = n + i := by tauto
    have hnp : ¬ M.pad n j := fun hp' => by
      rcases hT with h | h
      · have := hp'.2.1; omega
      · have := hp'.2.2; omega
    have e : ∀ r, R r → M.sv n j (n + i) r = true := by
      intro r hr
      unfold Model.sv
      simp only [if_neg (show ¬ n + i < n by omega), if_pos (show n + i < n + j by omega),
        show n + i - n = i by omega]
      exact pad_w hv (by omega) hpi hr
    refine htriv j hj hnp (true_src hv hj ?_)
    rcases hT with h | h
    · exact Or.inl fun r hr => by rw [h]; exact e r hr
    · exact Or.inr fun r hr => by rw [h]; exact e r hr
  have ord : ∀ j < s, ¬ M.pad n j → M.s1 j < M.s2 j := by
    intro j hj hnp
    by_contra hc
    by_cases he : M.s1 j = M.s2 j
    · exact htriv j hj hnp (same_src hv hj he)
    · exact hmin _ (valid_sw hv j) (meas2_sw hv hj (by omega))
  have pre : ∀ j, j + 1 < s → M.pad n (j + 1) → M.pad n j := by
    intro j hj hp1
    by_contra hnp
    exact hmv (j + 1) 1 hj (Or.inr (Or.inl rfl))
      (fun _ r hr => by rw [pad_w hv hj hp1 hr]; simp [tval]) (Or.inr ⟨j, by omega, hnp⟩)
  have rd : ∀ j < s, ¬ M.pad n j → M.Read n s j := by
    intro j hj hnp
    by_contra hc
    exact hmv j 0 hj (Or.inl rfl) (fun h => absurd h hc) (Or.inl hnp)
  refine {
    pre := pre
    padOp := padOp
    noF := noF
    noPadRd := padRd
    ord := ord
    used := ?_
    out := ?_ }
  · intro j hj hnp
    rcases rd j (by omega) hnp with h | h
    · exact h
    · exfalso
      by_cases hl : M.pad n (s - 1)
      · have hall : ∀ m, m < s → M.pad n (s - 1 - m) := by
          intro m
          induction m with
          | zero => intro _; simpa using hl
          | succ m ih =>
            intro hm
            have := pre (s - 1 - (m + 1)) (by omega)
              (by rw [show s - 1 - (m + 1) + 1 = s - 1 - m by omega]; exact ih (by omega))
            exact this
        exact hnp (by
          have := hall (s - 1 - j) (by omega)
          rwa [show s - 1 - (s - 1 - j) = j by omega] at this)
      · rcases rd (s - 1) (by omega) hl with ⟨i, hi1, hi2, _⟩ | h'
        · omega
        · omega
  · intro hs
    by_cases h6 : M.pad n (s - 1)
    · exact Or.inr h6
    · rcases rd (s - 1) (by omega) h6 with ⟨j, hj1, hj2, _⟩ | h
      · omega
      · left; omega

theorem lex_of_min2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False) : LexNF n s M := by
  have hnf := nf_of_min2 hv hmin
  intro j hj hnp ha hb
  have hnp1 : ¬ M.pad n (j + 1) := fun h => hnp (hnf.pre j hj h)
  have f0 := hnf.noF j (by omega) hnp
  have f1 := hnf.noF (j + 1) hj hnp1
  have l1 := hv.s1_le j (by omega)
  have l2 := hv.s2_le j (by omega)
  have l3 := hv.s1_le (j + 1) hj
  have l4 := hv.s2_le (j + 1) hj
  have h1 : M.s1 j < n + j := by omega
  have h2 : M.s2 j < n + j := by omega
  have h3 : M.s1 (j + 1) < n + j := by omega
  have h4 : M.s2 (j + 1) < n + j := by omega
  have o0 := hv.op_lt j (by omega)
  have o1 := hv.op_lt (j + 1) hj
  have o0' : M.op j ≠ 2 := fun h => hnp (hnf.padOp j (by omega) h)
  have o1' : M.op (j + 1) ≠ 2 := fun h => hnp1 (hnf.padOp (j + 1) hj h)
  
  have hx : lexKey n s M (j + 1) < lexKey n s M j → False := fun hlt =>
    hmin _ (valid_xsw hv hj h1 h2 h3 h4) (meas2_xsw hv hj h1 h2 h3 h4 hlt)
  have hK : ∀ y z : ℕ, y < n + j → z < 3 → y * 3 + z < 3 * (n + s + 1) := by
    intro y z hy hz; omega
  by_contra hc
  rcases lt_trichotomy (M.s1 j) (M.s1 (j + 1)) with e1 | e1 | e1
  · exact hc (Or.inl e1)
  · rcases lt_trichotomy (M.s2 j) (M.s2 (j + 1)) with e2 | e2 | e2
    · exact hc (Or.inr ⟨e1, Or.inl e2⟩)
    · by_cases e3 : M.op j = M.op (j + 1)
      · 
        have hw : ∀ r, R r → M.w (j + 1) r = M.sv n (j + 1) (n + j) r := by
          intro r hr
          have hs : ∀ k, k < n + j → M.sv n (j + 1) k r = M.sv n j k r := by
            intro k hk
            unfold Model.sv
            by_cases h6 : k < n
            · simp [h6]
            · simp only [if_neg h6, if_pos hk, if_pos (show k < n + (j + 1) by omega)]
          rw [hv.w_eq (j + 1) hj r hr, hs _ h3, hs _ h4, ← e1, ← e2, ← e3,
            ← hv.w_eq j (by omega) r hr]
          unfold Model.sv
          simp only [if_neg (show ¬ n + j < n by omega), if_pos (show n + j < n + (j + 1) by omega),
            show n + j - n = j by omega]
        obtain ⟨t, ht, htw⟩ := copy_tgt hv hj (k := n + j) (by omega) hw
        have hv' := valid_mv hv hj ht (fun _ => htw)
        exact hmin _ hv' (meas2_mv hv hv' hj (Or.inl hnp1))
      · have : M.op j = 0 ∧ M.op (j + 1) = 1 ∨ M.op (j + 1) < M.op j := by omega
        rcases this with h | h
        · exact hc (Or.inr ⟨e1, Or.inr ⟨e2, h⟩⟩)
        · apply hx
          unfold lexKey
          exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inr ⟨e2.symm, h⟩⟩)
    · apply hx
      unfold lexKey
      exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inr ⟨e1.symm, Or.inl e2⟩)
  · apply hx
    unfold lexKey
    exact lex3 _ _ _ _ _ _ _ (hK _ _ h4 o1) o1 (Or.inl e1)

theorem exists_nf2 {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} (h : ∃ M, Valid n s g R M) :
    ∃ M, Valid n s g R M ∧ NF n s M ∧ LexNF n s M := by
  classical
  have hex : ∃ m, ∃ M, Valid n s g R M ∧ meas2 n s M = m := by
    obtain ⟨M, h1⟩ := h
    exact ⟨_, M, h1, rfl⟩
  obtain ⟨M, hv, hm⟩ := Nat.find_spec hex
  have hmin : ∀ M', Valid n s g R M' → meas2 n s M' < meas2 n s M → False := by
    intro M' h1 h3
    exact Nat.find_min hex (hm ▸ h3) ⟨M', h1, rfl⟩
  exact ⟨M, hv, nf_of_min2 hv hmin, lex_of_min2 hv hmin⟩

section formula
variable (n s : ℕ)

def lexBase (j : ℕ) : List ℕ :=
  [P (ix n s 7 j 0), P (ix n s 1 (j + 1) (n + j)), P (ix n s 2 (j + 1) (n + j))]

def fLex : List (List ℕ) :=
  (List.range (s - 1)).flatMap fun j =>
    (List.range (n + j + 1)).flatMap fun a =>
      ((List.range a).map fun b => [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) b)] ++ lexBase n s j) ++
      (List.range (n + j + 1)).flatMap fun c =>
        ((List.range c).map fun d =>
          [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) d)] ++
            lexBase n s j) ++
        [[Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 j 1)] ++ lexBase n s j,
         [Q (ix n s 1 j a), Q (ix n s 1 (j + 1) a), Q (ix n s 2 j c), Q (ix n s 2 (j + 1) c),
            Q (ix n s 0 (j + 1) 0)] ++ lexBase n s j]

def enc2 (g : ℕ → Bool) (rows : List ℕ) : List (List ℕ) := enc n s g rows ++ fLex n s

end formula

theorem s_fLex {n s : ℕ} {g : ℕ → Bool} {R : ℕ → Prop} {M : Model} (hv : Valid n s g R M)
    (hn : NF n s M) (hl : LexNF n s M) : ∀ c ∈ fLex n s, ClauseSat (val n s M) c := by
  intro c hc
  simp only [fLex, List.mem_flatMap, List.mem_append, List.mem_map, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨j, hj, a, ha, hc⟩ := hc
  have hj1 : j + 1 < s := Nat.add_lt_of_lt_sub hj
  have hj0 : j < s := Nat.lt_of_succ_lt hj1
  have hb1 : ClauseSat (val n s M) (lexBase n s j) ↔
      M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j := by
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [lexBase, cs_cons, cs_nil, litVal_P, v_pad, v_s1, v_s2, or_false,
      beq_iff_eq, decide_eq_true_eq]
  have happ : ∀ c', ClauseSat (val n s M) (lexBase n s j) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_right _ hl', hv'⟩
  have hfront : ∀ c', (∃ l ∈ c', litVal (val n s M) l = true) →
      ClauseSat (val n s M) (c' ++ lexBase n s j) := fun c' ⟨l, hl', hv'⟩ =>
    ⟨l, List.mem_append_left _ hl', hv'⟩
  by_cases hesc : M.pad n j ∨ M.s1 (j + 1) = n + j ∨ M.s2 (j + 1) = n + j
  · rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;>
      exact happ _ (hb1.2 hesc)
  have hnp : ¬ M.pad n j := fun h => hesc (Or.inl h)
  have L := hl j hj1 hnp (fun h => hesc (Or.inr (Or.inl h)))
    (fun h => hesc (Or.inr (Or.inr h)))
  have hop0 := hn.padOp j hj0
  rcases hc with ⟨b, hb, rfl⟩ | ⟨c', hc', ⟨d, hd, rfl⟩ | rfl | rfl⟩ <;> apply hfront <;>
    simp (disch := (first | omega | (apply wd_lt1; omega) | (apply wd_lt2; assumption))) only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, litVal_Q, v_s1, v_s2, v_op, Bool.not_eq_true', beq_eq_false_iff_ne,
      ne_eq] <;> omega

theorem enc2_sat {n s : ℕ} {g : ℕ → Bool} {rows : List ℕ} {M : Model}
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hv : Valid n s g (· ∈ rows) M) (hn : NF n s M)
    (hl : LexNF n s M) : ∀ c ∈ enc2 n s g rows, ClauseSat (val n s M) c := by
  intro c hc
  rcases List.mem_append.1 hc with h | h
  · exact enc_sat hrows hv hn c h
  · exact s_fLex hv hn hl c h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem link2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (C : Circuit) (hC : Monotone2 C) (hsz : C.size ≤ s)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) :
    FormulaSat (enc2 n s (rowFun n f) rows) := by
  have hv := valid_ofCirc n s (rowFun n f) (· ∈ rows) C hC hsz (fun r _ => hev _)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in

theorem lower_of_unsat2 (n s : ℕ) (f : (Fin n → Bool) → Bool) (rows : List ℕ)
    (hrows : ∀ r ∈ rows, r < 2 ^ n) (hU : ¬ FormulaSat (enc2 n s (rowFun n f) rows)) :
    ∀ C : Circuit, Monotone2 C → (∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x) →
      s + 1 ≤ C.size := by
  intro C hC hev
  by_contra h
  exact hU (link2 n s f rows hrows C hC (by omega) hev)

end PEqualNP.Outside.L_meta_5473.LRAT.Link

namespace PEqualNP.Outside.L_meta_5473.LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5473.LRAT
  PEqualNP.Outside.L_meta_5473.LRAT.Link PEqualNP.Represents

theorem promise_lower (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (hrows : ∀ r ∈ rows, r < 2 ^ n)
    (hU : ¬ FormulaSat (enc2 n s g rows)) (C : Circuit) (hC : Monotone2 C)
    (hev : ∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i) = g r) :
    s + 1 ≤ C.size := by
  by_contra h
  have hv := valid_ofCirc n s g (· ∈ rows) C hC (by simp only [Circuit.size] at h; omega)
    (fun r hr => hev r hr)
  obtain ⟨M, hM, hnf, hlx⟩ := exists_nf2 ⟨_, hv⟩
  exact hU ⟨val n s M, enc2_sat hrows hM hnf hlx⟩

def row44 (u v : Fin 4) : ℕ := 2 ^ (u : ℕ) + 2 ^ (4 + (v : ℕ))

theorem row44_eq : ∀ u v : Fin 4,
    (List.ofFn fun i : Fin (4 + 4) => (row44 u v).testBit i) = oneEach u v := by decide

def rows44 : List ℕ :=
  (List.finRange 4).flatMap fun u => (List.finRange 4).map fun v => row44 u v

theorem rep_lower44 (A : Fin 4 → Fin 4 → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ u v, g (row44 u v) = A u v) (hU : ¬ FormulaSat (enc2 (4 + 4) s g rows44)) :
    ¬ RepSizeAtMost A s := by
  rintro ⟨C, hC, hs, hr⟩
  have hrow : ∀ r ∈ rows44, r < 2 ^ (4 + 4) := by decide
  have := promise_lower (4 + 4) s g rows44 hrow hU C hC (by
    intro r hr'
    simp only [rows44, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hr'
    obtain ⟨u, v, rfl⟩ := hr'
    rw [row44_eq, hr, hg])
  omega

def litRow (r : ℕ) : ℕ := r + 16 * (15 - r)

theorem litRow_eq : ∀ x : Fin 4 → Bool,
    (List.ofFn fun i : Fin (4 + 4) => (litRow (tableIndex x)).testBit i) =
      List.ofFn x ++ List.ofFn fun i => !x i := by decide

def litRows : List ℕ := (List.range 16).map litRow

theorem lit_lower4 (f : (Fin 4 → Bool) → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ x, g (litRow (tableIndex x)) = f x)
    (hU : ¬ FormulaSat (enc2 (4 + 4) s g litRows)) : ¬ HasLitSize 4 f s := by
  rintro ⟨C, hC, hs, hr⟩
  have hrow : ∀ r ∈ litRows, r < 2 ^ (4 + 4) := by decide
  have hall : ∀ r ∈ litRows, ∃ x : Fin 4 → Bool, litRow (tableIndex x) = r := by decide
  have := promise_lower (4 + 4) s g litRows hrow hU C hC (by
    intro r hr'
    obtain ⟨x, rfl⟩ := hall r hr'
    rw [litRow_eq, hr, hg])
  omega

end PEqualNP.Outside.L_meta_5473.LRAT.Promise

namespace PEqualNP.Outside.L_meta_5473.LRAT.Promise

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_5473.LRAT
  PEqualNP.Outside.L_meta_5473.LRAT.Link PEqualNP.Represents

def repRow (n u v : ℕ) : ℕ := 2 ^ u + 2 ^ (n + v)

theorem repRow_testBit {n u : ℕ} (hu : u < n) (v i : ℕ) :
    (repRow n u v).testBit i = (decide (i = u) || decide (i = n + v)) := by
  have h : repRow n u v = 2 ^ (n + v) ||| 2 ^ u := by
    have := Nat.two_pow_add_eq_or_of_lt (i := n + v) (b := 2 ^ u)
      (Nat.pow_lt_pow_right (by norm_num) (by omega)) 1
    rw [mul_one] at this
    rw [← this, repRow, add_comm]
  rw [h, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow, Bool.or_comm]
  congr 1 <;> exact decide_eq_decide.mpr eq_comm

theorem repRow_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    (List.ofFn fun i : Fin (n + m) => (repRow n u v).testBit i) = oneEach u v := by
  have hu := u.2
  apply List.ext_getElem
  · simp [oneEach]
  · intro i h1 h2
    rw [List.getElem_ofFn, repRow_testBit hu]
    simp only [oneEach, List.getElem_append, List.length_ofFn, List.getElem_ofFn]
    split_ifs with h
    · have hne : ¬ i = n + (v : ℕ) := by omega
      simp [Fin.ext_iff, hne]
    · have hne : ¬ i = (u : ℕ) := by omega
      have hiff : i = n + (v : ℕ) ↔ i - n = (v : ℕ) := by omega
      simp [Fin.ext_iff, hne, hiff]

def repRows (n m : ℕ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange m).map fun v => repRow n u v

theorem rep_lower {n m : ℕ} (A : Fin n → Fin m → Bool) (s : ℕ) (g : ℕ → Bool)
    (hg : ∀ (u : Fin n) (v : Fin m), g (repRow n u v) = A u v)
    (hU : ¬ FormulaSat (enc2 (n + m) s g (repRows n m))) : ¬ RepSizeAtMost A s := by
  rintro ⟨C, hC, hs, hr⟩
  have hmem : ∀ r ∈ repRows n m, ∃ (u : Fin n) (v : Fin m), repRow n u v = r := by
    intro r hr'
    simpa [repRows] using hr'
  have hrow : ∀ r ∈ repRows n m, r < 2 ^ (n + m) := by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    refine Nat.lt_pow_two_of_testBit _ fun i hi => ?_
    rw [repRow_testBit u.2]
    have := u.2; have := v.2
    simp; omega
  have := promise_lower (n + m) s g (repRows n m) hrow hU C hC (by
    intro r hr'
    obtain ⟨u, v, rfl⟩ := hmem r hr'
    rw [repRow_eq, hr, hg])
  omega

def gMask (n m M r : ℕ) : Bool := M.testBit (m * Nat.log2 (r % 2 ^ n) + Nat.log2 (r / 2 ^ n))

theorem gMask_row {n m : ℕ} (M : ℕ) (u : Fin n) (v : Fin m) :
    gMask n m M (repRow n u v) = M.testBit (m * u + v) := by
  have hlt : 2 ^ (u : ℕ) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) u.2
  have h1 : repRow n u v % 2 ^ n = 2 ^ (u : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have h2 : repRow n u v / 2 ^ n = 2 ^ (v : ℕ) := by
    rw [repRow, pow_add, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, zero_add]
  rw [gMask, h1, h2, Nat.log2_two_pow, Nat.log2_two_pow]

theorem rep_lower_mask (n m M s : ℕ)
    (hU : ¬ FormulaSat (enc2 (n + m) s (gMask n m M) (repRows n m))) :
    ¬ RepSizeAtMost (fun (u : Fin n) (v : Fin m) => M.testBit (m * u + v)) s :=
  rep_lower (n := n) (m := m) (fun u v => M.testBit (m * u + v)) s (gMask n m M)
    (fun u v => gMask_row (n := n) (m := m) M u v) hU

end PEqualNP.Outside.L_meta_5473.LRAT.Promise

namespace PEqualNP.Outside.L_meta_5473

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_5473.LRAT PEqualNP.Outside.L_meta_5473.LRAT.Link PEqualNP.Outside.L_meta_5473.LRAT.Promise

def certK : List Nat := [
11235582092889474423308157814548672941979455888359052495389318280812252513073621195794513708778555000019919366653249296060512293100791519304696621365054429577291545088838532710567319697106631893509149334811249025707899680813581112748748964518704095527061146072141039704135808659752512724871220247548018098177,
11235582092889474423308157442431404585112356118389416416851180980978274234627838277475860459796565854229327549224355538929732821026082299724390305265494852742984958104454601014954976146733873515902694554437540019234918455366544882444842968621504738341200896077371474993585408924173294723919653723089382932480,
11263013539910499826394562679355972670802070627566178620363214460536290467682097332306794632620459071334854247000784868135199510868259153124659669230199155046020864326349894676947459097755090050858512759666985741562622875645169618260864823695397470500472747889557114504231162022864180459424065414494662164480,
11235582092889474423308157442431404585112356118389416776087523369669348729308635462766351927003168151374314915887913548147697654786265527921294365022283317805793283635275424914020649574544495919128775095685341937109367363608763085235452791473059514155547235897263188757595888763292063272547303317297244471377,
11271585870374753627176240606459878068303761434963639635281982324183765784506210292875135166439377869970586695853011769457988821521075366060371782399212006023174034852105514482524352199608969948823735016266761150993854140696259777834130620442626334265251916215854030497225949907425476352179658867811276554240,
11235583599698453278996578824026553607008079486428898589734467484392490118947864497840267107204068877018742004958031854493431807385676612549226518211977036250588031197497073242388501675874910122828342340700660748741845406428951789735970842206236083368374722900744423407844092155505783116461103599608800477290,
11235582092889474423308157442431405886830080836668583091754610106655210700283621548797710355945658828982777369704541814067257790276684695145631695510758885433799700480274591054955774160118311843558028631087808640854098876897936550174010872577321383522373839548621713168897803657028771916104201645011880640657,
11291816570270394367837535126849235926285103044526365702810331688654320773491965209378520791446252984310981091482045670303060160844797469700454762434362333270442549255016956410706300754830680608501354870342998073494958964697915707050602989920043502375458478386716921798839223745941836132944992118767246901248,
11300731793953220923397397549034782863013323086295719938826893993298791252566475317045861974432874940345248737330096326203898627364048682143101773499126221656220386329113788807035929994289972877409297432473795333342811110013438966791594250298290184777764852232658528885415214251286636432789132967991286333440,
11235582092889474423308157442431404585164721250186255237223080771997391957847705062373530042929778250704848488526113029173313059462566179822332559645139779136287085811549138580101723412990026183894362202711872096101391189554101101624641229550083217251678424436957553699407099579974942455509272437401866731520,
11235584300783188543089770931330482471631075818823641733397715193006473916707926794164815966326171623302941784166406829044212449571119921254683307541701291586187497326374398331624281236423221496884004539363336177243565971712411573482910947388953459913526404783057049881767449129645900399105859511361667596288,
11235584541454065063801840078480833101132118534155606374090140143084650302389505847807469325680509104971704640819056795387771117610058482622875816236735388951885289605689032972507915863155599541790980934622535237986589820752829732430147658182205323289222966369938310117722724069670954349417964647315736100864,
11235582092889474423308157442431404585112356118389417897816112048496629183983564576942425931633823678256233250871953569212791490149421084756685732555076762677498700981144932607736381781168254882046490639180648526023111478514092036434616411725572931657435872083380745906853356249412190180793316056978918047744,
11329534824313117033916225434784824154696651682751771997922213560376392994760555943469299713715840023514439670989887002722794789275183799211478112640000558619541001392460181028494247173159015668747577342118149647917520822610859645106782637577402666323151062265754561427459398860719037182705041202552789532672,
11235585263466703708660227285513487645830118929034122100581475567772126491701670712114267605016982510717101201054626327014641178657331447780160059072939484599550182357057013272712197190149625206551969230325438970200910462229603333081773641524211491363381012693885097369671960554788904707308143592029389684736,
11341189981213752930460834215266758363561288176631113471939036110636074037442683900027209464866545985145189478098613855105340487972378329512360667004347624103225311365481590455440049832317444346365019702608268105032620284666032563228060017857454568260180189438492456307645672866292881965260988249768166162432,
11354566029268741034574175051550082305729606275710547196182830507134145153369633872480621978921845264108298606970457042725237979495277404651512355640587624960597201668085074066729085012603316698943617973974899656391115101725622729280228860963410242438411742601913976852381268019589946984011961641453643366400,
11235582092889474423417899290277064975241781054316318589881003130342944460450860630881672722052212083680719582732543439264883587546984217656912284001132403151906770127742615405455525958597816260678268383059569486207705756458675606548843999337524212680427442116482519656715810683337253141947334327905379320156,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794281884473112875259282244633020544166017028404685607870472100848954536185624728155868206994351654453209029959892783701046633589810720677386663447167647298373562321328844383454026803615676723083389440919330836005067801231360,
11235582092889474423308157442536656408705580253012199998019893144333433544328688174411999900476497748228144943926517351336437570154050266083791130557999871503917901905523163784979445037401453479100329563007423992350440108351150701511252631672539316393353796238007438499190151587307965744305716824087600300032,
11235586184294410066184353641984082148205206992503492025523369432772372831740403556798078991291387237096233008233370974808242284402078470578670115932728105249969981700706118679813500020917037066318823512439899842350017744815765640721085789887656372314448065317614828909004905386295846172526076693292213338493,
11235582092889474423426226584964540560298522280742518184063802132370048157892838481423965520829007108579493481720772146597012837030463287553443150152510389930662836727493150549876741064350794157273010413275058859775595929212772533517633633864247742718748527608625483023080021870246477072017583397682167152640,
11375825408820092925612137475060654390969679506602393217446304262916151466468085201672722214784634244859832189985592844626375457568448419520544105882386285441929733365435396704069771156839509459959993635126689920205202562214709272050579428921540591667585736530801471860356850373513966478807856110230323593216,
11235582092889474423308157442431404585112359471947453715174970466151105873336274349961436337845818459235283042348719520308999850491188968325726522119122685785280152244041995398683312101391245093505466744629410383765079842482229908035655752992114007451912672423377768608157166636253381625967444605330613141504,
11392284283166164966788193907186569466539351843183199183324917345132721954347561851637109622902424062234043156819942794388274808843459567457687324780092718861670688595847709700600339023090979651984858048774200210051873427462815132510908559901965803895607117820141041264967317190524898867212978472101882101760,
11235582092889474423308161699089913350250640128956503679097212256904171375272922838847845681666625944346714932491622536097160233108492567849877208580091070466914782375685663681026025332796572013814707166442235606707364312760547762597137046977630317627837510209120811345898816351734629712346861691321714737152,
11235582092889479257131126254329531117078909931075016573228802455289163036827734391977222370121359085138443234690638907048002496543788871505483240465963455876183716542335480192374470122174245395468334266018240040227310476022753727103654523590332220848391082773780684808640013260205050549306508237504333742080,
11411480945845172066867326067765031836386739353914936302169627691762770383173089676759405254031867415625231797664853535389538245432692595554689620156249480256243427283895337131579145523530601796146721768813916413585418102442587972881969850092099436815358939562633535243810277718892769445216114935216883105792,
11418687060971475797569656985816253758768325586175812340646289696525335675277398487457991516246871851644378202194421089471913305959390856926723294029950278650262776251861549229554526220272335154975041855233067558112839588715660943192089923411210500731881643117028543690883800852779752788579669271831191224320,
11235582092889474423473221347546750557629209751993798702046414959867961765579151986028455112872328061819893162307516025324505972501870462209431908430517182268567184292001515920520241868966004578115732948035435601965065356988851186176681197657133084483153396259302288699881093731422053031758199257246214390295,
11235588005021926183474527909815713247960007500633757499299776887168797024855985861782602578453520644491087162285768008779276107475152739498293826963074912124626550911590033085821502393171360197335666132664818074382359025446942312617501708963640480953178885200409726139367947264779878730566685428105286254592,
11445089838971271667561506634150036369265745774339316546410448696050407902208694804077963974098877673697290055183178147050193362979640809666509749095855898922946129321791226574468995112174885541866192482762457954166664786023179590525671788829873832439262484554934106769598070663271264097646393340246945169408,
11235589083021906683384340108118019845436408657328274532893661369590451056801290336850449198681412848428046133203893315787733764541461534499585215189741084553899408411115369635342987743559394528781661999253787260146089233504456583210560526892945245902067812536849066328132655901664895108872373416295960576612,
11235582092889474423519617690995293294565530741142783587495439373918983630066564818207534680266413394948029075726896932950370053560264423315129496392248764626640090921789289940202435439165541454015223058016924097733962759567609489898840012012429039294948699476604945901303897007073050382607589847420408692736,
11484865452325413915344451251091533696817037885287105538760136718402406259524703992378166987879059507320211693143204200988680275588189492928059747358153421766256101659649179598566066761297859543366757013553952592904054488945555464064697383309315699134346646726172843434214908029095396328518037807143975911424,
11235582092889474423308157442431404585112356118389421504943338388254942802938238591155687591043762209697036055410338982207281327707538773595709594002195170706579094827786968710035432610645811337884506754892732627293152501892801192335764787568134180314369125740871764461960158264980076859962011083865548686040,
11235582092889474423308157442636922619602277418613661116285878581038418880583447147594600636697390192131562958530061554350756745252277941413853761177716183005669688983309968680084648952432303906898926704661255545727521810964095443107170898247958901724211603972078265871476195711050120263160947792978080956416,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195928567344414964159734931141156476549011757941767267253359548093031349949794946204406578209520934065541038016182640218289788231873118633663987941782555850830661798918064895523883256443951169741021475092226989749358552940544000,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550903914121720089255175586115417346737638251231702190312716881865492897614747176293508239345808740880490123642339129139942529366536310459622812575595208041777129240324327742636032,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773612822163472628559975516622121189403934579887320509090514382522196443620835550606053167205435668200726284355910054272197853107994227558109772609748992,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817738115843009320306047986899557542229521787325744840676618664018845011662047442811213304503922265093377622016,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119609848721703048669133947580517716523856832789686623782346539408077881344,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423532102188848158714369744330610791103945147858728197043377609437807260495618831762888212165351522184277139883942577500206183524341083332109439375776423079969295924675870782146010552755023181335084007422849405581756786308717124234512993008721150887870872049881334459922210597526185130852352,
11235582092889474423308164295043602689074594393531477296800734331777613807123502768983070504327897790044496945197496374206052323592930593173315206582858880728251195634278522839196902638115821248544558137328306375233169176836081492222599313451352335218730199673828733138853380846531130740318271721853595680768,
11235582092889474423308157442641083687100026870530674627005231591102269633963795271729433660473339230884443187120823606015706382529526561133368971518156590790104916887718537421303238105122898354310963412290283489353052699007228540023636859383684347720625085056983040442223994776508812519561681247211731550208,
11235582092889474423534488313895467248470952843143051186757653460063563730350350586882375610426989357990761197694884946780594676257879746821178160540358774198663512550532366546108980103799556025413507561575174853204313142911884156613454917869766529087736025702211382243776594005533388866712166966600440741888,
11235582093134092067037174532385372763249331560897148770826154399986457486013871846187112621235458727635060578231031774671331648069135696263181193504879426986680266530309036127250751718130358614203178618729418157191077530122869949638861103903599890913551652243570078185682405009614535797353179822248825978880,
11499601813700178185564729938261269301431524939729295350318135225588417887172031153195537613212522072711197559612181261216708851701478536223469003374893081632104359551448629327562271552978233840410285893951849865131824104508790204927646981299798993051965580993561452916440281017353849540340045185448195129344,
11500981433351679220632529502455270632198684979007324756542362172803013844158591714206261936667736104146252340202558452829897368631249430705772152806305945133269579713636711307064554250960427672622946035919230250236287528846987687516596796920825869771601614349684293496794025593385460043104133450995379208963,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269948057083585924956160,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786677700900533871500815233548741490361461899264,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
11235582092889474423308157442431404585112356118389416079589380072358292237843810195794279832650471001320007117491962084853674360550901038905802964414967132773610493339054092829768888725077880882465817684505312860552384417646403930092119569408801702322709406917786643639996702871154982269052209770601514008576,
95268205270873786358080970147496530326800480428008152797215483387004752771599292606210513399154418065180265231976520474104247304665780191232]

def certP : List Nat := [
11503716408134172439942598145257686371351005954235183869480728589302298043990881074874468568042852491749819635817737821863153808392785859530448264127027206888193792052729255307301053096456437895686301242992253672971244618745405709279879925647677177883240804649571032065782340048527269564435018264144340026126,
11427765574855168955128146133745704811929350429747617341146929597808459821128449198380191825451733202822631748289491956079513325758715060662350501985191556117304125535382570033164139171635183221900166581167241313742827855287327910620008166711604899992661435989791136317464556882527444739471449476215439806431,
12712380031938882608939363332603467487871934035910027648624790167739208274309063471249314476841769163448297883475761391574890661470138898267834490272804605950984628058853649276205992095770366463428726321318907690727309200836728359154921690668348570295749573398638952927208206290081779214954902053441344865053,
11235621741057481080250139023510214600163876103077978112019597863542959229317561451905350180563563406446799541556808879214889798133863474082209266570816373268276373078667637373115395356523156040559919155363209153963272368914382568012548431538133258246931522349268830501285367589510064190135208591095676076039,
11439968414990347567975555870472624790702999598209232680424330428657260007988325345482277537078614353657361729046314167607081623146427973547509992733133174315947006874409322817095758867933863786548852481818164663834833911213943612822647790587123482367729079061143228224334791881883233281732517892398128464674,
11511973918968663114771549333266024778894276944063966919880227514898877670101112437446391884311743433601245423179387744061203911444193334677669588246918355859680657662922069657674549729044376380333621802931828392854010278694468712225112504500188008070947226086435485487157453845223847890368863052843818093193,
11237695758981509243449907471893267646732836827965600652423982302340364240043607355156728889503578934601998232883356537356122659798916820890428609028296906155883334558581582328506149905215257927682290728271357923572974724119463586609729772947202890494746051854919419037983992608242855418087452865334723707693,
15567911075910051176184575644468840332715390502768977088337626750060605981553728801210399886167252826268244406787515854466678937264409911201451666143803369616334622336872709791633771836543248935324766805608658708919688693271059181261388446925175693939572534331646064502534574707337916153308002121423428886448,
11384055996963101423029844033109555275818927639095084436682991590339588478283754173833997015121805660660066099706466622925248038675486194097012813250952447762143677924341176845328118044294421167252892656848713684346375997510475182808519946254877758499521833396184391502597691403848641494406108987555147219111,
11235930657716197582967233592700547216595647348839391773428873405975638127821794903533213376765056846903251687938679854729334712895168698240966217603080368994174343894731268910365754394401862257545888929025701770721047015786009149019100427486748731073210029892462052677304699349146623162216335503979591150662,
13270598126832168283855544458691465528581815909959895802828745347323696537808420441838862490080040594204929042803268175999712336966011024249294079025243207053769050575645490486359194115057142183532492991753558768298503174465570656717628744977102803795238460723985317048272447448892305544808068640635861762873,
18246513955972108886503643462290477568544407599609783919585611908314355223832207733455542217593113189103231519630881121861200506305947162357498071866725632466944329984633717128752779036538505240145354892544552534626039728718911577396468338298373134885393211598408294132725765786164445805081935610301697130505,
14645559350920548549038039563766726252370431993172060553751884879489995026983061954234882922690312875919559180290822260019646917005203666090865166172168090397201626535071275860708684919493228108490773022871947600501283290834624085727411179763470883228009242569775897550603419885158708093854864862298236093202,
12163080373155069748191816765042864177883737591803713654297928460572152731049091801611589839772611290929601494894110774558471781073002662733437729062927855046681902763461541338706062105445309620167519601496417610052753241105652517392840145332757873239972949691115774648717247530137279122211125803260612281112,
12163088680865637783587669978966550009671810469829208067141964984301520909880261373841029419428568264509988502539926024689429003170882302330816033156493956149970299772049297325566205041709463554899268824434049494632569322714621637509293259412258480699803249087311405241096568692495764017971371630141305552938,
12349614157453039090806820676845505528082626419928505153140491138049213917423465300062889901492864620537426585634047755022405909262573527921139156697505908877112269047907735289087086824903934130039042091445947849454906813713780290393609562873115417626388656976565411473021257797005189159533693700088521168140,
12718207197109118428758281334492299688129334658286241833115077205379468872404857679461882445729406775552237925365723561288470008211321182618841639856898634292078805203937545954897676969628127204677274198163914001123160933304858511257512823940538398887997483873312783745929524898962685501436556843017600958898,
12344808746698924303626461758526086202765835940645980592687674734392928417001880069162096236191880126204697842587895156854125482057068857321666827015482735202242323985172527855638567698174356815987907522203054465032849991940406252115875659724182700956408115051566718326074609558557510941119815762218541252782,
12344808746698924303626461758526086202765835940645980592687674734392928417001880067208689714556050162791746585415485652700821498612880022314358404924603471157188749709538077367331805241612268209166460539111493076214117515208771262466782820905348378533129682474930619601483021383606331758481640538608489365803,
12528594174381597067843379284167803587895339599063410197769480506444845173967506639231430445527053322316001326672005965837895080605314787333885298878773490552171146578240668867778753312260939380398208819591742646113704126313341289691630076888101627152515438207589833336640004622867488219519602197284527440171,
11369036899628368880189494228878951191977117742987665972780678555503295068975591187819769898911834675586098259232409148444337018535865445016088022228948634727875825717758762258011903318458054214139988497835404754253672213054895150623845168095099061679312764220995493477746959907402572328416690871025220354165,
11349486795939583521922023779242378344545251390210446286384134130626984424120769180221516611165702038099467256916554187944056289437098537636599151825565337448810180142753271615416291211787716082147936868682546958794036154780721690428582496997277290327552508552531312592991362890682287354841206474026304775233,
16262591296198054330089256229575394585165515443874179750593575008879910006406417443768424772958627955556702162542129704681354266177957608139701829728832435843272913942080769558411173415690717740586053845065299095213192688063027036004059723044584610802816521605702358021836952875052800220892782928949221431617,
11406804888719649197023267692102232083693773509696320990870612088089507089190838008270597616541351093593816444218756406574653162151613288290367522245283987932839068166418040565074653172378098401406671749557986220881962200471512028092791096095729108904991329164570293569678482995351845606557596137618103238986,
12158965675463962061145456753725322153383007013939508223601511332051050740907846069129010054078587004905135754692315408956252215375272518788027319680460118722726572687955126451648459278150411286811933910867525383197521264469375502505603900229368243912000565411048083247885670756085906991495119548123160030831,
11342286279020488285676305444899396515589827956476883244333517644929884692333795741669454835410775544304988485099408479012983079101647790289974382669173358061125233471332273651324211907730651556971759004884244141093800268622894678609483497259286980285060782099250723961579830114729397244528631192834841870380,
11371779961662765724531121434620493724176066784331227669010064518825148434815517048353135339761818463031947429903714558685241343868001914237244012247816360245668572132588829274441669861086828589564716405514254485374275804257834435377836492701754964210984068144122325763633960914506083540116926967681981880645,
12718612132302325797953028887402067888767633325940750826737484756163845206980419532666980838713022972669612870252849285208365709088130151422746369598037862242729507104459313328588908603986397318277240306584109459883894315160704905787401043562749082613479647891430843493302654955805441214679877689756984321005,
12527564374909697853734234368722252465411240565675705025659437755411256528716062354450055477431103695232208543763295173711548173251190776162755706485267340915861911268851349232294760490850331449943176701560065270911095637158642797929953905772726249410221321205028316783930788955198498587299832099849224880669,
11527720170739156099630012792722499703771174397066555034650887996596211760614747491464710491002070890606250844728311217813074638973068924629900095298173031442890463904087909972023905799787564785413472849324825099988407223859987612875957270168031996378433100348848626757053650904640051810670286943366474138352,
12530651408117932439422122483868495673652194845791118149047829932642178292900350734406311378669556587584428162163973228285555228030361040371132287751525744941923670579734084942127126025231695156934307396724142389171022373709228644665203277856497024532051043508464688147765006215220543933382927109103312899231,
12533394501549292680295886410259510911317061040454769597549233705335236213664151282494000962012141002023694365544624299181244903715332771533405916004919938080614702378651950725303204658691219937724274368602508188654203386367307501723616318037750055504505435539650060875605556083070369565309923031598177615878,
11790366421254458764464425903390659368166787951055748603096677118628852628149685433237493434847439114079232888460099423260125906992032258187137608624912647954698297971394877694135210676367826318627440119608248161718725139725303687157732423188041924134433385086670833448025246161773722148518228954349216400212,
16233789238086378914747762288393474738765249959597421171871416039975007696039335328613997093504747053240865248187223483101799077438469708048493218178952899064970208895896601344825948347881025403416307294757942486877418457625012146995388275483737998218134987253674758882065471088015067685932403162474919330326,
11480816646133422622633199089527705633025722662723203176506637556598575378309476930719861265139460857867839697947589772115805725194882494750651783639782812424309582378481035703500089534157194814937320316074201319939948778359125917814579288926446900666252139052735375423443299328710011661497597240986810155137,
12161393699319298371294650002029123903546223366259432584493129707026795372976076841507818622078552783189057913003958676243518544570965140598438104267981895168705316685195798482769137957908885222814997634103609121617597217771890318632876234276137403152119107208181099767761689351882637953182874079026391554909,
11367407097297983394459558414189347776271373239724647620143137425986764898282162847779447614406515409590951168170863401897304624718387692527158579234600211719670990213492649294813677444602490190077312685848807537441435191322892849333221147145771451724475645264803973347165768989717291553030238551187096865428,
11466752729199369819124538024390498813232395817042841082919090105604408760267294833699402981722685309201973805726017871973544475487682959262206833555471691944445585783165931351913656215996051373167499870773079720457115612460866628873586262914595169541681717703287861526164003785458373141499146926608012256224,
13086812049524237947952081858357100612557074129186320697779926682203308543714665843460052101717594198368108525980977111406719924264151131160714978441130982037470167422092955997568401887197438314195755622021722852079382059545457641840027740001811620569527164634372065173590903858285582953806529496769757741914,
12530659255110968642078594276822430790371622532706748703350296371763317620550763856242038924971550155607539196632059640820439280857686822739271452182803932430407927285354160251149139784521595231051104696197885450330309438853321959652574600027675513844278901396828003843011521302237296106708890637122367291961,
15317602435757447926695473109579557513801022778113334803885858897721423887315115220453614774464816811601014555749474340799663804654801970907568122460447001108785701409649158726438514624070801395052725549362481792621484639080091222257921102091905068748172326604430780108875407846921590106856703558707325507916,
11416714794580013741361710172418660322688930556690526937407873764770718708081265790394473835621515728047049174998219854997950608519981042752510727826876616682672716051290806052085032005236392454108172336906648699902443967720600679988522579909985615036634177599754925021390314064876146701763785364165117707009,
11322736311473532734801224997095993153814543162155687433202475600674110237109321376138992775855324649973840527544922863958421314925582417081765999707666581934899957276909826929160064245324696884327010978259439177577802750409110267658390530548622891899399776956415292180411796118920480925517468151689393811585,
14276611150034395953510920273027022872973222004533860901680090336540576911938681679629769408691955963772832805600387128193265991983910399380299645083151462963122789809135551138018697319182973080824115317708642519106166459544586115229915451392568514832164336763349983763401526878763974726148152583227652937511,
11505790665592885171626470819720265523378192789007239579285827675514334033189197520630422104439851024158021063527709860384267898774524065576677036574498770297834128554493879148245232844722373727849872872329395277912178701639506204464729429260805280313881239205116612356944332542701326760266661990433241137346,
15523679179666322725955355409865003358939197481060528358270858391071238525797537203655335586189582988946247917151883935971232454122726942009788691104520994382808258946391156727392917180416645168697452498828675232327629372380507905291592444499357364723638837258285306114134177840022464242581793188724032284184,
13454379788347563340437018080571667622582774149818355829973019121858690591716242285326729300596919551729222489681765286048410571258775647935138843441776358543556640809508589735303367171063332811260087495657683631075313530123523835927326355569352471898186466666343987159704451731025191637791767259514558087337,
14568410702052683961523188885484930363389112818577405175592832097191964183164463177199538781339009041675914375344331375642460825055932942313143229778633038652443842158696529384188223359772698542287445672008174235515209495217082826766248701794327949045928052337512019018878940108506319868722351035390579999045,
13450269046031944830254489441721273696863938922268620679411578499669574231468269190008672209366833877610289792277301347752144100357503593602008590528110738464575520797979305214956619482352976502831452659692392843699321459375279036677275605362826131559754382826712370804772758085785230555715514633082473448135,
11790366421082656408360410719919424599453110043452209969510969906665532860151644230780222532818791002834910333834361834192307383102536115815700141887630012075002692876908578137131884241490635179595774804737374726116424732745807680648147513729836892773695138018875301139254302916760595685663823961349666276021,
16044860306629829134565993091054045780599551245132925719322558131868599813550766654970822609070491838588525705797405511591690107570602654378431701368426555585575945611244458226341147159909650637529996104403669391853903198665747005994167804098665784710287051200946352070455459987986488627974941666039840899074,
14200580067854954019211936376395975627355526702920085773739632503645405156502063030109746626346780987963580465209800232842414954914419082315037233473134708999478947956906325767266392599360526015232008269917474669975730505671993741414342735235815314422680934544433020457701545406990774243891482093642852107083,
14384621331356922582893692715463222449731600610653684937490296169532943658272595364277945251712038115423337861885124515685293240222575600944672862291136681018084362698268840594469708253963210681079751323453529801182573477954497858848877484883162889431462547118436610244726934105784224901332220956790512176042,
13269908251748181093227920052664542920108169423368342778023829083986406515116189787151664883762899144564719617974517076363169500446764653261130609998915492893326749867062196522270408736191849772558506526739552268874544647850275261236365601405788517006370341817799905431453593257306110335708776382023865270782,
12348641575318959281916967608083612606279415762736631494023606119403809506910810093175597493365082200754020317492552408797393359795796237578474668534258406930033845004129474187222134668191757472139360392043137238212303631857155000180847354934767008415185689896543528874641173215698380008243080820098917040401,
14948320795208067631053684862922372651144863230146248027784207846804760923090518424337250303046357600513094287604811929046347833217525724456377310514604705619016951121340226707430627318556916358727266463264591240575009360342216979401948566911004469648185003878984437786646222713696500081013961967805725346984,
14970608215232412937613586342197889852729212653444856502170902810385417488132622609191651745287170622893266465112017047532566640743977050294162067945430273097769183823485765384609469359301760891624358099398605267706201780051072845295175600700790831030684582672409686818954823608215177563094485585414176669718,
13082014881613994892393233559767988310437037515011709339906420282231184649739368789951350939052214126196516487562433615790311806169540452295097145400579652580817916120930975223973612680814405105100955759268285017615072064188126211918962770356899329856289538406075184012235941192531882009331969782018885419413,
15523679158748638953149841490236976007667116184116276154539940240288326985892718044252116255893440951440519129218207656099369840127139336970560514561971910938231190649776189734417208442205981957361824690383683512666735397855198378208753306727330348642569336641560489774921758713341907975894088815499410997256,
11349829699622104965511887445385205123912954362108400502316542526671094168833443327345447841655080643671920436634220692753979826087182116372144361618437760183276140046118504255463103020141798345767504715453782622349292219735569760358282346618485644692446833457485013954322485920198572385098003285165880508933,
11404971876549754562282108305958607217335530111031062404332161804017446121324437505605707559248095868662118323471637413096548503631154419981972009557712244320069228521041589752984651882938668351598946574216710713450732300236689340760368063214983078108092936566521399260159858835447038015393307129656015001923,
16229051221161079278467936127863722006264552065338431168377814150601064742098161815268429702103618452285735093127456669545733129306389191033602790252703475625554699108069211237417195890432744205938392911891499260708320594153790166746527347241667702535824471446969771069570920550256729844404948441846766644839,
11356344586954435557602047251798644282925425381278576363897648305573158675387481908018278072557471568284905716896307613867562491285890273430512200473618656737341097601979127380005113652595934714645347754651873912647808809532597212895332730969037512237078171333060230214923082071824907444237786035507971555328,
13456437375972259739747199827578697383297446739925025264776412123127299739620233272132952128237307569902482533429061357793860192600900170736322957448732674305845651159746768014087685763183271867669475134888579526637624246905850216767594678512009996322379500636211121737374543623392303788574988063900201525702,
11411869001538097777197420759499546643498330250618492103669312823754981002937320946200648775685402606484054803947423123499857046123087927293754754319657284600456489223297898592192246623092105849963964201805390255893043454432366570907131919999669625090336967149131014931563067051139753767704959954927549317956,
12713751730378662576153176385944890444402010088574841095970072502620731919121787004721723606629692827676100041587278220485975402039201863770694169262503446173573858240034594556870992368861332194707955856186862593049173820195656118132868009540014707914753595267064501465564484660819426448841412764244054225243,
11236267858399678435835791913097925282535863114489012482097161341935938021434162998614364241630494783293287923717269639939625611034673651432007653819275708627637837572237677557229179062730215410875342178120864430245817942800889043076325209647408177191490682978844651033055028269484284962403174553909950578879,
11273338707744273782918769476428032496100046953079180424612199049892307135995783939740500442985264889108188833742572884182278263425869818525195995494977262317220322598126463880500510351130728214522268352066177828751676780397031050931676917039799565449666203237698804850909570556899084284168327743649993916819,
11531237508942520786497754954392352387246392263145849055956810258230895987841345471039232370307947255512494582162978402457560093770494624462795676049455107083449646217247755767151512440856041351727853927815724731313591197542845222572567444768712369471650595905532586516823577273643367895659955867057544474241,
11504503903047030878820343767383986531377877437106046992125769835533188000112892977399399656926823976001882550143988499511254751035337067400474909072666242808688598800364675466967350950395276363155105847669372745515542875574583114040432751214083936038497603334405734087473192346649283246627096709775699608440,
11505773704655500443227601945355927616315928038543414312998671347371698910235429125811002956988082817604711371738951114871028090651014681004054198253631310223649207044510912743754974287643117740976482919293234234046811928524565163678667038575222219914205588151673885269068745173272723537238108888233277982293,
11236627682453587789756499828330414913659737798926238999019290589498152752450401436900580333390898709803106042707649661163137330481423823560981950305252609300729606651173506921087204263472305142992477993936774788486882455574797691101891425603182441320452449276497393315245932674665016647744108317590900549144,
12347557671130070683362835973821520550921611367168116305909907936328341914812781570307465157878724257784087691484991500781641559411759663823320912029184801998563961474843742785322239593771308988820283155366739620192796340894780210884524459171554541373948575994311446936386639328249727842948295152284514222977,
11238730057598351195395177350260005360816949838411953378587384929952783983852086448711140155352389312388391081982900443270855355470972989655027667221487468362163604243735654099231389986580120281618161087810118233358044943263445661133003791698226180252795566802554162967905741620100280805827195328727364075953,
11545548156129760213738298054899644828503822240714459008557666025652205490641288869435696589425109765270077017262377940687140933683860658920153693389719095456343055764814860706909734008532191756443835631009992953869548572387323083265780625194656578279843130085921157171935980967745811716451837487854039532422,
13454379665365162249420830671462319524899166365475831478502967389293186404908689195568182094750868195069075484789212184041530169045236972412071711539287954159411987569120822842301016659313821446809155217863953415641557483147625063658536407905818464572688595110545255924458402701580540232227972146991933361320,
11421090757170967984338496008199429901420318239064569325749659230132736932317688315918401651868885094830047239610355667638909460124692025702309533878366804377209110863972438614333937365482584357564435759511757568390925243828896382903862036483863549089136879691493899369861669532836658486957881285114541015351,
13457127887835005958810636883624926596790345497581120724381276806651586485013224307049207177559747042988562494149763007033963187320118757309820903781847400008801561726065627841833784469275416227377540018980761997053751548448062783681970833905689103044844127639033031936391484845209752929079671205266054905857,
14200150071771234038021104488113108893119341159187067722807964307752550638755632592127383910297616916795133733181497404274054186891933782165385446285621746838291927383511285819658561593956937921654978966500841989767477010211493845466594033445462517036344233050349481683474378556187766546359969394037758395153,
12348923182792528131757030296307046179232867525712560716319731259842289245971147462973725428289250428503781902566566359280759820469310606203021717621676557704482902330768977135712933567920427153864551431592559627384384900980531994261771739222138181770105283080603836679604289502977118751970672478700169199932,
11235734818059570954987153665359679094290011056326699486507986806930882358022753244824744824155410170475896069278745114120007422469723540328112261085556546254900935541977616181773853720777366274483688516524498009530957759577129952532257361010714292425294206229339581649762492895168892793114092910587472544650,
18062043242398193044553605628623990111735598299380494858648244385372523683443789091150545385626802632430035696540807660711305666802979461975835059036358374937046745957215037834161641557474547239277071856991494603693835067631202230870632447434175358264722703303393680198847605401005056954311078466178321187694,
11546233874470456812252383880704489118980355796721349031843657463068941557775451690129424665170836667524821615901728106656584101946711057336723309748546915430379133125349108560548836517524600381360639269786938249389326457211976445714457553896699055151080623813993757785927925939047769763969884915572969373703,
14601327467392391456410958809408884186558910234908159194001594132328565942542262277903193941483618308016879291245521983209023238775385312436825493771785221509712170269118632109034024048000294503553314405004551123793539303138456897669399945633501492139227753764378898703701136155078788863831321298724728999081,
13084071531130190567333443704671458872766454152242318891453074737699036201073664887638630620033491461767603155666025671856032712845764993720901943417807847323315173895024395381757751572545128739854829857879672148496663382488148550680407883826356733602282875847363971822481850578210415575683847061474597045132,
13266486180300591345314002267020117719755823446030717497016744465559514069278066381805245515031032987786349406848663113795506363916236072151381543550971763507563713468953055241705374088068738117446661335784327576859097531138870426046531641666099141890185372043668681273914118252968004769638331402523530265390,
11437928143125787338162563752815916691264306224389546705907770843861107997169789803979993864809813986340870343102748988216056427821880453578024318127224387861382528140845166581794110704846164700370049472054897868734989918927928147895667213536303264675056707405341195672504996120526655879112933576124799288208,
11388170590014696689672450808866514575445168077242158338550041790192890640675571700849990578805271122220296009389198432470625685114941057310495108202723924319633473519069346830921031049785647412456925141518030660897172255602620841027927643894692662244865945299206323686372810857089291804315345578762413787537,
11421086214957754330291095830219629656619005765323747402148755225564621045948070343661944046346387906143308125380809704403806756765877284859947114493205361244164274994848831024147003724221207914616695052580553490024400350860681856945289420667578995447051570010484407354703135148754162639435492647411571668905,
11341257609829367669982811288199301978933443670805899017829124169136253466177112274327900774812389955025996612902024564752981439216944560948836091490236867965983301800150722358848559460720631529900899934145650148926824199126586811998806038613353444550487251458611598612670264537188929073513663363370200039425,
13267165145097331922253927909869347122762603866170206400625403879176396210540647319577173466081295744266613599358372546040440122223185405264742701772345055943928350933638580680224351566689099807642678998006052700027331658539178892834456967709130307536678113756278958820027968760491555182651894746724615985469,
11790366421254458775009756790602787402618268317533394250487346315094468941375012226939793987399787785483405262126238540107547378802293911942553947159179719106432467992908558643356192792972264357746835076810348792070052667415471255383322416051782947231876437085597121121055753011254636560797160690213109072134,
12527564378595778065243804959088395848055518699511331802867714238364346067029722466493763634418185302726222833924382189884691612404964547598051576206690742095502438036555720052670230256120319799039183068167026103388440613581008775761285055269322925470387426054945029275245679521019578928133727665719722508807,
11299443451343788520249122812473707973580707277394638774415071201172864420384678439570545267629058595980539145755018057256324623647529777872606628440157258689505160404284554181658347476012398878887214665703438065779514457117552303765012947845703642578616579951452250652806929113242756064723361453329776411103,
11237986522773910738699142838914868329228663188388156176777135036783715581331550743870360922599665140815992720583144437723091836898602140101056267073216839108635332712520848648369432064972149083285619156602146120092053807787209444711671247910420083258497538798514974143656220607791990931092304409787520753580,
12533394501548015069628991634405487890374872728584832444290469736926359312043041009267192094998964321486365383614148545168117140373772596129401384251444508553452594142091091241650312979658961573257755919079411085243889772886387987608739930877282922314636355800226020313096219211060421624184306167665132077622,
15501731154457445132635592450875201494522431838390918730279125950798064184771302678532083786808153584254132030567586979116207588876414903817829420802153882924898321314584009659277996945302655090703977863019106782854331473514096464975852538840415091416434158842089159733362121884168742491946527211000654922106,
11235784781520633768216631745196975872478498304123265905892941924339127592812048127583745460450573064460459537305277542356859000071684576528283201739217434788395807592264810064219599096203047235884709264111444723862527652015914396270288098254624135411865904943434124924502799682277473531903025280479640322230,
11237306259255795695999679448956397523137162698786613344263010859607669994034483600941335644064458146919092014594692544923720103481502003798760088532780820895977934255542896319344716604606150201517274239379597887671797853478273016715531842912435167510191135696961394142038549607725786378006044448754114855540,
12713758971432928762382744164520235929852501629708076137041678416753463819352546060262452298324187795563303712052346033312816367782759218494833011077897427670819619556350356740694782943138166823663782290401211892038711652168739648192478392586745402313232912036538963466226182235449545481360223418069678563256,
14048258180631513431750844595372712233419500597505828960209981995160667869056140989123722020964805375659840771344391125778071916157913397401641590474580971722259524117623593878943423144090949777832672725217544421816299799382179142774869450026424184607622730033199532345774119923548712126498435387374641054574,
16229331605317063916266679142949398783854398001052632614161401700022687288712714134493845889185767810741598095981796339475905130624662174861222492271715361982737550724327539358760181082035043771239425972676449850692785150586008791079773972611332431459901392036761982136580181658127160113538639112853390983975,
11238701836505788176344856771005236156244745987964858099460508749350912056925682438852983374083521792733888633181423785874564537979400914578681870899247726124406348363559531932458591469573193560798399569228889769742079296206927150500722142654232008983164023840598767269778009378549242144851756860059814756485,
11556262624093194944290825416901288901116756269908512226461352299048690111200968820691448980826994508522771293903674171676277263241384824810074660288679505769253314617856633479331584994891890178095188622920301512047279418168752387657431694966775652920666230028031714175762605733135374905391497932820197119776,
11536392313114392332549419319606521626189737490164619609850308874889755380093172475643598490551021688509141765497288589155309812015547317374484011104288075644865486928456427037603810934440059477950946849445208523307561311944076387071072370937045680135685410278251622137431586233829633214875401715838030680291,
11274710249258634229896036772998142694066439108031565440409044233186820943598168118136026166566409699447496291605471363347494847865036301140194419321076705092262292287086846242716459552686537693702817050791496914009991998184052083977220920219934463460017281860393166836404093069884770232387085139958429817704,
11235784790389486818595112051699753490119014083629064297962951075266930551730525592105260609979988110638054126894777177540233400049683566495486870568709890817907997275715005662187125606452454897253077626034597959205859810466348533194282255442879836708563980750813003179104881744906553902916726939086051675851,
13641256677045323419698198562596132516301110114942960025739638891935353044599639293676247202849526152998182288279395793755598787277355472242331169353061339636059988535381649848159122578549722476416846645346753447896750850126354093066859671202075555300695933334102621912640358660258272193527378079263317328657,
12534087958915318380127556146429667727526408654637359675235946621768919314307122656297875104358503919718261772586441299028233072001990903425047895369129467377766425385697809046642464755148477707717334005967419713231104843291931812521453690411219763002396741950482744419007569010189884350004344224329271050762,
16425118045370674970207937974043338928204968193603893032849615897790301345167461804449916378048291810555441345011297889788948569067625031462372100163371864514261230156024741719833769505629643385972986172932744230074091144139862341386355473098743701129086316749591357612451429783268042483795886556826855833727,
12532023306234991122736646705802898707109074132451981610980170858440048937349435726168651716021211552941687615540635337624279619823121558108379312873473527288174181978748786130757045657982372399449298483729083513351006103103229321154869769410023085589470186936462303963702349877722185706680262755381578531341,
12163080331299264740998183072114903093954774664524253812681088957017501379102165840499660567626541096892036833878927673935832343214528395768353558165753366219783856929061505987873712152481083800073503024856693598235300558568651559715629119973418096606774510557549924020406451105331424317574003982178489434474,
11245868576383326437821659644489219379808492552427682300415549554636074789107566398058041150061856013099436565961570989701666618351131890138907704748282532746995242781494298270997465451735527149879695061269933171269322335724775560696996282484843337345204461932900402397343171559860476672759656565169900322854,
11235672891426343879547370995055204366025217682605734224776864051288342689325826615145087228121379464976543534661973899078030383736896948623595647806932796691928828805385593531167883235547700166311786095434254136347013658900912871810041458341052136751997699994222276783986619089063134653595237860920469097107,
12713758971437399309858984442699046425026703934622934734359040274176941368123986980963582975851686503759519371450612510049360625372563224905304486811358997769709846032289060640296722783428118734231483172620101928558020443656044781083197059223968020187136862465303763664910529482846662921633319179948724880302,
14026656251474717938568369423949398424457525864050235415716300156892611913530911904149254796841830040938090629060960820968715703026491787552113950371355041082235590220856413488090891474877006992259405524703498897890709427760513952787884878759763090611856628956810748144375851971648842618687298947489309950844,
14276612820653327246090998837107300608346485863451201517435285789163765696979647976790572999656053979585327498820139124685591073783950343890779311858697070122031300812817975004887249758040044725801936831950455777322383019691527805328118478991416877566963247497004899430448589019093607924792040531910953140416,
11563035229949610590673001218629993892581617215139047491767019624801166194463957608119178014017414311867779731531168603950100328824223489122067882906607880094368140647325522402879590965670225133859960396866917509921399969929529826585505623059554646412554920511538884833474732163872485689467115757698780725601,
11513030736172631858233507629077461781575668359340970037206750546917698994984307667388008907985270915597571370011357520894462008428679850845443929305034025100757111354376286393239468149613145685366915705749985094101295171671674610877216567258863295371701742310120411027920961115741223234542519563154251626724,
11279940550765642139053634473687048748716983659299007762889412722666295710201211382550371115430342998843385623495313893436676295977049643687508424057421806144597271916828273193345683609112808759245898548961538674868714900124935299346322108143949190324260522315972858140611900684353217025466708187762986030343,
11272995793630771823818175704269730086218930086772097158544463687844023583278135998761508492442473416578082734959819085551716418736992487280176612608195911519095358377449040208756540969707449608022021818560518292645235552611443182726599265881189820626047340053418631827863239992427492881328462987605739278023,
14602356158385751470151441163264202214927131072384665379406098690885337545021815027540620793861224317749013308732480508551212218323587394549935138050782525447704179080599491221565405320248845489287947452085207407663640090716828626102263575511244631168141970730019916691504392898183604341759925493581234769599,
11236620653103364997571291247252445817028223106717446850368772283380642379000139126751450942587320205404208949344024469759749522597248830731723457324275199766806922534037785408636881251114314416459231013238087380325670479436050415921167270776169497144497135021260814111489001792974427989538774239702297084781,
11421090757170967984338496008137665135637240344828956971549808227093934384643777986748769402302504770409690837006486413330379235353368520549392727045761311603016049536665706550286345868023216122760710514284963134307483698922958006787478731411208726724102624642072213455228881042050548531465892566586009714688,
13270939805368939189681829371004057360553293716304820386318979005989826309733772346116966716815686332925194300201370691709506062045623051289003179485331079852588145620459852392278845387901118829943007646708894895770579853268878587726732037105660344096383583836153059311061598345991164497342501457476166025217,
12717521430564909498545544239028193710465672049117988232151722220373866100768345555773176205434443506292753224734083734014321959144375487123886368749945841502200918861431003441404268760486434823307386576709386076321778390029247347034245782825108528373280556475236118891467514290021408495608764670529699741696,
16228986953123878075715675260968052163497980172620343541331811064386784345138006351706730109182350142714328832427087960926261252147719027738093628212741844902391387159386232036095306240792137465501491648837546624759416233041216879472670896770693963889318170598334439254753171593052616120525665508323614098354,
15860730060374333817385579344377221272755860687478907529265961065346671058999251775918856564386801271591734810465955752888829366939660341563550163858927415151234990242301386562671293174068042962235995667684134678114246774268612237388576553300592806567190019609488558160291192597865135742382582762929551278512,
12717187851296958385364278767159889098912481623749793715185378006530736329688059295924266799114501111604358743797247335762514540884706972150245354093472283980647170553554801189994823511717459850452860668758707540036893098902662445399245269619132294907653385962214732513617445410248704056514950314830814872174,
14091805366839488190561986159948898750186453434569332476224840537226785234705651162481158696536723224060892382763097024120603995505842897040751676989190524170446914423650043318800284181620463311430596443855119159182999818679830017132259359655694093511785567722674167017492816946412410086350012903241028699007,
12531337508472971728376684948853799856599712090956082101108603115652474689653349474234014432097917658015907876909534763762461091630434887902760443685554679059422232890269762735836166005734284599661837807224155716685105513164018481517271492144306307804531861468762612319572784856131971187769353953866955195200,
15014150373102109050378272121832016200762817997067058528332470320973008701976419976181530727926493028344267146973271377828349984684238133852910582435540733120485167241814912990567327990437606571270630505794570459029959833213544909300519104990720795842883736476426055357217676550881277085609365073930892509538,
11236267863053016782117462210203397441104799854167693750793340704012506899602962865199185724677752566195663886599666393923278539288259244517435495847841815751442628029240418563937338574712558704651311507576783673198626930079333277272240637775927795237813255731765215358654709677597460644175994468221291331818,
11605562423553293389808027316658959810016463274259324653435008110677995377073491756950341727373167114573736479873280934348142671207805594867201664216740803322709001035361540481140702967520799368112577965659865250008562785045863228659051775748183514182538691643295933771514014741625095848624614023242056499327,
11373163254187393888490314192344396036726782217746801163214736860952909499582046724837446821018193259618388518718770504643747530746987393863642461069758745511999985849002559546666175455880403238912161716832289957454519466713031361486679013220557094574517224621092012844674047875360834461668801734717736321899,
11285453504408986847794298602793486530622110250500674147756349283278861894837270063197717603157659621761526652297205616339378650742870346476423125548135534695891011205847958651970462149971754372149305910713269895602385111942493551241542006909984874366447302185721049092954416122827196632489334693843137036291,
15339555920735351915586117253650974992595526190795876906932533864372475465767335784615948910701142021513949673227592781788167513990368816452010877059024173908411796225613024091726396747401508395053405744066806845978449083350005131687005154543397359319599676295507824801449763137339955952990586433200192818885,
13270996173816206380039964298862512904932919326500023553481323166399591327438354949713392802624551760289190910866501183306672015186461426017834498743435431971928139379308238137491716524048400112658279350307245429331863434735640382490749141910785576937515935689107737818676355664985466990273375328784368075230,
11517493862631633766332782095978474627648618820039501254568321453370096277971175643965597388169583056241739294533848340192150480894072884902062244686906609930641725204707683459575991599363479300385723228254728485557633241828743216631993275642910436379871860704093563104991449668767150027405659555157470945764,
11391256545406705938586916011349944031177916898593492102078282459561786835239568884344715205117975322582118445115592748988683616216181393218027729658756580155702158865418956586016132104399727475723642322190759397444307044119378267063989813304407087851186178867063111835123466547515340486089740191651416378527,
13641256677049474837525210058431631880515475802705441274932221530716316464640632691209075759172230014782082717306212911717091803747381314229247898191971101179227652708962926866327650965496667983442458497057023469692881614948684155312747126041699914141555526092807473302356586977745045080297885771560336261661,
15306630104974506432218873466646841295715712040748965477465982981480485274243614345346888516855954684602476333067146117324286974101549843573213202601089445432428535656716149136797078153478688800546752149530663752445289940088351557838406209433559691665237145527346426861435032084739446965632532697891707650989,
15871704199201789004924751237574159045167950087037886027652202536473658022837425028854160128127972376315127773397333874239646980408730461552991166698152914300263372271374336429005061852185417807769888269030006992031335584793605474462993898154221522020365942545985351908119999783428664568610853323183516319864,
11570922128713235580960859914781462983619271757953608975935216716497278162468026103906474402232588685133532690858445890303619388887638897520602598190105856494404759114909951361261481200418407940639455920532872055709246014116715847402141745945546348648331465679536032701130444319569236544040116634621697491368,
15198968500383167271239393143221331783088898343177461685097340198023301040916637764664221805151304243729458901141692097064665749585550500837382515566418188438216047169345687296966675707951955241499217479349524279445387031973568669678043308117878688884527850416873407091291795383715591288934596409757612021553,
15860730039466868773018630509561524011090747149627192878219146982461385561116586380548545726034984059152531849201196039971450428219201620501031973070937667949548121075035385536888499609557455905305696822233735126500113691210383136472395136654538211354326128130617159009714889196817507640138060976232613314837,
14092270535705147464733102689329785911132849490753421192025896856376037652711724931933888895063539656042670261178118583573646190223787684085745501517094603774476547260832909222151922048782174564530490486542667063007210344192235299899096730786577791205576574157153335762263379702889556548295382460295643791770,
11476494113469181785703665053339726015527726366931723874043889703454535279114738115890352595656724519743614466853526705676574380877898969506923346762487620746166650146110218323220498290601952106325766312720790297592534549493565416975481912598166540442348218581444349209905052433785816128160640738464249127999,
14047908288252608980291307560096725231097678709888204032081228211703260245623823388126115739310984067418205492167046688499828439567028813563050758751637162657822282599133453089997964094007919599768583476199943815525903193151848417673291060662278966279344029272677079698299683295031589059301375585552187857213,
15308691501610622042343648244769097235645999975511003469928230475418927450218572874252205422034350779003161183281295901258679743049404340164834828713041580424033208693637683280956799059640004143950120222098530900530152301540930847945443278130957292475335497877111719122909571495899994633626549771199198462330,
11507156567010477590790992273528762919212741640871500249166595340638345196467795235202245131349606053117686152841442205296862734407626834764730688527223400304598139131927121835755616655651363183085363624666612807220283398129888985590170947356047540884739402554134937292545615659605047527661115126002436506099,
11285425356379772693000164810837921339704890155457243790714130722314709085540089516419424392946185462523419060851449312785900737968248281105592927093250272744591773761058733461144933842841514346805501204113823354903229277361013540247796324166558400550891482691475872800400184752610570075503558903580329158171,
11506319283531929869886510170559521278534271049620339496561825181142226433016160108478936399639721601900655852012123007249777659377700041722811540208388679171634673258648438568610658618431631215613488674520503299010869799650318127983906951904510871504531242523506751033271830329492430150416279567140404596421,
11400635280279040364492122171277775606784080933219088302390396670109462556000143835426199599714571292541194212792236536826083059711011881702897711098316082622153093625715218886461583105333525709617599832663151666891822647331132476324102545615557820989196612144460254039627884859895055113403216958001117603416,
11574098857825216686076117298066664493894743152004437007208534922180850323572050908197603183416836926606116519685550140800883117672196009751123943415175583944581242868398633462768025196296480644342098393182979027078553752980363380202735535586660535945619082156782489847346554077193154707844797683351030086083,
11386204706687444848549224627298675810951043386387851406374160088696531126083265196217447871397140591787110129593231974171321553328190119303102993633861279047774315706327164584175601672674195794915530697345312367563629061080268036368586420482203687540272565947678036230220293271979533158082848523071157149642,
13641256677049474837525210058428308079596787474751421130911405572992332605075744102526603847572152432213570794125318579344438860816343635980283449380460565397394853793655898443786021751148914827929093272429887641664563739000551534693858260602279762837272392954494354012038334893702268079067659541938292335141,
15308691504208722289270254883519296933792303788235994842660044358240286355845187914979590616485651912758863072712481434292847366390092577121203616801562400336433270533296942651899076678823673786289105834097246795541254668004736500012635561424863986766198086147020401844883060555511424665557906906196157694518,
14580411651707298997996796519337211830046366838745364269669531649949073865934615951381259263104588508321233903831230298427402276651927359848503092544117372680627965705161083181412693449287431682837317710027873096159040538716673983766539804661441909781380018089688014491720134977490808153676421809117398008307,
11606334777660368504296320335538784801942432346566276233440722153277492917041901451502494407597234130829168629556647713844484214764596693617723396298876957670674430584432048503570993984195455778247831569762387896200054845244695249327012333256571289270420715832468745934475979718844969759985070102318464992025,
11558268762364189400546354389408626731138532961187784167445683046156696434746040147083894210302938406033591551682904226182651676666659168051319438160181356558299865189824910815320348251697419729721594635555652472917971336252432285555386603183363793997494315941495004124690318720119471152563044696216623448064,
14416852247507395422270448529399914343246287783068420150139719749006817631033526639106314946430154785460871220945179167280266021803890720338253623677365480705215715699862560154155424088191944278174084840445917664587403194208532436295354888893042939166013632289597106069979298851829951836972442493382512757675,
11574693138613076305416972847403076453881880329306153534792526044481430138898618559733620642259818504109577726222678557881843108126493911412250338889047453460603577785664372796956374260728633077189825515800274389394032470294626018946497116048558038121247951334883388281598797301759392499483515721351545356793,
11577875182731402619030306796891117462819802024309511945531603801749239213899017401546048558839221015913120789746696679453419097866139181813979863607628266702054834123264255402927367414764056919337679917774366550110575849588380829277162540702207365211520079980255433613392767635530091340350855642798166118628,
14200148357750281678684759411480694273464119413517468297087614186831347075263802754601796312612117706858328401088581974476227502182633838281664396624880451515871687491173661788216139852914556261325526411607207969693325629021177403716033247799669097633772400172026253845637645705805625641660249524726479886665,
12344129910294103908706544406541994447778802674209442224012604627322324291854555661397084488392329343649081110540612381016645797270711108829511143976153517190431190948140292537228993715673409964584901514813115869824232970634625816704713844213224358116501723284995136683537527883320579267790657369840066363903,
12532708725574825937844638091894029872464888202885693826916216457997387872557947376233113682583408600942865579984093188520001987774331196408984778046508730140618393353304370898761370340781103151166674145292356238775036602835649309918021661947390533245822174514996627852460745079310284997445333173272505844465,
11504610499321812578413551528933553264321940194314949748508782759193277526998631554658944487837616328684118594344680494996794204723330443534097296791630076210370442181251534369686617866733643755070495136411901987058306342203349678221076028832577377138619369191507857947877744383485780557571619947615845811175,
11536392982807670085715002787340451052810274099456781392540944747490457981033164501992417231841197645207695454532469004316257561638826997284229537872732582989003260957107019506113730210785951477976128112446185070802951762110158965776157561060585711874370592935793894175574175157009529546892598049048244094549,
11296403202737640422629006396495678100645578239250440890334604124404231129524120046144057261408030643953882304135958010851231959232149463917414418129020728142771148669238751585135369317191530523092190909482671605607505351369507566438739731119765224952161943701319058821854777313167466873980963487761290042216,
11530174853013729681034047657563947118564531852065330300614630769835859520899596755124367154255596004755726275529634606829292551045063408364160135294952267610933605035036936742064757001689442466591108143830074018953995027205109150025018792393763892320099528756334545035358267101968180623518298084187838456356,
12343446790195196451863964589192765906299581253253048329176843901158393355453706063468029612009711353708388487365815821516854817014665201691247183499239132593830763073820332056328669242112295849563394575583724628140023855689403705425786919591594941499453492368149907666926618372650913225749950463134312702091,
11475697105559678586434220745709600850790807537388217329387213370508627612673562227713747452222162999562237766294454117335671055950299408908324145894235944388759676900188688444545730110492919976977763755030592535666592710213439662827014102626987993557956042328750847807969589696549117121247356668193194345348,
11519922503624158230802021329070162496909304392464772989184853634039084009622566277145464632508262846701383120296110661215196501300823321342882603732040269245614584499152023492650207499286706250271469043798816886203600390397946643530932794734732719539688253338170855794323738499096149587692572576821325106889,
11606277968874797050183420067014172633836731608909730492525480555480998765932129441215088365629731071744982710270659970044232637608492000560023073424598962929352636460023574770019114981174606778504835572124958126040480579814530866253271224995301888967996380790992909989307986501087959380736934366548235914407,
11522324880325752430549100836201638155005765265882879127795791847928863808089131439783306975712606222007958194494745418624575620927979702234901035890902417395715794497685735995810409333025457871559802380874293204697941612228407664851931451617814706977544274168951046462362215562555963260805672822941210320843,
11422463052405641259198385784072436587098264097560232989582087277438681142205350128378558680159296752872807351687060356749928455056568946175710977854867607410047041883324920185981568878175063618584523666825939962038101769473551239934257760066956370445116721778922524707391595988788078594436377644407330507949,
11421090757170967985139107200520261148165624324981375200483563177965596639534156084709844260516082541231142336913462635347473827722677748547154244782003832771436317645958997474044175824538824057704127613181773105399040297363292553945273122951844365568791748157803150082829994077922805470357803923329082819501,
11295373884780947156046087715919169618265991423567204659970189431561151104299392847649392330571827154090974735386370664150574575688173856087810959406987153639466728526178837262172617140062281667513982299558899911269528630286662278206177747789869400646582525958158580077456504036867452814327925307086887551935,
11545582016731668061808386707298256685505020516941516058436867173270908650035947825121397594560890755910651553807444978404545336787255233174267656506589798298841600958338081659752959060089184206566510282281553056273070073454661668678280975850895450224800638080246966482769229598112363401811136845069881745892,
12344815696669932195911546471923765313464638776816586032678058041926458456677074586658472920558789783006766481568427202467412997895689542955067934221853019563613825710406348275585541522658510774091028175068733294850319771846209443309809342411431898238101002793295192897399020461104221506682013028612742909094,
11582922365713948074664264698985290801004379587654495083060094873980603903223079907634040840228213661970049121029605746604486140645337933534443940949666296910916636497368250711263100462561096582470719087044601657022471007847767138934467308064528607597769155022488380223970352846025708046731328418682013647604,
11421086354436012857870439930556813553664176391364394161048426865370413868470602037060562405109152959574511952043939744184260269101973050923191957847351648232640575463255618222680970695854031402051220717645627053471842163653852933036379016262874616656461654929489084243785699019739681338644133097819653644235,
12158965679114597662515919651705450770040997759895410742599998340832739338560359227923463513688055219577191092712447606858036812590650611967493691757258739716217220769111414065953359217659556366991604171427661859352861520535591908244805050280582801787512085866949754905311154850524542869386345547892228292609,
11574795882682330619153785847948826503329973216615025853474874869453212637369351654973887912041147668477671062409873542007507416552664382039495731179104511675206670222595997381278983027149412733225835964398291910755191518737094164963985221741857639654239240803947569050616587819087422763518148323573328609312,
11272652889948250399719261134447652396642268692492650083666964877083418155875128066803684396972938704788658352851556572580392454181918998127383984137050214149197338118513052017352639210293330807601789995698580073071542842431110557663599238725134975274146650293397507629725094276457567162579337828391284674788,
12533061056216085282386153606215160654925653556134228923109239108237682409190090218888682858299341612427783600526700631925336742197882011227224788456609376999783730530615538897537551556742819878784615759517706731249583681026179688937069677336465386066087012606625327099869223999119984232204680157739053649597,
12718217477514583972862613868317339442326777719316480937843897875499497188813799674338596385529555906953392483614811055901229772391600822504550089412013646505671267987722404566354019166513667738231276346227744950275172589996446338964900606281747650074503608477241089252072831756122964236075368624140713078401,
13450950911080043638688135393870287366145493795248649812819814964242131814431364006872281567694600850296159890428862800726320293402326841036503814043097101554966801795545760470580414960941707750681635213090990336100449084871208693499285209834189885431989147893749914896787859071337905343608396106794230711075,
11474296139548780182798990453401069895417459960029264723277410408130551929011729843567675563057077880813821744040865496744788090828511588984352577260205910995255352763239683583248840277920542096570411056843850613342373189901134876250596069113850789112999304933059282974698916928184393002121895547511527932224,
11585424285382716556612555272616909359036047767530071752621217143250214559575724263133400419647934739883765235227215701556066926229728352321664807164051169600469624450277378996790476086767780652461757439343352485722293684622983835983598588022107704803069665438140818837906795754968131118767418493731990182211,
11410862871957780011587442636018725885192612454094302232451199707151488736096959201898565046515303076764597325371492816555547084863013783646254676316496147998329870437709543023941626795504322219819543065042638666796687565579970890295190967305108342790453424603411057176886198161924511418675198224878905230392,
15383439799070402054448516553179272463539035782026716758811459340454146365465190450402888311152069181447482057934871978863372951398195672470127520046583847669058672030458847206794620415170422143465445659894761565800582697868334376727455426718592557771137122480205933746133109934735794126844147582245099354972,
14210434693893532393564331511669940777132796547649426759673931492818940032509802231626457695505560375071703548565059828499686772255474901398310137446074071517130553288249643461687468262828488838999619567556715835553026074303558378189212352978463885617251716368015591352518895335410722420561591146269200187730,
11558622893880790290518475763405225070976220732861674670506072224596729755480386137499431336532995573544423929481825604955162131571971546067067161085511256305662552448725441207588259699318333514871012466088628408396043360465706075448904356967226874822443426577729264365956991042620934536199045560846989984248,
12528975355196513529832685444998719416598035255192203945261065499123211874261994158669109750840649817749691377242510721679158544347341344311465748799054767640886058474486080748770105318008869412580778453330014965537881057524359908616097137299427761100794132755845268578994597604034735092095844724729909248545,
15306291092126461957494565546501607997837183579978425698858484660091762788323282913616350276955222384604925831516961016922896088122495692413412902355411073831157759100660769460156387545648297104636281222940989693846577838084111993565495008763369942416820837231542806454370939350992015444751729237599524757418,
18062043242398193043587344178534246872707890567344899017592638215557327715499673893346837549175703178259527444767959908296468721118189909653051235551613035880629959857752737911649354015848060352429551274734898949117177569631781840645213802138110054300915892776272904792413792971060083798995577926061440237671,
15495559611428815871624406479087655142862334953166174368981835754461555194655373539248937183495134345396925896394309221375622966634149549994944220401787625396977373774045982644447866058800961172628343604431220963707384214077888464647970958679950485571615066452798887293764216338792115227780830231897301222180,
11237679016622516048095933057226726299007526757188891736649011411320955547067479016227119736832324512550930571253870073301278341271399178196540255880006910102232415662559035453375899430067573589028094509287346715218483770366602113712018803222443762043295317559536154823667026432415321820564091479507079365135,
11790057473613668565338835954144260465716867193190782939004104645334936731064943280951138317991415261594730199591462809156726994443573741594032657372676021137177158809573499014225526244768307971207919552478846390656389748220628263612441376454862343659642052336413574636006143559413349295020108170454911157255,
11363978248822635592941502434363270044122624075950069234720336142972707775902874499937138171884374071334898344970819084635948245939438647418100293718386118589270975430403583166591506268970766537320170400599271008153657014449888695864549043869332359688872320779048507205431744089349919485671781801228484221260,
12532032606623495520307794955742294892030657719207331191755298821774978748202643506202184423203910695348291553650967771650745603244214860910754449234855900368003399437901751079596001782322526460105374982927061990823014555857708923120048226427774945063542401118024332397615434880672035327638360628042296271838,
11327571086009049542418690555468081028318836237894865505737663642068570542555152760111389838861132581970381875594769517246828686119545052603570279570950718084616858998269022073104731246924143282346068522188765815790324493342569687757394919590146449096012856585946641492031305662000685789444386401447770986824,
13641256677054903424107135669213961161273161945864549117341657327795129375604121543084958573209107364050592837890472706118768209219030099937551974776336697211804821546527842397482568851610137720393744367772594280020137857187880668879258015687516541952602485845590246791075893587992424531336995869943214940107,
12530658262007279722444978950284176738065347934572759803914214172441236530855110667435415996022691118599276617184796834292265742687768929613603982969144742421652398021439911381746622307035263542288259838438807002592836787706678651507470867349034796850694875210357347156360565153757947735488171200158742643631,
11591504376529643635143817396365388092161221835844874333161636122039353680778183433942035106214361498285703807446661499571510812535082685292146888211486067551019127387748586686176436215980085253654425371863760512758482326893369093026527209265895101988706587207125061548661401193745220698227970000528146334693,
11513171308899077727371256984439863442767914999947763641501502455814938290585028058542615452642236729696387194380468753149041030957238158186110333464945222595597961161080883272951996129107069817151064553220234083715366975447137328264966913199348599106172431460814685923775859337365881824448207756058191731020,
11329959671193143591068525615274680836976126044359532110405081157943693141525308889608408267952602536606883319769553939160637911000723041947231853979892285766229548079821251903661255938677544123665410396926151051143883176611334533168297327629700889042959261526952810591218147592504613180843939007186977232135,
11285367846463190989924622071076622888129259793758643782363276310416960402459471058157766935633077705402569483019084851048292780574083973342125864626334738886466176543904446116138701197361993247794267593973312306594396633162373063190419402442658269061700946175872072775822988070417938702031051723650902663178,
11591528347393756445383068656914119035681086449655078002619387910329162402968690164601667012192158954223428762998647100895682594163792256347410383017110188175786601894944472792429195577943632772163452443834238618382338506008352745352689479943252173485554959945540419160072334422778042395256699509251980725957,
11790091284396082612615720183709902174339860322906421429476311849406719855248397125665200132377848963229856258971169900985281925209283232542722198371892187049102461397837732463390500021440638704787606242090966750436146210604626009917103447513446306714380160618107938156789983462004884071109369860217098246476,
11293659136162050755574466253336406761015356499209866059674533019615091872700450981979684203751294489373652950610433044757647715216159265815987213295333974498094631547883868851149987899152509143015333826728063568141668049496566366268640503089403551375294839545970021752118555482301312949448154533053430923264,
13450272582846190279630443617707250705805107027802126326250938349234688517625174515660689675795151549031747194305595563590712235943337967558939543113657516331888641590330734457834044143154093082128256568668641341306228494018051966076602578585635935336020360563671874313335281302970694298705235277495037501892,
13270968015484030426271264006007713337127321233655891734936150513357031243204185911452301236247508667492962345157398955550225830921660205766317824499886331744675514779506821175036765521265906908570958994823534913568007890874191803019539216838088960966394004645130106026274681736424196025254418966786431550027,
11325822339977671251454977595759696254529816771344764900977779235756844911595904770220012885712008117410990434414348981028550861299505345558025903281432498270578785588004384610590379383256895130712298310394859310852689067948467968049818704825531978004339119849452416870684985228656417319654313608472269162065,
11594440151386870665708567812401679359087664312692084484982608226445837757412059354151838431953591575194825368134516532411276769899010345040997287014185670579204827339530533225395172523254375458997569367051532025251139177050467933231333135362794734196281605425989865611284154275085492655055651499238238656297,
14200148357750281677719983121805998382878714698205350368410212782570643329749896078541116964096327229251382003904064333433290594527511987933493913691829218052435578989124953445758601063641954650856723444125805998342795093636199517625302862577926460467082254400527078074087443762330965688450447045280927681703,
11594243115188255071904472708273765187477837119386634240917317484381633187160979025010824242910947051801934786134523467926118602954068103014214317100749155137476200277492332428870116724243060215274765541369753238807664676676843505872122898484390315001856039792896869976982682728543789994234221923372444287484,
15318292157686393139548655213590498067772345869639255099253071193307204127082347993170313699171566209157046103689792558618355124833771186651827133128688171761534604161206635721243302739559968649066756507051709770224942205332263776748703519041209585981910897876977241444395985528800904799518962090129861938343,
11408485786353137117623268756062223263307280304430937947267322076154565720351530424771320260560067909679560477633781447442510850910401988497754204999391829418430101399713221717063127182020064917060459473986723892862221951201342686256347981626565599306943603812829282847186299841039893762725379180519255015568,
11421086208011587680191878446676521821328796202668950016336227064456754275901689178910145830479058797397624072241136010387738554212619296272773065309690469218042172053803740856177000153974739832420304774611169819041437310483714010574531926233076204928459214924898595964489872880179648857657887098111939358842,
11235712024111823973779471933450826933153991405644006620706467828626948880177272665679435675988198194542622618195175641025238705851408499287427428446088983734994225931856026982931863803138078980851190693294772532401260214815136083578241476036905612851309257616573280815453045555730759320926068262763173445633,
12718217475323312159401299562447468062971633792130208387954394798022541347062083140703603170000769007666645865337986766705543328448174927300051077392018962394190107961446740865803991927483808796373874593608402218026335380960505393847547221287583224671491950892941797520539893752162826374989861823273801155617,
11235706687502118858761274740813559554285655601776587251214317876252540472821534936977653999895655848101919751928396826644786126203268510841760529997275839991127996643193596979272214266989863798666335661651247050404185234376384686840377211826786857613659044475276367570419347902040443516237403634103880286405,
16240652958468220990574750000161828904501083449859136074327443922185007971544809593916149162783846229007496038853758961272160037425976400834899859028987222484376100277819223537816932538300468568169005102498600169040399052395679717825040670075845285802614722586743692763608341796201510930519846978589089104943,
11612417570988247724585063222867069466952602487627906896997606071587077681280611713089246867833950478771090363159328480256305440082806907462591706792739703336613317893805731269388363957713133502448995898572414128011615280451292464563997641454083127243964822069978914952714245330580211399742526013588069515622,
13453702038223068321821135056721859955200820132059813632615929244985500835517587849198546165965720237744360567541750205909849664357299915440773148621974925037158160605698333563951003626793763504270260228919508916901498678919319325110493570796122154129993069309683101845871973033584388784096542108143253987467,
15501740958153498781405668985746270248448392930068006584004322646243781338078083343117954979895178688141010622798831687433285979079369450664218028736090990489623258724421540707348991113422592846998543347949725350246707382786444198516771105354624253276633128692022880010230986294516010646797958858165860303864,
11300432179893213249240490269798841053843208131782809815764972226235497986948339385708580959467275820171208417459758275321212726759460468271879825727497430478372567873277136038104790306979244354526830244715579077129027135760014969043677975693230744539504195747623896371739705186999729981759288119103423479808,
11375135395171564423859209603344760228295435014355988935637477665261676345692464595373661208603945721418723985112924858202522928627125922380157799588108503495808147823500052700722693740601188902845700698960198805294281165416922029085973601730020600507665656586414245842710312809023171444341886028785370727519,
11399605292837002459624873674867293023685664063728511357375663111322729278909854313978923325980026173317289948129401069266815511634869426855021703470571551456599566010694494730742962244283038298920595394147289849104838414597233534601795823013160838070543367490405025753889665044022075282431193965305528353895,
44058875752144627467916279266218329769070]

def certW : Nat := 15

set_option maxRecDepth 100000 in
theorem accepted :
    checkW (enc2 (4 + 4) 4 (gMask 4 4 23) (repRows 4 4)) (unpack certW certK) certW certP = true := by
  decide +kernel

theorem unsat : ¬ FormulaSat (enc2 (4 + 4) 4 (gMask 4 4 23) (repRows 4 4)) :=
  checkW_sound _ _ _ _ accepted

def upC : Circuit := ⟨[⟨GateOp.or, [4,5]⟩, ⟨GateOp.or, [8,6]⟩, ⟨GateOp.and, [0,9]⟩, ⟨GateOp.and, [1,4]⟩, ⟨GateOp.or, [10,11]⟩], 12⟩

theorem upMono : Monotone2 upC := by
  intro g hg
  simp only [upC, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

theorem upRep : Represents (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) upC := by
  decide

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  rep_lower_mask 4 4 23 4 unsat

end PEqualNP.Outside.L_meta_5473

theorem PEqualNP.Outside.L_meta_5473 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (23 : ℕ).testBit (4 * u.val + v.val)) 4 :=
  ⟨⟨PEqualNP.Outside.L_meta_5473.upC, PEqualNP.Outside.L_meta_5473.upMono, by decide, PEqualNP.Outside.L_meta_5473.upRep⟩, PEqualNP.Outside.L_meta_5473.lower⟩
