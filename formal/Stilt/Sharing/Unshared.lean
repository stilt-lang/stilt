import Stilt.Sharing.Evacuate

/-!
# Stopping sharing when every binding is live

When a frame of copies and a state of sharing agree on every binding, `unshare` succeeds, every
binding reads what it read, and the binding that stops sharing refers to its home, which no
other binding's part overlaps: a binding that referred to another's storage gets a new home, and
otherwise every other binding that referred into its home gets one (modes.shared-writes).
-/

namespace Stilt.Sharing

open InPlace (Ref)
open Moving (keep)

theorem Holds.reads {st : Array Value} :
    ∀ {fr : Copy.Frame} {env : List (Name × Entry)}, Holds st fr env →
      ∀ ye ∈ env, ∃ v, deref ⟨[], st⟩ ye.2.ref [] = .ok v
  | [], [], _, _, h => by simp at h
  | (_, v) :: _, (_, _) :: _, ⟨_, h₂, h₃⟩, ye, hye => by
    rcases List.mem_cons.1 hye with rfl | hye
    · exact ⟨v, h₂⟩
    · exact Holds.reads h₃ ye hye
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

theorem AgreesAll.holds_all {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) :
    Holds s.store fr s.env := by
  have := h.holds
  rwa [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp)
    (by simp [h.len_env.symm])] at this

theorem AgreesAll.reads {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) :
    ∀ ye ∈ s.env, ∃ v, deref s ye.2.ref [] = .ok v := fun ye hye => by
  obtain ⟨v, hv⟩ := h.holds_all.reads ye hye
  exact ⟨v, (deref_env s [] _ _).symm.trans hv |>.trans rfl⟩

theorem ReadsAlike.names {st st' : Array Value} :
    ∀ {env env' : List (Name × Entry)}, ReadsAlike st st' env env' →
      env'.map Prod.fst = env.map Prod.fst
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨⟨hn, _⟩, h⟩ => by simp [hn, ReadsAlike.names h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- A frame of copies agrees on every binding with a state whose bindings read what another
agreeing state's read, keep their homes apart, and refer into the store. -/
theorem AgreesAll.of_alike {fr : Copy.Frame} {s s' : State} (h : AgreesAll fr s)
    (hr : ReadsAlike s.store s'.store s.env s'.env)
    (has : ∀ ye ∈ s'.env, s'.Has ye.2.home ∧ s'.Has ye.2.ref)
    (homes : s'.env.Pairwise fun a b => overlaps a.2.home b.2.home = false) :
    AgreesAll fr s' := by
  have hn := hr.names
  have halign : fr.map Prod.fst = s'.env.map Prod.fst := h.align.trans hn.symm
  have hlen : fr.length = s'.env.length := by
    rw [← List.length_map (f := Prod.fst), halign, List.length_map]
  refine ⟨by simp, halign, ?_, has, homes, h.safe⟩
  rw [Moving.keep_all (by simp) (by simp), Moving.keep_all (by simp) (by simp [hlen])]
  exact h.holds_all.alike hr

/-- Each binding after `evacuate` is one from before, or a settled one: it keeps the verdict of
the binding it was, refers to no other's storage, and has a new home at the root of a new
location. -/
theorem Evacuated.mem_settled {region : Ref} {skip : Nat} {s s' : State} :
    ∀ {i : Nat} {env env' : List (Name × Entry)}, Evacuated region skip s s' i env env' →
      ∀ yb ∈ env', (∃ ya ∈ env, ya.2 = yb.2) ∨
        ∃ ya ∈ env, yb.2.unique = ya.2.unique ∧ yb.2.alias = none ∧
          s.store.size ≤ yb.2.home.loc ∧ yb.2.home.path = []
  | _, [], [], _, _, hyb => by simp at hyb
  | _, (y, e) :: _, (y', e') :: _, ⟨_, hu, _, _, _, h₆, h₇⟩, yb, hyb => by
    rcases List.mem_cons.1 hyb with rfl | hyb
    · split at h₆
      · exact .inr ⟨(y, e), List.mem_cons_self, hu, h₆.1, h₆.2.1, h₆.2.2⟩
      · exact .inl ⟨(y, e), List.mem_cons_self, h₆.symm⟩
    · rcases Evacuated.mem_settled h₇ yb hyb with ⟨ya, hya, h⟩ | ⟨ya, hya, h⟩
      · exact .inl ⟨ya, List.mem_cons_of_mem _ hya, h⟩
      · exact .inr ⟨ya, List.mem_cons_of_mem _ hya, h⟩

/-- A state follows from another whose store it grows when each of its bindings is one of the
other's, or refers to its own home, past the other's store. -/
theorem Follows.of_settled {s s' : State} (hg : Grows s.store s'.store)
    (hm : ∀ yb ∈ s'.env, (∃ ya ∈ s.env, ya.2 = yb.2) ∨
      (yb.2.alias = none ∧ s.store.size ≤ yb.2.home.loc)) (hk : Kept s s') : Follows s s' := by
  refine ⟨Evolves.grows hg, fun P hP i q hq hi => ?_, hk⟩
  obtain ⟨yb, hyb, hP⟩ := List.mem_flatMap.1 hP
  rcases hm yb hyb with ⟨ya, hya, he⟩ | ⟨ha, hl⟩
  · exact ⟨P, List.mem_flatMap.2 ⟨ya, hya, by rw [he]; exact hP⟩, [], by rw [List.append_nil]⟩
  · have hr : yb.2.ref = yb.2.home := by simp [Entry.ref, ha]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · simp only [InPlace.Ref.toPath, List.cons.injEq, Step.index.injEq] at hq
      omega
    · rw [hr] at hq
      simp only [InPlace.Ref.toPath, List.cons.injEq, Step.index.injEq] at hq
      omega

/-- Every binding stays shared through `evacuate`, and a settled one's home is a location's
root. -/
theorem AllShared.evacuated {region : Ref} {skip i : Nat} {s s' : State} (h : AllShared s)
    (hev : Evacuated region skip s s' i s.env s'.env) : AllShared s' := by
  refine ⟨fun yb hyb => ?_, fun yb hyb => ?_, fun yb hyb => ?_⟩
  · rcases hev.mem_settled yb hyb with ⟨ya, hya, he⟩ | ⟨ya, hya, hu, -⟩
    · rw [← he]
      exact h.shared ya hya
    · rw [hu]
      exact h.shared ya hya
  · rcases hev.mem_settled yb hyb with ⟨ya, hya, he⟩ | ⟨-, -, -, -, -, hp⟩
    · rw [← he]
      exact h.homes ya hya
    · exact .inl hp
  · rcases hev.mem_settled yb hyb with ⟨ya, hya, he⟩ | ⟨-, -, -, ha, -, -⟩
    · rw [← he]
      exact h.inout ya hya
    · exact fun _ => ha

/-- Two different bindings of a frame whose homes are apart have homes apart. -/
theorem homes_apart_of_mem :
    ∀ {env : List (Name × Entry)}, env.Pairwise (fun a b => overlaps a.2.home b.2.home = false) →
      ∀ {a b : Name × Entry}, a ∈ env → b ∈ env → a ≠ b → overlaps a.2.home b.2.home = false
  | [], _, _, _, ha, _, _ => by simp at ha
  | c :: env, hp, a, b, ha, hb, hab => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact hp.1 b hb'
    · exact (overlaps_comm _ _).trans (hp.1 a ha')
    · exact homes_apart_of_mem hp.2 ha' hb' hab

/-- A binding after `evacuate` that isn't the one at `skip` is one from before that referred into
no part overlapping `region`, or a settled one, which refers to its own new home. -/
theorem Evacuated.unmoved {region : Ref} {skip : Nat} {s s' : State} {e : Entry} :
    ∀ {k : Nat} {env env' : List (Name × Entry)}, Evacuated region skip s s' k env env' →
      (∀ j ye, env[j]? = some ye → j + k = skip → ye.2 = e) →
      ∀ yb ∈ env', yb.2 ≠ e →
        (∃ ya ∈ env, ya.2 = yb.2 ∧ ya.2.alias.any (overlaps region) = false) ∨
          (yb.2.alias = none ∧ s.store.size ≤ yb.2.home.loc)
  | _, [], [], _, _, _, hyb, _ => by simp at hyb
  | k, (y, e₀) :: rest, (y', e') :: rest', ⟨_, _, _, _, _, h₆, h₇⟩, hs, yb, hyb, hne => by
    rcases List.mem_cons.1 hyb with rfl | hyb
    · split at h₆
      · exact .inr ⟨h₆.1, h₆.2.1⟩
      · rename_i hc
        refine .inl ⟨(y, e₀), List.mem_cons_self, h₆.symm, ?_⟩
        by_cases hk : k = skip
        · exact absurd (h₆.trans (hs 0 (y, e₀) rfl (by omega))) hne
        · simpa [hk] using hc
    · have hs' : ∀ j ye, rest[j]? = some ye → j + (k + 1) = skip → ye.2 = e :=
        fun j ye hj hjs => hs (j + 1) ye (by simpa using hj) (by omega)
      rcases Evacuated.unmoved h₇ hs' yb hyb hne with ⟨ya, hya, h⟩ | h
      · exact .inl ⟨ya, List.mem_cons_of_mem _ hya, h⟩
      · exact .inr h

/-- A name that a frame binds is found by `findIdx?`. -/
theorem findIdx?_of_lookup {x : Name} :
    ∀ {env : List (Name × Entry)} {e : Entry}, env.lookup x = some e →
      ∃ i, env.findIdx? (·.1 == x) = some i
  | [], _, h => by simp at h
  | (y, f) :: env, e, h => by
    by_cases hy : y = x
    · subst hy
      exact ⟨0, by simp [List.findIdx?_cons]⟩
    · rw [lookup_cons_ne (Ne.symm hy)] at h
      obtain ⟨i, hi⟩ := findIdx?_of_lookup h
      have hb : (y == x) = false := by simpa using hy
      exact ⟨i + 1, by rw [List.findIdx?_cons, hb]; simp [hi]⟩

/-- `evacuate` keeps the binding at `skip`, so a name first bound there is found as it was. -/
theorem Evacuated.lookup_skip {region : Ref} {skip : Nat} {s s' : State} {x : Name} :
    ∀ {k : Nat} {env env' : List (Name × Entry)}, Evacuated region skip s s' k env env' →
      (env.findIdx? (·.1 == x)).map (· + k) = some skip → env'.lookup x = env.lookup x
  | _, [], [], _, hf => by simp at hf
  | k, (y, e₀) :: rest, (y', e') :: rest', ⟨hy, _, _, _, _, h₆, h₇⟩, hf => by
    subst hy
    by_cases hyx : y' = x
    · subst hyx
      simp only [List.findIdx?_cons, beq_self_eq_true, ↓reduceIte, Option.map_some,
        Nat.zero_add, Option.some.injEq] at hf
      subst hf
      simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at h₆
      simp [h₆]
    · have hb : (y' == x) = false := by simpa using hyx
      rw [List.findIdx?_cons, hb] at hf
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_map] at hf
      rw [lookup_cons_ne (Ne.symm hyx), lookup_cons_ne (Ne.symm hyx)]
      refine Evacuated.lookup_skip h₇ ?_
      rw [← hf]
      congr 1
      funext j
      simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 k]

/-- `unshare` of a binding that refers to its own home, when every binding agrees: every other
binding that referred into the home gets one of its own, each reads what it read, and no other
binding's part overlaps the home. -/
theorem unshare_agrees_home {fr : Copy.Frame} {s : State} (h : AgreesAll fr s)
    (hsh : AllShared s) {x : Name} {e : Entry} (hx : s.env.lookup x = some e)
    (ha : e.alias = none) :
    ∃ s₁, unshare s x = .ok s₁ ∧ AgreesAll fr s₁ ∧ AllShared s₁ ∧ Follows s s₁ ∧
      s₁.env.lookup x = some e ∧ ∀ ye ∈ s₁.env, ye.2 ≠ e → overlaps e.home ye.2.ref = false := by
  obtain ⟨i, hi⟩ := findIdx?_of_lookup hx
  obtain ⟨s', env', hev⟩ := evacuate_ok e.home i 0 s s.env h.reads
  refine ⟨{ s' with env := env' }, ?_, ?_⟩
  · simp only [unshare, hi, hx, ha, hev]
    rfl
  obtain ⟨hg, -, hE⟩ := evacuate_spec hev
  have hE₁ : Evacuated e.home i s { s' with env := env' } 0 s.env env' :=
    Evacuated.congr (s₁ := s') (s₂ := { s' with env := env' }) rfl hE
  have hap := evacuate_apart hev ⟨h.homes, fun ye hye => (h.has ye hye).1⟩
  have hxe : (x, e) ∈ s.env := List.mem_of_getElem? (lookup_of_findIdx? hi hx)
  have hs : ∀ j ye, s.env[j]? = some ye → j + 0 = i → ye.2 = e := fun j ye hj hji => by
    rw [Nat.add_zero] at hji
    subst hji
    rw [lookup_of_findIdx? hi hx, Option.some.injEq] at hj
    rw [← hj]
  have hrefs : ∀ yb ∈ env', yb.2.ref.loc < s'.store.size := fun yb hyb => by
    rcases hE₁.mem_settled yb hyb with ⟨ya, hya, he⟩ | ⟨-, -, -, ha', -, -⟩
    · rw [← he]
      exact State.Has.grows hg (h.has ya hya).2
    · have : yb.2.ref = yb.2.home := by simp [Entry.ref, ha']
      rw [this]
      exact hap.2 yb hyb
  refine ⟨AgreesAll.of_alike h (Evacuated.alike hE₁ fun ye hye => (h.has ye hye).2)
      (fun ye hye => ⟨hap.2 ye hye, hrefs ye hye⟩) hap.1,
    AllShared.evacuated hsh hE₁, ?_, ?_, ?_⟩
  · exact Follows.of_settled hg (fun yb hyb =>
      (hE₁.mem_settled yb hyb).imp id fun ⟨_, _, _, ha', hl, _⟩ => ⟨ha', hl⟩)
      (hE₁.kept hsh.inout)
  · rw [show ({ s' with env := env' } : State).env = env' from rfl,
      hE₁.lookup_skip (by simp [hi]), hx]
  · intro ye hye hne
    rcases hE₁.unmoved hs ye hye hne with ⟨ya, hya, he, hany⟩ | ⟨ha', hl⟩
    · rw [← he]
      cases hr : ya.2.alias with
      | some r =>
        rw [hr] at hany
        simpa [Entry.ref, hr] using hany
      | none =>
        have hne' : (x, e) ≠ ya := fun heq => hne (by rw [← he, ← heq])
        simpa [Entry.ref, hr] using homes_apart_of_mem h.homes hxe hya hne'
    · have hr : ye.2.ref = ye.2.home := by simp [Entry.ref, ha']
      rw [hr]
      exact (overlaps_comm _ _).trans
        (overlaps_fresh (Nat.lt_of_lt_of_le (h.has (x, e) hxe).1 hl))

/-- Replacing the binding that `findIdx?` finds, a name's first, changes what `lookup` finds. -/
theorem lookup_set_findIdx? {x : Name} {e' : Entry} :
    ∀ {env : List (Name × Entry)} {i : Nat}, env.findIdx? (·.1 == x) = some i →
      (env.set i (x, e')).lookup x = some e'
  | [], _, h => by simp at h
  | (y, f) :: env, i, h => by
    by_cases hy : y = x
    · subst hy
      simp only [List.findIdx?_cons, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp
    · have hb : (y == x) = false := by simpa using hy
      rw [List.findIdx?_cons, hb] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      rw [List.set_cons_succ, lookup_cons_ne (Ne.symm hy)]
      exact lookup_set_findIdx? hj

/-- Bindings read alike in a store that grows, each referring into the store before. -/
theorem ReadsAlike.grows {st st' : Array Value} (hg : Grows st st') :
    ∀ {env : List (Name × Entry)}, (∀ ye ∈ env, ye.2.ref.loc < st.size) →
      ReadsAlike st st' env env
  | [], _ => trivial
  | (_, _) :: _, h =>
    ⟨⟨rfl, deref_grows (s := ⟨[], st⟩) (s' := ⟨[], st'⟩) hg (h _ List.mem_cons_self) []⟩,
      ReadsAlike.grows hg fun ye hye => h ye (List.mem_cons_of_mem _ hye)⟩

/-- Replacing a binding with one of the same name that reads what it read keeps the frame
reading alike. -/
theorem ReadsAlike.set {st st' : Array Value} {x : Name} {e e' : Entry} :
    ∀ {env env' : List (Name × Entry)} {i : Nat}, ReadsAlike st st' env env' →
      env[i]? = some (x, e) →
      deref ⟨[], st'⟩ e'.ref [] = deref ⟨[], st⟩ e.ref [] →
      ReadsAlike st st' env (env'.set i (x, e'))
  | [], [], _, _, h, _ => by simp at h
  | (y, f) :: env, (y', f') :: env', 0, ⟨_, h₂⟩, hi, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact ⟨⟨rfl, hr⟩, h₂⟩
  | (_, _) :: env, (_, _) :: env', i + 1, ⟨h₁, h₂⟩, hi, hr =>
    ⟨h₁, ReadsAlike.set h₂ (by simpa using hi) hr⟩
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim

/-- Replacing a binding with one whose home overlaps no other's keeps the homes apart. -/
theorem pairwise_set_apart {b : Name × Entry} :
    ∀ {env : List (Name × Entry)} {i : Nat},
      env.Pairwise (fun a c => overlaps a.2.home c.2.home = false) →
      (∀ a ∈ env, overlaps b.2.home a.2.home = false) →
      (env.set i b).Pairwise (fun a c => overlaps a.2.home c.2.home = false)
  | [], _, _, _ => by simp
  | a :: env, 0, hp, hb => by
    rw [List.pairwise_cons] at hp
    rw [List.set_cons_zero, List.pairwise_cons]
    exact ⟨fun c hc => hb c (List.mem_cons_of_mem _ hc), hp.2⟩
  | a :: env, i + 1, hp, hb => by
    rw [List.pairwise_cons] at hp
    rw [List.set_cons_succ, List.pairwise_cons]
    refine ⟨fun c hc => ?_, pairwise_set_apart hp.2 fun c hc => hb c (List.mem_cons_of_mem _ hc)⟩
    rcases List.mem_or_eq_of_mem_set hc with hc | rfl
    · exact hp.1 c hc
    · exact (overlaps_comm _ _).trans (hb a List.mem_cons_self)

/-- `unshare` of a binding that refers to another's storage, when every binding agrees: it alone
gets a copy of what it reads, at a new home that no other binding's part overlaps. -/
theorem unshare_agrees_alias {fr : Copy.Frame} {s : State} (h : AgreesAll fr s)
    (hsh : AllShared s) {x : Name} {e : Entry} (hx : s.env.lookup x = some e) {r : Ref}
    (ha : e.alias = some r) :
    ∃ s₁ e₁, unshare s x = .ok s₁ ∧ AgreesAll fr s₁ ∧ AllShared s₁ ∧ Follows s s₁ ∧
      s₁.env.lookup x = some e₁ ∧ e₁.alias = none ∧
      ∀ ye ∈ s₁.env, ye.2 ≠ e₁ → overlaps e₁.home ye.2.ref = false := by
  obtain ⟨i, hi⟩ := findIdx?_of_lookup hx
  have hxi := lookup_of_findIdx? hi hx
  have hxe : (x, e) ∈ s.env := List.mem_of_getElem? hxi
  obtain ⟨v, hv⟩ := h.reads (x, e) hxe
  obtain ⟨s', e', hse⟩ := settle_ok hv
  have hS := settle_spec hse
  obtain ⟨hhome, hsize⟩ := hS.fresh (by simp [ha])
  have hr' : e'.ref = e'.home := by simp [Entry.ref, hS.alias]
  let s₁ : State := { s' with env := s.env.set i (x, e') }
  refine ⟨s₁, e', ?_, ?_⟩
  · simp only [unshare, hi, hx, ha, hse]
    change Except.ok ({ env := s'.env.set i (x, e'), store := s'.store } : State) = Except.ok s₁
    rw [hS.env]
  have hold : ∀ ye ∈ s.env, ye.2.ref.loc < s.store.size := fun ye hye => (h.has ye hye).2
  have hmem : ∀ yb ∈ s₁.env, yb ∈ s.env ∨ yb = (x, e') := fun yb hyb =>
    List.mem_or_eq_of_mem_set hyb
  have hfresh : ∀ ye ∈ s.env, overlaps e'.home ye.2.ref = false := fun ye hye => by
    rw [hhome]
    exact overlaps_fresh (hold ye hye)
  have hfresh' : ∀ ye ∈ s.env, overlaps e'.home ye.2.home = false := fun ye hye => by
    rw [hhome]
    exact overlaps_fresh (h.has ye hye).1
  have hreads : ReadsAlike s.store s₁.store s.env s₁.env :=
    (ReadsAlike.grows hS.grows hold).set hxi (by
      rw [show (⟨[], s'.store⟩ : State) = { s' with env := [] } from rfl]
      exact (deref_env _ _ _ _).trans ((hS.reads (h.has (x, e) hxe).2 []).trans
        (deref_env _ _ _ _).symm))
  have hhas : ∀ yb ∈ s₁.env, s₁.Has yb.2.home ∧ s₁.Has yb.2.ref := fun yb hyb => by
    rcases hmem yb hyb with hyb | rfl
    · exact ⟨State.Has.grows hS.grows (h.has yb hyb).1, State.Has.grows hS.grows (h.has yb hyb).2⟩
    · have : s₁.Has e'.home := by
        show e'.home.loc < s'.store.size
        rw [hhome, hsize]
        exact Nat.lt_succ_self _
      exact ⟨this, hr' ▸ this⟩
  refine ⟨AgreesAll.of_alike h hreads hhas (pairwise_set_apart h.homes fun a ha' => hfresh' a ha'),
    ⟨fun yb hyb => ?_, fun yb hyb => ?_, fun yb hyb => ?_⟩, ?_, lookup_set_findIdx? hi, hS.alias,
    ?_⟩
  · rcases hmem yb hyb with hyb | rfl
    · exact hsh.shared yb hyb
    · rw [show (x, e').2.unique = e.unique from hS.unique]
      exact hsh.shared (x, e) hxe
  · rcases hmem yb hyb with hyb | rfl
    · exact hsh.homes yb hyb
    · exact .inl (by rw [show (x, e').2.home = e'.home from rfl, hhome])
  · rcases hmem yb hyb with hyb | rfl
    · exact hsh.inout yb hyb
    · exact fun _ => hS.alias
  · refine Follows.of_settled hS.grows (fun yb hyb => ?_) (Kept.set rfl hxi rfl fun hin => ?_)
    · rcases hmem yb hyb with hyb | rfl
      · exact .inl ⟨yb, hyb, rfl⟩
      · exact .inr ⟨hS.alias, by rw [show (x, e').2.home = e'.home from rfl, hhome]; exact Nat.le_refl _⟩
    · have := hsh.inout (x, e) hxe hin
      simp [ha] at this
  · intro ye hye hne
    rcases hmem ye hye with hye | rfl
    · exact hfresh ye hye
    · exact absurd rfl hne

/-- When a frame of copies and a state of sharing agree on every binding, `unshare` succeeds,
every binding reads what it read, and the binding that stops sharing refers to its home, which
no other binding's part overlaps (modes.shared-writes). -/
theorem unshare_agrees {fr : Copy.Frame} {s : State} (h : AgreesAll fr s) (hsh : AllShared s)
    {x : Name} {e : Entry} (hx : s.env.lookup x = some e) :
    ∃ s₁ e₁, unshare s x = .ok s₁ ∧ AgreesAll fr s₁ ∧ AllShared s₁ ∧ Follows s s₁ ∧
      s₁.env.lookup x = some e₁ ∧ e₁.alias = none ∧
      ∀ ye ∈ s₁.env, ye.2 ≠ e₁ → overlaps e₁.home ye.2.ref = false := by
  cases ha : e.alias with
  | none =>
    obtain ⟨s₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := unshare_agrees_home h hsh hx ha
    exact ⟨s₁, e, h₁, h₂, h₃, h₄, h₅, ha, h₆⟩
  | some r => exact unshare_agrees_alias h hsh hx ha

end Stilt.Sharing
