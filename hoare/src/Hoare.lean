namespace Hoare


def Pre (σ : Type ) : Type := σ → Prop

def pre (p : σ → Prop) : Pre σ := p

def Post (σ α : Type) : Type := σ → α → σ → Prop

def post (q : σ → α → σ → Prop) : Post σ α := q

structure HoareM {σ : Type} (p : Pre σ) (α : Type) (q : Post σ α) where
  run : σ → α × σ
  valid : ∀ s : σ, match run s with | ⟨x, s'⟩ => p s → q s x s'

-- TODO: Add an equivalence operation for comparing Hoare monads.

namespace HoareM

def eval {p : Pre σ} {q : Post σ α} (h : HoareM p α q) (s : σ) : α :=
  match h.run s with
  | ⟨x, _⟩ => x

def exec {p : Pre σ} {q : Post σ α} (h : HoareM p α q) (s : σ) : σ :=
  match h.run s with
  | ⟨_, s'⟩ => s'

def Always : Pre σ :=
  fun _ => True

def Exactly (x : α) : Post σ α :=
  fun s x' s' => s = s' ∧ x = x'

def pure (x : α) : HoareM (Always : Pre σ) α (Exactly x : Post σ α) :=
  {
    run := fun s => ⟨x, s⟩
  , valid := fun s => by simp [Always, Exactly]
  }

def bind {p' : α → σ → Prop} {q' : α → σ → β → σ → Prop}
  (h : HoareM p α q) (f : ∀ x : α, HoareM (p' x) β (q' x)) :
  HoareM
    (fun s => p s ∧ ∀x, ∀s', q s x s' → p' x s')
    β
    (fun s y s'' => ∃x, ∃s', q s x s' ∧ q' x s' y s'')
    :=
    {
      run := fun s =>
        match h.run s with
        | ⟨x, s'⟩ => (f x).run s'
    , valid := by
        intro s
        intro precond
        let x := (h.run s).fst
        exists x
        let s' := (h.run s).snd
        exists s'
        let qsxs' := h.valid s precond.left
        apply And.intro
        case left =>
          exact qsxs'
        case right =>
          let p'xs' := (precond.right x s') qsxs'
          exact (f x).valid s' p'xs'
    }

def fmap (f : α → β) (h : HoareM p α q) : HoareM p β (fun s y s' => ∃x, f x = y ∧ q s x s') :=
  {
    run := fun s =>
             match h.run s with
             | ⟨x, s'⟩ => ⟨f x, s'⟩
  , valid := by
      intro s
      intro ps
      let x := (h.run s).fst
      exists x
      apply And.intro
      case left =>
        rfl
      case right =>
        exact h.valid s ps
  }

def GotState : Post σ σ :=
  fun s x' s' => s = s' ∧ s = x'

def get : HoareM (Always : Pre σ) σ (GotState : Post σ σ) :=
  {
    run := fun s => ⟨s, s⟩
  , valid := by simp [Always, GotState]
  }

def PutState (s : σ) : Post σ α :=
  fun _ _ s' => s' = s

def put (s : σ) : HoareM (Always : Pre σ) Unit (PutState s : Post σ Unit) :=
  {
    run := fun _ => ⟨(), s⟩
  , valid := by simp [Always, PutState]
  }

def Transformed (f : σ → α × σ) : Post σ α :=
  fun s x s' => ⟨x, s'⟩ = f s

def state (f : σ → α × σ) : HoareM (Always : Pre σ) α (Transformed f) :=
  {
    run := f
  , valid := by simp [Always, Transformed]
  }

def Gotten (f : σ → α) : Post σ α :=
  fun s x s' => s = s' ∧ f s = x

def gets (f : σ → α) : HoareM (Always : Pre σ) α (Gotten f) :=
  {
    run := fun s => ⟨f s, s⟩
  , valid := by simp [Always, Gotten]
  }

def Modified (f : σ → σ) : Post σ α :=
  fun s _ s' => s' = f s

def modify (f : σ → σ) : HoareM (Always : Pre σ) Unit (Modified f : Post σ Unit) :=
  {
    run := fun s => ⟨(), f s⟩
  , valid := by simp [Always, Modified]
  }

def Applied (f : σ → α → β) : Post σ β :=
  fun s y s' => s = s' ∧ ∃x, f s x = y

def apply (f : σ → α → β) (x : α) : HoareM (Always : Pre σ) β (Applied f : Post σ β) :=
  {
    run := fun s => ⟨f s x, s⟩
  , valid := by simp [Always, Applied]
  }

end HoareM


end Hoare
