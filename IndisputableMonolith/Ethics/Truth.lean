import Mathlib

namespace IndisputableMonolith
namespace Ethics

namespace Truth
  abbrev Claim := String

  /-! Evidence ledger over claims with support/conflict relations. -/
  structure EvidenceLedger where
    universeClaims : List Claim
    supports : Claim → Claim → Bool
    conflicts : Claim → Claim → Bool

  /-- Iterate a function `f` n times. -/
  def iterate {α} (f : α → α) : Nat → α → α
  | 0, x => x
  | Nat.succ n, x => iterate f n (f x)

  /-- One closure step: add all ledger claims supported by any current claim. -/
  def step (E : EvidenceLedger) (current : List Claim) : List Claim :=
    let add := E.universeClaims.filter (fun b => current.any (fun a => E.supports a b))
    (current ++ add).eraseDups

  /-- Supports-closure of a claim set within the ledger universe. -/
  def closure (E : EvidenceLedger) (S : List Claim) : List Claim :=
    iterate (step E) (E.universeClaims.length.succ) S

  /-- Check for any conflict within the closure of a claim set. -/
  def hasConflict (E : EvidenceLedger) (S : List Claim) : Bool :=
    let C := closure E S
    let rec pairs : List Claim → Bool
    | [] => False
    | x :: xs => xs.any (fun y => E.conflicts x y || E.conflicts y x) || pairs xs
    pairs C

  /-- Symmetric conflict count between request-closure and evidence-closure. -/
  def divergenceCount (E : EvidenceLedger) (S : List Claim) : Nat :=
    let Creq := closure E S
    let Cev := closure E E.universeClaims
    Creq.foldl (fun acc x =>
      Cev.foldl (fun acc2 y => acc2 + (if E.conflicts x y || E.conflicts y x then 1 else 0)) acc) 0

end Truth

end Ethics
end IndisputableMonolith

