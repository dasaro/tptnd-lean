import TPTND.JsonCodec

/-! # leaf_check

Reads a JSON certificate from stdin, decodes it, runs `checkDerivation`,
and prints a one-line JSON verdict:

  {"ok": true}                          -- accepted
  {"ok": false, "error": "<reason>"}    -- rejected / malformed
-/

open TPTND Lean

private def verdict (ok : Bool) (err : String := "") : String :=
  (Json.mkObj (("ok", Json.bool ok) ::
    (if err.isEmpty then [] else [("error", Json.str err)]))).compress

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input with
  | .error e => IO.println (verdict false s!"JSON parse error: {e}")
  | .ok j =>
    match parseDerivation j with
    | .error e => IO.println (verdict false s!"certificate decode error: {e}")
    | .ok d =>
      match checkDerivation d with
      | .ok ()   => IO.println (verdict true)
      | .error e => IO.println (verdict false e)
