import TPTND
import Lean.Data.Json
import Mathlib.Data.Finset.Sort

/-! # JSON certificate codec

Decodes/encodes `Derivation` trees to a small JSON schema so certificates
can be produced, shipped, and re-checked outside Lean.

Schema (all probabilities are exact rationals written as strings "num/den"):

  Output      {"type":"atom","name":s} | {"type":"neg","arg":O}
              | {"type":"sum"|"prod"|"arr","left":O,"right":O}
  Term        {"type":"atom","name":s} | {"type":"pair","left":T,"right":T}
              | {"type":"fst"|"snd","arg":T}
              | {"type":"lam","var":s,"body":T} | {"type":"app","fn":T,"arg":T}
  Constraint  {"type":"exact","p":R} | {"type":"interval","lo":R,"hi":R}
              | {"type":"outside","lo":R,"hi":R} | {"type":"unknown"}
  Entry       {"name":s,"support":[s],"output":O,"constraint":C}
  TermClaim   {"mode":"frequency"|"expected","term":T,"samples":n,
               "output":O,"value":R,"prov":[s]}
  TrustClaim  {"type":"trust"|"untrust","kind":"oneSample"|"twoSample",
               "term":T,"samples":n,"output":O,"observed":R,"model":R,
               "interval":C}
  Comparison  {"type":"excess"|"noExcess","left":TC,"right":TC,
               "diff":R,"interval":C}
  Claim       {"type":"outputDecl","output":O} | {"type":"distDecl","context":[E]}
              | {"type":"identity","entry":E} | {"type":"term","claim":TC}
              | {"type":"trust","claim":TrC} | {"type":"comparison","claim":CC}
              | {"type":"priorFamily","x":S,"alpha":O,"y":S,"beta":O,
              |    "pairs":[{"a":R,"b":R}]}
  Derivation  {"rule":s,"premises":[D],"context":[E],"claim":Claim,
               "independenceWitness":bool?}
-/

namespace TPTND

open Lean (Json toJson)

abbrev Dec (α : Type) := Except String α

-- ============================================================================
-- Decoding
-- ============================================================================

private def jField (j : Json) (k : String) : Dec Json := j.getObjVal? k

def parseRat (s : String) : Dec ℚ :=
  match s.splitOn "/" with
  | [a] =>
    match a.trim.toInt? with
    | some n => .ok (n : ℚ)
    | none   => .error s!"bad rational '{s}'"
  | [a, b] =>
    match a.trim.toInt?, b.trim.toNat? with
    | some n, some d =>
      if d == 0 then .error s!"zero denominator in '{s}'" else .ok (mkRat n d)
    | _, _ => .error s!"bad rational '{s}'"
  | _ => .error s!"bad rational '{s}'"

def parseProb (j : Json) : Dec Prob := do
  let s ← j.getStr?
  let q ← parseRat s
  if h1 : 0 ≤ q then
    if h2 : q ≤ 1 then
      pure ⟨q, h1, h2⟩
    else .error s!"probability {s} exceeds 1"
  else .error s!"probability {s} is negative"

def parseStrSet (j : Json) : Dec (Finset String) := do
  let arr ← j.getArr?
  let mut s : Finset String := ∅
  for x in arr do
    s := insert (← x.getStr?) s
  pure s

partial def parseOutput (j : Json) : Dec Output := do
  match (← (← jField j "type").getStr?) with
  | "atom" => pure (.atom (← (← jField j "name").getStr?))
  | "neg"  => pure (.neg (← parseOutput (← jField j "arg")))
  | "sum"  => pure (.sum (← parseOutput (← jField j "left"))
                         (← parseOutput (← jField j "right")))
  | "prod" => pure (.prod (← parseOutput (← jField j "left"))
                          (← parseOutput (← jField j "right")))
  | "arr"  => pure (.arr (← parseOutput (← jField j "left"))
                         (← parseProb (← jField j "ann"))
                         (← parseOutput (← jField j "right")))
  | t => .error s!"unknown output type '{t}'"

partial def parseTerm (j : Json) : Dec Term := do
  match (← (← jField j "type").getStr?) with
  | "atom" => pure (.atom (← (← jField j "name").getStr?))
  | "pair" => pure (.pair (← parseTerm (← jField j "left"))
                          (← parseTerm (← jField j "right")))
  | "fst"  => pure (.fst (← parseTerm (← jField j "arg")))
  | "snd"  => pure (.snd (← parseTerm (← jField j "arg")))
  | "lam"  => pure (.lam (← (← jField j "var").getStr?)
                         (← parseTerm (← jField j "body")))
  | "app"  => pure (.app (← parseTerm (← jField j "fn"))
                         (← parseTerm (← jField j "arg")))
  | t => .error s!"unknown term type '{t}'"

def parseConstraint (j : Json) : Dec Constraint := do
  match (← (← jField j "type").getStr?) with
  | "exact"    => pure (.exact (← parseProb (← jField j "p")))
  | "interval" => pure (.interval (← parseProb (← jField j "lo"))
                                  (← parseProb (← jField j "hi")))
  | "outside"  => pure (.outsideInterval (← parseProb (← jField j "lo"))
                                         (← parseProb (← jField j "hi")))
  | "unknown"  => pure .unknown
  | t => .error s!"unknown constraint type '{t}'"

def parseEntry (j : Json) : Dec ContextEntry := do
  pure { name       := ← (← jField j "name").getStr?
         support    := ← parseStrSet (← jField j "support")
         output     := ← parseOutput (← jField j "output")
         constraint := ← parseConstraint (← jField j "constraint") }

def parseMode (j : Json) : Dec TermMode := do
  match (← j.getStr?) with
  | "frequency" => pure .frequency
  | "expected"  => pure .expected
  | m => .error s!"unknown mode '{m}'"

def parseTermClaim (j : Json) : Dec TermClaim := do
  pure { mode    := ← parseMode (← jField j "mode")
         term    := ← parseTerm (← jField j "term")
         samples := ← (← jField j "samples").getNat?
         output  := ← parseOutput (← jField j "output")
         value   := ← parseProb (← jField j "value")
         prov    := ← parseStrSet (← jField j "prov") }

def parseCIKind (j : Json) : Dec CIKind := do
  match (← j.getStr?) with
  | "oneSample" => pure .oneSample
  | "twoSample" => pure .twoSample
  | k => .error s!"unknown CI kind '{k}'"

def parseTrustClaim (j : Json) : Dec TrustClaim := do
  let kind ← parseCIKind (← jField j "kind")
  let t ← parseTerm (← jField j "term")
  let n ← (← jField j "samples").getNat?
  let α ← parseOutput (← jField j "output")
  let f ← parseProb (← jField j "observed")
  let p ← parseProb (← jField j "model")
  let c ← parseConstraint (← jField j "interval")
  let σ ← parseStrSet (← jField j "prov")
  match (← (← jField j "type").getStr?) with
  | "trust"   => pure (.trust kind t n α f p c σ)
  | "untrust" => pure (.untrust kind t n α f p c σ)
  | t' => .error s!"unknown trust type '{t'}'"

def parseComparisonClaim (j : Json) : Dec ComparisonClaim := do
  let l ← parseTermClaim (← jField j "left")
  let r ← parseTermClaim (← jField j "right")
  let diff ← parseProb (← jField j "diff")
  let c ← parseConstraint (← jField j "interval")
  match (← (← jField j "type").getStr?) with
  | "excess"   => pure (.excess l r diff c)
  | "noExcess" => pure (.noExcess l r diff c)
  | t => .error s!"unknown comparison type '{t}'"

def parseClaim (j : Json) : Dec Claim := do
  match (← (← jField j "type").getStr?) with
  | "outputDecl" => pure (.outputDecl (← parseOutput (← jField j "output")))
  | "distDecl" => do
      let arr ← (← jField j "context").getArr?
      pure (.distDecl (← arr.toList.mapM parseEntry))
  | "identity" => pure (.identity (← parseEntry (← jField j "entry")))
  | "term" => pure (.term (← parseTermClaim (← jField j "claim")))
  | "trust" => pure (.trust (← parseTrustClaim (← jField j "claim")))
  | "comparison" =>
      pure (.comparison (← parseComparisonClaim (← jField j "claim")))
  | "priorFamily" => do
      let arr ← (← jField j "pairs").getArr?
      let pairs ← arr.toList.mapM (fun pj => do
        pure ((← parseProb (← jField pj "a")), (← parseProb (← jField pj "b"))))
      pure (.priorFamily
        { xName  := ← (← jField j "x").getStr?
        , alpha  := ← parseOutput (← jField j "alpha")
        , yName  := ← (← jField j "y").getStr?
        , beta   := ← parseOutput (← jField j "beta")
        , points := pairs })
  | t => .error s!"unknown claim type '{t}'"

partial def parseDerivation (j : Json) : Dec Derivation := do
  let rule ← (← jField j "rule").getStr?
  let premArr ← (← jField j "premises").getArr?
  let ps ← premArr.toList.mapM parseDerivation
  let ctxArr ← (← jField j "context").getArr?
  let ctx ← ctxArr.toList.mapM parseEntry
  let claim ← parseClaim (← jField j "claim")
  let w := match jField j "independenceWitness" with
    | .ok b  => (b.getBool?).toOption.getD false
    | .error _ => false
  pure (.node rule ps ⟨ctx, claim⟩ w)

-- ============================================================================
-- Encoding
-- ============================================================================

private def ratStr (q : ℚ) : Json := Json.str s!"{q.num}/{q.den}"

def probJson (p : Prob) : Json := ratStr p.val

def strSetJson (s : Finset String) : Json :=
  Json.arr ((s.sort (· ≤ ·)).map Json.str).toArray

partial def outputJson : Output → Json
  | .atom s   => Json.mkObj [("type", "atom"), ("name", s)]
  | .neg α    => Json.mkObj [("type", "neg"), ("arg", outputJson α)]
  | .sum α β  => Json.mkObj [("type", "sum"), ("left", outputJson α), ("right", outputJson β)]
  | .prod α β => Json.mkObj [("type", "prod"), ("left", outputJson α), ("right", outputJson β)]
  | .arr α a β => Json.mkObj [("type", "arr"), ("left", outputJson α),
                              ("ann", probJson a), ("right", outputJson β)]

partial def termJson : Term → Json
  | .atom s   => Json.mkObj [("type", "atom"), ("name", s)]
  | .pair a b => Json.mkObj [("type", "pair"), ("left", termJson a), ("right", termJson b)]
  | .fst t    => Json.mkObj [("type", "fst"), ("arg", termJson t)]
  | .snd t    => Json.mkObj [("type", "snd"), ("arg", termJson t)]
  | .lam x b  => Json.mkObj [("type", "lam"), ("var", x), ("body", termJson b)]
  | .app f a  => Json.mkObj [("type", "app"), ("fn", termJson f), ("arg", termJson a)]

def constraintJson : Constraint → Json
  | .exact p              => Json.mkObj [("type", "exact"), ("p", probJson p)]
  | .interval lo hi       => Json.mkObj [("type", "interval"), ("lo", probJson lo), ("hi", probJson hi)]
  | .outsideInterval lo hi => Json.mkObj [("type", "outside"), ("lo", probJson lo), ("hi", probJson hi)]
  | .unknown              => Json.mkObj [("type", "unknown")]

def entryJson (e : ContextEntry) : Json :=
  Json.mkObj [("name", e.name), ("support", strSetJson e.support),
              ("output", outputJson e.output),
              ("constraint", constraintJson e.constraint)]

def termClaimJson (tc : TermClaim) : Json :=
  Json.mkObj [("mode", if tc.mode == .expected then "expected" else "frequency"),
              ("term", termJson tc.term), ("samples", toJson tc.samples),
              ("output", outputJson tc.output), ("value", probJson tc.value),
              ("prov", strSetJson tc.prov)]

def trustClaimJson : TrustClaim → Json
  | .trust k t n α f p c σ =>
      Json.mkObj [("type", "trust"),
                  ("kind", if k == .twoSample then "twoSample" else "oneSample"),
                  ("term", termJson t), ("samples", toJson n),
                  ("output", outputJson α), ("observed", probJson f),
                  ("model", probJson p), ("interval", constraintJson c),
                  ("prov", strSetJson σ)]
  | .untrust k t n α f p c σ =>
      Json.mkObj [("type", "untrust"),
                  ("kind", if k == .twoSample then "twoSample" else "oneSample"),
                  ("term", termJson t), ("samples", toJson n),
                  ("output", outputJson α), ("observed", probJson f),
                  ("model", probJson p), ("interval", constraintJson c),
                  ("prov", strSetJson σ)]

def comparisonJson : ComparisonClaim → Json
  | .excess l r d c =>
      Json.mkObj [("type", "excess"), ("left", termClaimJson l),
                  ("right", termClaimJson r), ("diff", probJson d),
                  ("interval", constraintJson c)]
  | .noExcess l r d c =>
      Json.mkObj [("type", "noExcess"), ("left", termClaimJson l),
                  ("right", termClaimJson r), ("diff", probJson d),
                  ("interval", constraintJson c)]

def claimJson : Claim → Json
  | .outputDecl o => Json.mkObj [("type", "outputDecl"), ("output", outputJson o)]
  | .distDecl Γ   => Json.mkObj [("type", "distDecl"),
                                 ("context", Json.arr (Γ.map entryJson).toArray)]
  | .identity e   => Json.mkObj [("type", "identity"), ("entry", entryJson e)]
  | .term tc      => Json.mkObj [("type", "term"), ("claim", termClaimJson tc)]
  | .trust tc     => Json.mkObj [("type", "trust"), ("claim", trustClaimJson tc)]
  | .comparison c => Json.mkObj [("type", "comparison"), ("claim", comparisonJson c)]
  | .priorFamily fam =>
      Json.mkObj [("type", "priorFamily"),
                  ("x", Json.str fam.xName), ("alpha", outputJson fam.alpha),
                  ("y", Json.str fam.yName), ("beta", outputJson fam.beta),
                  ("pairs", Json.arr (fam.points.map (fun p =>
                    Json.mkObj [("a", probJson p.1), ("b", probJson p.2)])).toArray)]

partial def derivationJson : Derivation → Json
  | .node rule ps concl w =>
      Json.mkObj [("rule", rule),
                  ("premises", Json.arr (ps.map derivationJson).toArray),
                  ("context", Json.arr (concl.context.map entryJson).toArray),
                  ("claim", claimJson concl.claim),
                  ("independenceWitness", toJson w)]

end TPTND
