namespace K28.Finite

inductive CaseTree where
  | leaf
  | split (conflict : Nat) (left right : CaseTree)
deriving Inhabited

def extraCases : Nat → CaseTree
  | 261 => (.split 30 .leaf .leaf)
  | 341 => (.split 61 .leaf .leaf)
  | 546 => (.split 31 .leaf .leaf)
  | 674 => (.split 7 (.split 14 (.split 20 (.split 22 .leaf (.split 25 (.split 31 (.split 94 .leaf .leaf) .leaf) .leaf)) .leaf) .leaf) .leaf)
  | 682 => (.split 22 .leaf (.split 24 (.split 31 .leaf (.split 62 .leaf .leaf)) .leaf))
  | 683 => (.split 62 .leaf .leaf)
  | 698 => (.split 31 .leaf .leaf)
  | 762 => (.split 31 .leaf .leaf)
  | 763 => (.split 31 .leaf .leaf)
  | 802 => (.split 31 .leaf .leaf)
  | 1285 => (.split 30 .leaf .leaf)
  | 1301 => (.split 95 .leaf .leaf)
  | 1365 => (.split 21 .leaf (.split 30 .leaf (.split 32 (.split 61 .leaf (.split 86 .leaf (.split 88 (.split 95 .leaf .leaf) .leaf))) .leaf)))
  | 1493 => (.split 21 .leaf (.split 30 .leaf (.split 32 (.split 95 .leaf .leaf) .leaf)))
  | 1497 => (.split 95 .leaf .leaf)
  | 1501 => (.split 95 .leaf .leaf)
  | _ => .leaf

end K28.Finite
