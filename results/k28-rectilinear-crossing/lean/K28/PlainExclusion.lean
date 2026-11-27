import K28.Exclusion
import SweepCore.Plain

namespace K28.Finite
set_option Elab.async false
set_option maxHeartbeats 0

private theorem plain10 : (plainCoverage 10).ok = true := by native_decide
private theorem plain9 : (plainCoverage 9).ok = true := by native_decide
private theorem start10 : decode 10 (initial 10) = plainStart 10 := by decide +kernel
private theorem start9 : decode 9 (initial 9) = plainStart 9 := by decide +kernel

theorem plain_paths_below_fifty (p : Traces)
    (ha : PlainPath 10 (plainStart 10) (p 0)) (hb : PlainPath 9 (plainStart 9) (p 1))
    (hc : PlainPath 9 (plainStart 9) (p 2)) (compatible : Compatible p) :
    score (p 0) + score (p 1) + score (p 2) < 50 :=
  projected_paths_below_fifty p
    (encode_path ha _ start10 ((plainCoverage 10).sound plain10))
    (encode_path hb _ start9 ((plainCoverage 9).sound plain9))
    (encode_path hc _ start9 ((plainCoverage 9).sound plain9)) compatible

#print axioms plain_paths_below_fifty
end K28.Finite
